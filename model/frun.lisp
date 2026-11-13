; frun: a whole program's meaning, from the text: the modules elaborated in
; order, then the main program (fmean.lisp's evaluation); fortran-run.

(in-package "ACL2")

(include-book "fmean")

(set-verify-guards-eagerness 0)

; ---- a program: the modules elaborated in order, then the main program

(defun ext-frame (units)             ; the external procedures (R503)
  (declare (xargs :guard t))
  (if (atom units) nil
    (if (eq (kar (car units)) :proc)
        (cons (cons (tok-name (hd-name (unit-hd (car units)))) (list :proc (car units) :ext)) (ext-frame (cdr units)))
      (ext-frame (cdr units)))))

(defun me-modules (units mods modenvs gframe st fuel)   ; (mv err mods modenvs st)
  (declare (xargs :guard t :measure (len units) :verify-guards nil))
  (cond ((atom units) (mv nil mods modenvs st))
        ((not (eq (kar (car units)) :module)) (me-modules (cdr units) mods modenvs gframe st fuel))
        (t (let* ((u (car units)) (m (tok-name (hd-name (unit-hd u)))) (spec (unit-spec u))
                  (ufr (use-frames (kar spec) mods)) (env0 (append ufr (list gframe)))
                  (pfr (proc-frame (kadr (unit-int u)) (list :mod m))))
             (mv-let (e fr copies st) (me-decls (kaddr spec) env0 st (list (list mods modenvs gframe) nil) fuel pfr nil m nil)
               (declare (ignore copies))
               (if e (mv e nil nil st)
                 (me-modules (cdr units) (cons (cons m fr) mods) (cons (cons m (cons fr env0)) modenvs) gframe st fuel)))))))
(in-theory (disable me-modules))

; R840 DATA (8.6.7): a main program's DATA statements give its variables
; their initial values before its first statement. Each set's values, a
; repeat r * c as r copies of c, go in order to its objects: a scalar, an
; array element, or a whole array's elements in array element order
; (9.5.3.2), each as by intrinsic assignment. Not yet in the model: a
; data-implied-do, a substring or structure component object (:data).
(defun prim-expr (sign p)            ; the :expr tree of [sign] p (lone-prim's inverse)
  (declare (xargs :guard t))
  (list (list (list (list nil (list (list (list sign (list (list p nil) nil) nil) nil) nil)) nil) nil) nil))
(defun unit-datas (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (append (if (eq (kar (car ds)) :data) (true-list-fix (kadr (car ds))) nil) (unit-datas (cdr ds)))))
(defun no-datas (ds) (declare (xargs :guard t)) (if (atom ds) nil (if (eq (kar (car ds)) :data) (no-datas (cdr ds)) (cons (car ds) (no-datas (cdr ds))))))
(defun take-n (n xs) (declare (xargs :guard t)) (if (or (zp n) (atom xs)) nil (cons (car xs) (take-n (1- n) (cdr xs)))))
(defun drop-n (n xs) (declare (xargs :guard t)) (if (or (zp n) (atom xs)) xs (drop-n (1- n) (cdr xs))))
(defun data-vals (vs env st cx fuel)   ; (mv err exprs st): the values, repeats expanded
  (declare (xargs :guard t :measure (len vs) :verify-guards nil))
  (if (atom vs) (mv nil nil st)
    (let ((v (car vs)))
      (mv-let (n st) (if (kar v) (me-ev :expr (prim-expr nil (kar v)) env st cx fuel) (mv (vi 4 1) st))
        (cond ((errp n) (mv n nil st))
              ((not (and (ival-scalar n) (<= 0 (v-num n)))) (mv (err :data) nil st))   ; C882: a nonnegative repeat
              (t (mv-let (e es st) (data-vals (cdr vs) env st cx fuel)
                   (mv e (append (repeat-v (v-num n) (prim-expr (kadr v) (kaddr v))) es) st))))))))
(defun data-each (es ty k env st cx fuel)   ; (mv err raws st): each value converted to the type
  (declare (xargs :guard t :measure (len es) :verify-guards nil))
  (if (atom es) (mv nil nil st)
    (mv-let (v st) (me-ev :expr (car es) env st cx fuel)
      (let ((c (if (errp v) v (conv1 ty k v))))
        (if (errp c) (mv c nil st)
          (mv-let (e rs st) (data-each (cdr es) ty k env st cx fuel) (mv e (cons (raw c) rs) st)))))))
(defun data-objs (os es env st cx fuel)   ; (mv err es st): the values left
  (declare (xargs :guard t :measure (len os) :verify-guards nil   ; the measure only, the body kept closed
                  :hints (("Goal" :in-theory (union-theories (quote ((:definition len) (:definition o-p) (:definition o<) (:definition o-finp) (:type-prescription len) (:definition not) (:definition natp) (:type-prescription len))) (theory (quote minimal-theory)))))))
  (if (atom os) (mv nil es st)
    (let ((o (car os)))
      (mv-let (b suf d) (env-lookup (tok-name (kadr o)) env)
        (declare (ignore suf d))
        (cond
         ((atom es) (mv (err :data) nil st))                ; fewer values than objects (8.6.7p4)
         ((and (eq (kar o) :name) (eq (kar b) :var))
          (let* ((loc (kadr b)) (old (st-get loc st)))
            (if (aval-p old)
                (let ((n (len (a-es old))))
                  (if (< (len es) n) (mv (err :data) nil st)
                    (mv-let (e rs st) (data-each (take-n n es) (a-ty old) (a-k old) env st cx fuel)
                      (if e (mv e nil st)
                        (data-objs (cdr os) (drop-n n es) env (st-put loc (mk-arr (a-ty old) (a-k old) (a-lbs old) (a-ubs old) rs) st) cx fuel)))))
              (mv-let (v st) (me-ev :expr (car es) env st cx fuel)
                (let ((c (assign-val old v)))
                  (if (errp c) (mv c nil st) (data-objs (cdr os) (cdr es) env (st-put loc c st) cx fuel)))))))
         ((eq (kar o) :ref)                                  ; an element: as its assignment statement
          (mv-let (s st) (me-blk (list (list :act (list :assign (kadr o) t (kaddr o) (car es)))) env st cx fuel)
            (if (eq s :normal) (data-objs (cdr os) (cdr es) env st cx fuel) (mv (if (errp s) s (err :data)) nil st))))
         (t (mv (err :data) nil st)))))))
(defun me-data (sets env st cx fuel)  ; (mv err st)
  (declare (xargs :guard t :measure (len sets) :verify-guards nil
                  :hints (("Goal" :in-theory (union-theories (quote ((:definition len) (:definition o-p) (:definition o<) (:definition o-finp) (:type-prescription len) (:definition not) (:definition natp) (:type-prescription len))) (theory (quote minimal-theory)))))))
  (if (atom sets) (mv nil st)
    (mv-let (e es st) (data-vals (kadr (car sets)) env st cx fuel)
      (if e (mv e st)
        (mv-let (e es st) (data-objs (kar (car sets)) es env st cx fuel)
          (cond (e (mv e st)) (es (mv (err :data) st))       ; more values than objects
                (t (me-data (cdr sets) env st cx fuel))))))))

(defun find-main (units)
  (declare (xargs :guard t))
  (if (atom units) nil (if (eq (kar (car units)) :main) (car units) (find-main (cdr units)))))

(defun me-program (units in fuel)    ; (mv status lines): in the input's records
  (declare (xargs :guard t :verify-guards nil))
  (let ((gframe (ext-frame units)) (st (mk-st7 nil 0 nil nil nil nil (cons in nil))) (main (find-main units)))
    (mv-let (e mods modenvs st) (me-modules units nil nil gframe st fuel)
      (cond (e (mv e (close-lines (reverse (true-list-fix (st-out st))))))
            ((not main) (mv (err :syntax) nil))
            (t (let* ((g (list mods modenvs gframe)) (cx (list g nil (unit-formats main))) (spec (unit-spec main))
                      (ufr (use-frames (kar spec) mods)) (env0 (append ufr (list gframe)))
                      (pfr (proc-frame (kadr (unit-int main)) :host)))
                 (mv-let (e fr copies st) (me-decls (no-datas (kaddr spec)) env0 st cx fuel pfr nil (unit-key main) nil)
                   (declare (ignore copies))
                   (if e (mv e (close-lines (reverse (true-list-fix (st-out st)))))
                     (mv-let (fr st) (if (kadr spec) (mv fr st)          ; IMPLICIT NONE, or implicit typing (8.7)
                                       (implicit-vars (used-names (unit-exec main)) fr env0 st (unit-rules main)))
                       (mv-let (s st) (mv-let (e st) (me-data (unit-datas (kaddr spec)) (cons fr env0) st cx fuel)
                                        (if e (mv e st) (me-blk (unit-exec main) (cons fr env0) st cx fuel)))
                         (mv (cond ((equal s (err :stop)) :stop) ((eq s :normal) :normal)
                                   ((errp s) s) ((goto-p s) (err :label)) (t (err :syntax)))
                             (close-lines (reverse (true-list-fix (st-out st)))))))))))))))
(in-theory (disable me-program))

; ---- the text to its answer

(defun parse-stmts (ss)              ; each statement parsed whole, or nil
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ss) (mv t nil)
    (mv-let (ok s r) (fps :stmt (car ss))
      (if (not (and ok (null r))) (mv nil (car ss))
        (mv-let (ok2 rest) (parse-stmts (cdr ss)) (if ok2 (mv t (cons s rest)) (mv nil rest)))))))

(defun fortran-parse (text fixed)    ; (mv ok units-or-the-bad-statement); fixed: fixed source form
  (declare (xargs :guard (stringp text) :verify-guards nil))
  (mv-let (ok ss) (parse-stmts (if fixed (flex-fixed text) (flex text)))
    (if (not ok) (mv nil ss)
      (mv-let (ok2 us r) (fpu :program (ldo-sugar ss nil nil))
        (if (and ok2 (null r)) (mv t us) (mv nil (kar r)))))))

(defun fortran-run-in (text fixed in fuel)  ; (list status lines), or (list (:error :parse) stmt); in the input's records (strings)
  (declare (xargs :guard (stringp text) :verify-guards nil))
  (mv-let (ok us) (fortran-parse text fixed)
    (if (not ok) (list (err :parse) us)
      (mv-let (s lines) (me-program us in fuel) (list s lines)))))
(defun fortran-run-form (text fixed fuel) (declare (xargs :guard (stringp text) :verify-guards nil)) (fortran-run-in text fixed nil fuel))
(defun fortran-run (text fuel) (declare (xargs :guard (stringp text) :verify-guards nil)) (fortran-run-form text nil fuel))

; what fortran-parse accepts is a program of the grammar: each statement
; one fps read whole (fps-sound), the units fpu read from them (fpu-sound)
(defthm parse-stmts-sound
  (implies (mv-nth 0 (parse-stmts ss)) (stmts-p (mv-nth 1 (parse-stmts ss))))
  :hints (("Goal" :induct (parse-stmts ss))
          ("Subgoal *1/2" :use ((:instance fps-sound (nt :stmt) (toks (car ss)))) :in-theory (disable fps-sound))))

; a label DO rewritten keeps every statement one of the grammar
(defthm ldo-sugar-stmts
  (implies (stmts-p ss) (stmts-p (ldo-sugar ss stack term)))
  :hints (("Goal" :induct (ldo-sugar ss stack term) :in-theory (enable fgs))))

(defthm fortran-parse-sound
  (implies (mv-nth 0 (fortran-parse text fixed)) (fgu :program (mv-nth 1 (fortran-parse text fixed))))
  :hints (("Goal" :use ((:instance fpu-sound (nt :program)
                                     (toks (ldo-sugar (mv-nth 1 (parse-stmts (if fixed (flex-fixed text) (flex text)))) nil nil))))
           :in-theory (disable fpu-sound flex flex-fixed parse-stmts ldo-sugar fpu))))
