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
(defun no-datas (ds) (declare (xargs :guard t)) (if (atom ds) nil (if (member-eq (kar (car ds)) '(:data :equiv)) (no-datas (cdr ds)) (cons (car ds) (no-datas (cdr ds))))))
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

;; R870 EQUIVALENCE (8.10.1): a main program's sets, its variables declared,
;; give fequiv.lisp's groups. Each object's storage starts at a unit, an
;; array element's at its offset in array element order (9.5.3.2) times its
;; units; the objects of a set start together (8.10.1.2), sets with a
;; variable in common are one group. Outside the subset, an :error :equiv:
;; a type other than integer, real, logical, complex, character; kinds not
;; all default unless one type and kind (C8110; a character's kind its
;; length); objects that cannot share storage so; an object initialized.
(defun eqv-subs (as env st cx fuel)  ; (mv err idx st): an element's subscripts' values
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count as)))
  (if (atom as) (mv nil nil st)
    (mv-let (v st) (me-ev :expr (kadr (car as)) env st cx fuel)
      (if (not (ival-scalar v)) (mv (err :equiv) nil st)
        (mv-let (e idx st) (eqv-subs (cdr as) env st cx fuel) (mv e (cons (v-num v) idx) st))))))
(defun eqv-tk (v) (declare (xargs :guard t)) (if (aval-p v) (list (a-ty v) (a-k v)) (list (scal-ty v) (scal-k v))))
(defun eqv-item (a fr env st cx fuel)  ; (mv err (loc . unit) st)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((p (lone-prim (kadr a))) (b (cdr (alk (tok-name (kadr p)) fr))) (loc (kadr b)) (v (st-get loc st)))
    (cond ((not (and (eq (kar b) :var) (eq (kaddr b) :rw) (member-eq (car (eqv-tk v)) '(:i :r :l :z :c)))) (mv (err :equiv) nil st))
          ((eq (kar p) :name) (mv nil (cons loc 0) st))
          ((not (aval-p v)) (mv (err :equiv) nil st))
          (t (mv-let (e idx st) (eqv-subs (kaddr p) env st cx fuel)
               (let ((off (and (not e) (arr-offset idx (a-lbs v) (a-ubs v)))))
                 (if (natp off) (mv nil (cons loc (* off (if (eq (a-ty v) :z) 2 1))) st) (mv (err :equiv) nil st))))))))
(defun eqv-union (a b)               ; (mv ok alist): a's (loc . start)s with b's, a loc at one start
  (declare (xargs :guard t))
  (if (atom a) (mv t b)
    (let ((c (alk (kar (car a)) b)))
      (cond ((null c) (eqv-union (cdr a) (cons (car a) b)))
            ((equal (cdr c) (kdr (car a))) (eqv-union (cdr a) b))
            (t (mv nil nil))))))
(defun eqv-shift (s d) (declare (xargs :guard t)) (if (atom s) nil (cons (cons (kar (car s)) (+ (ifix d) (ifix (kdr (car s))))) (eqv-shift (cdr s) d))))
(defun eqv-common (s g) (declare (xargs :guard t)) (cond ((atom s) nil) ((alk (kar (car s)) g) (car s)) (t (eqv-common (cdr s) g))))
(defun eqv-merge (s gs)              ; (mv ok groups): s joined to the groups it meets
  (declare (xargs :guard t :measure (len gs)))
  (if (atom gs) (mv t (list s))
    (let ((c (eqv-common s (car gs))))
      (if (null c) (mv-let (ok r) (eqv-merge s (cdr gs)) (mv ok (cons (car gs) r)))
        (mv-let (ok u) (eqv-union (eqv-shift s (- (ifix (cdr (alk (car c) (car gs)))) (ifix (cdr c)))) (car gs))
          (if ok (eqv-merge u (cdr gs)) (mv nil nil)))))))
(defun eqv-set (as fr env st cx fuel s tks)  ; (mv err s tks st): a set's (loc . start)s, its objects' (ty k)s
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count as)))
  (if (atom as) (mv nil s tks st)
    (mv-let (e it st) (eqv-item (car as) fr env st cx fuel)
      (if e (mv e nil nil st)
        (mv-let (ok s2) (eqv-union (list (cons (car it) (- (cdr it)))) s)
          (if ok (eqv-set (cdr as) fr env st cx fuel s2 (cons (eqv-tk (st-get (car it) st)) tks)) (mv (err :equiv) nil nil st)))))))
(defun eqv-kinds-ok (tks)            ; C8110: numeric or logical all of default kind, or one type and kind
  (declare (xargs :guard t))
  (or (and (subsetp-equal (strip-cars-safe tks) '(:i :r :l :z)) (subsetp-equal (strip-cadrs-safe tks) '(4)))
      (and (consp tks) (subsetp-equal tks (list (car tks))))))
(defun eqv-all-undef (us) (declare (xargs :guard t)) (if (atom us) t (and (eq (kaddr (car us)) :u) (eqv-all-undef (cdr us)))))
(defun eqv-install (g ms st)         ; each member's key (:eqv loc) to the group g, its storage undefined
  (declare (xargs :guard t))
  (cond ((atom ms) st)
        ((not (eqv-all-undef (eqv-units (st-get (kar (car ms)) st)))) (err :equiv))
        (t (eqv-install g (cdr ms) (st-save (list :eqv (kar (car ms))) g st)))))
(defun eqv-installs (gs st)
  (declare (xargs :guard t))
  (cond ((atom gs) st) ((errp st) st) (t (eqv-installs (cdr gs) (eqv-install (car gs) (car gs) st)))))
(defun me-equiv (sets fr env st cx fuel gs)  ; (mv err st)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count sets)))
  (if (atom sets)
      (let ((st2 (eqv-installs gs st))) (if (errp st2) (mv st2 st) (mv nil st2)))
    (mv-let (e s tks st) (eqv-set (car sets) fr env st cx fuel nil nil)
      (if e (mv e st)
        (mv-let (ok gs) (eqv-merge s gs)
          (if (and ok (eqv-kinds-ok tks)) (me-equiv (cdr sets) fr env st cx fuel gs) (mv (err :equiv) st)))))))
(defun unit-equivs (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (append (if (eq (kar (car ds)) :equiv) (true-list-fix (kadr (car ds))) nil) (unit-equivs (cdr ds)))))

(defun prim-names (ps)               ; the names of primaries (:name tk) or (:ref tk ...)
  (declare (xargs :guard t))
  (if (atom ps) nil (append (if (member-eq (kar (car ps)) '(:name :ref)) (list (tok-name (kadr (car ps)))) nil) (prim-names (cdr ps)))))
(defun lone-prims (as) (declare (xargs :guard t)) (if (atom as) nil (cons (lone-prim (kadr (car as))) (lone-prims (cdr as)))))
(defun eqv-names (ss)                ; an EQUIVALENCE's objects' names
  (declare (xargs :guard t))
  (if (atom ss) nil (append (prim-names (lone-prims (car ss))) (eqv-names (cdr ss)))))
(defun data-names (ss) (declare (xargs :guard t)) (if (atom ss) nil (append (prim-names (kar (car ss))) (data-names (cdr ss)))))
(defun spec-names (ds)               ; the names only a main's DATA or EQUIVALENCE may give (8.7)
  (declare (xargs :guard t))
  (cond ((atom ds) nil)
        ((eq (kar (car ds)) :data) (append (data-names (kadr (car ds))) (spec-names (cdr ds))))
        ((eq (kar (car ds)) :equiv) (append (eqv-names (kadr (car ds))) (spec-names (cdr ds))))
        (t (spec-names (cdr ds)))))
(defun find-main (units)
  (declare (xargs :guard t))
  (if (atom units) nil (if (eq (kar (car units)) :main) (car units) (find-main (cdr units)))))

(defun me-program (units in fuel)    ; (mv status lines): in the input's records
  (declare (xargs :guard t :verify-guards nil))
  (let ((gframe (ext-frame units)) (st (mk-st8 nil 0 nil nil nil nil (cons in nil) nil)) (main (find-main units)))
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
                                       (implicit-vars (append (used-names (unit-exec main)) (spec-names (kaddr spec))) fr env0 st (unit-rules main)))
                       (mv-let (s st) (mv-let (e st) (mv-let (e st) (me-equiv (unit-equivs (kaddr spec)) fr (cons fr env0) st cx fuel nil)
                                                       (if e (mv e st) (me-data (unit-datas (kaddr spec)) (cons fr env0) st cx fuel)))
                                        (mv-let (sfr exec) (sfun-frame (unit-exec main) fr st (unit-rules main) (kadr spec))
                                          (if e (mv e st) (me-blk exec (if sfr (list* sfr fr env0) (cons fr env0)) st cx fuel))))
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
