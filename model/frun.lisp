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
                 (mv-let (e fr copies st) (me-decls (kaddr spec) env0 st cx fuel pfr nil (unit-key main) nil)
                   (declare (ignore copies))
                   (if e (mv e (close-lines (reverse (true-list-fix (st-out st)))))
                     (mv-let (fr st) (if (kadr spec) (mv fr st)          ; IMPLICIT NONE, or implicit typing (8.7)
                                       (implicit-vars (used-names (unit-exec main)) fr env0 st))
                       (mv-let (s st) (me-blk (unit-exec main) (cons fr env0) st cx fuel)
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
