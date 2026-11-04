; gen-disch: the per-function discharge (GEN.md) for gen-inst's 10 functions.
; clotran's definitions are copied here (check-gen.bb checks that the guard and
; body ACL2 makes of each equal what clotran's certified books make). For each:
;   <fn>-a-ev: on int64 arguments, under its guard, a-ev of the body answers
;     without an error (no :range: no int64 overflow) the function's value;
;   <fn>-fortran-correct: with gen-inst's theorem, the generated Fortran
;     procedure, on int64 arguments and under the guard, answers the
;     function's value. No a-ev hypothesis is left.
; One guard does not cover the range: ex-aplook's (t) leaves req + 1
; overflowing at req = 2^63 - 1, so its theorems add (< req 2^63 - 1).

(in-package "ACL2")

(include-book "gen-inst")

; ---- clotran's definitions (model/heapg, heapsw, vmg, seqk, vmicg there);
; the constants and sb64ip written out

(defun hpg-add (n k)
  (declare (xargs :guard (and (natp n) (<= n 1099511627776) (natp k) (<= k 1099511627776))))
  (let ((s (+ (nfix n) (nfix k)))) (if (< s 1099511627776) s 1099511627776)))

(defun hpg-text-tag (tag)
  (declare (xargs :guard t))
  (or (equal tag 5) (equal tag 6) (equal tag 7) (equal tag 11) (equal tag 12) (equal tag 13) (equal tag 15)))

(defun hpg-s64 (x)
  (declare (xargs :guard t))
  (if (and (integerp x) (<= -9223372036854775808 x) (< x 9223372036854775808)) x 0))

(defun hpg-n40 (x)
  (declare (xargs :guard t))
  (if (and (natp x) (<= x 1099511627776)) x 0))

(defun bnd40p (x) (declare (xargs :guard t)) (and (integerp x) (<= 0 x) (<= x 1099511627776)))

(defun sk-step (kd i cnt)
  (declare (xargs :guard t))
  (cond ((equal kd 1) 1)
        ((equal kd 2) (if (and (integerp i) (integerp cnt) (<= 0 i) (< i cnt)) 2 0))
        ((equal kd 3) 3)
        ((equal kd 5) 5)
        ((equal kd 0) 0)
        (t 4)))

(defun sk-more (d) (declare (xargs :guard t)) (or (equal d 1) (equal d 2) (equal d 5)))

(defun ex-apstep (req k more)
  (declare (xargs :guard t))
  (cond ((not (and (integerp req) (<= 0 req) (integerp k))) 3)
        ((and (< k req) (equal more 1)) 1)
        ((or (< req k) (equal more 1)) 2)
        (t 3)))

(defun ex-aplook (req k)
  (declare (xargs :guard t))
  (if (and (integerp req) (<= 0 req) (integerp k) (<= k (+ req 1))) 1 0))

(defun vmicg-sat (x)
  (declare (xargs :guard (natp x)))
  (if (< x 1099511627776) x 1099511627776))

; ---- a-ev on a quoted body, opened one node at a time

(defthm a-ev-quoted
  (implies (and (syntaxp (quotep x)) (syntaxp (quotep n)))
           (equal (a-ev x env defs n)
                  (cond ((zp n) (mv :fuel nil))
                        ((symbolp x) (let ((b (lkp x env))) (if (consp b) (mv nil (cdr b)) (mv :unbound nil))))
                        ((atom x) (mv :syntax nil))
                        ((eq (car x) 'quote) (mv nil (kadr x)))
                        ((eq (car x) 'if)
                         (mv-let (e c) (a-ev (kadr x) env defs (1- n))
                           (cond (e (mv e nil))
                                 (c (a-ev (kaddr x) env defs (1- n)))
                                 (t (a-ev (kadddr x) env defs (1- n))))))
                        (t (mv-let (e vs) (a-ev-list (cdr x) env defs (1- n))
                             (cond (e (mv e nil))
                                   ((consp (car x))
                                    (a-ev (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) defs (1- n)))
                                   (t (let ((d (lkp (car x) defs)))
                                        (if (consp d)
                                            (a-ev (kaddr d) (pairlis$ (true-list-fix (kadr d)) vs) defs (1- n))
                                          (a-prim (car x) vs))))))))))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm a-ev-list-quoted
  (implies (and (syntaxp (quotep xs)) (syntaxp (quotep n)))
           (equal (a-ev-list xs env defs n)
                  (cond ((zp n) (mv :fuel nil))
                        ((atom xs) (mv nil nil))
                        (t (mv-let (e v) (a-ev (car xs) env defs (1- n))
                             (if e (mv e nil)
                               (mv-let (e vs) (a-ev-list (cdr xs) env defs (1- n))
                                 (if e (mv e nil) (mv nil (cons v vs))))))))))
  :hints (("Goal" :expand ((a-ev-list xs env defs n)))))

(in-theory (disable a-ev a-ev-list))

; ---- per function: the hypothesis is the guard ACL2 holds for fn (read from
; the world), the formals int64s, and any extra hypothesis, stated

(defun disch-int64s (vs) (if (atom vs) nil (cons (list 'int64p (car vs)) (disch-int64s (cdr vs)))))

(defun disch-sym (fn suffix) (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) suffix) fn))

(defun disch-events (fn fname raw bools extra w)
  (declare (xargs :mode :program))
  (let* ((vs (formals fn w))
         (hyps (append (disch-int64s vs) (list (guard fn nil w)) extra))
         (defs (list 'g-defs raw))
         (body (list 'kaddr (list 'lkp (list 'quote fn) defs)))
         (env (list 'pairlis$ (list 'quote vs) (cons 'list vs)))
         (call (cons fn vs))
         (aev (disch-sym fn "-A-EV")))
    `(progn
       (defthm ,aev
         (implies (and ,@hyps)
                  (equal (a-ev ,body ,env ,defs 100) (mv nil ,call)))
         :hints (("Goal" :in-theory (enable int64p))))
       (defthm ,(disch-sym fn "-FORTRAN-CORRECT")
         (let ((p (find-proc ,fname (mv-nth 1 (g-module ,raw ,bools)))))
           (implies (and ,@hyps (integerp fuel) (< (+ ,(+ 6 (len vs)) (acl2-count p)) fuel))
                    (equal (f-invoke p (g-lits (list ,@vs)) caller heap procs fuel)
                           (mv nil ,call heap))))
         :hints (("Goal" :in-theory (disable a-ev f-invoke g-lits ,fn)
                  :use ((:instance ,(disch-sym fn "-GEN") (args (list ,@vs)) (n 100)) ,aev)))))))

(defmacro disch (fn fname raw bools extra)
  `(make-event (value (disch-events ',fn ,fname ',raw ',bools ',extra (w state)))))

(disch hpg-add "hpg_add" *heapgn-raw* *heapgn-bools* nil)
(disch hpg-text-tag "hpg_text_tag" *heapgn-raw* *heapgn-bools* nil)
(disch hpg-s64 "hpg_s64" *heapgn-raw* *heapgn-bools* nil)
(disch hpg-n40 "hpg_n40" *heapgn-raw* *heapgn-bools* nil)
(disch bnd40p "bnd40p" *vmfg-raw* *vmfg-bools* nil)
(disch sk-step "sk_step" *vmfg-raw* *vmfg-bools* nil)
(disch sk-more "sk_more" *vmfg-raw* *vmfg-bools* nil)
(disch ex-apstep "ex_apstep" *vmfg-raw* *vmfg-bools* nil)
; the guard is t, but the Fortran's req + 1_int64 overflows at req = huge(0_int64)
(disch ex-aplook "ex_aplook" *vmfg-raw* *vmfg-bools* ((< req 9223372036854775807)))
(disch vmicg-sat "vmicg_sat" *vmicg-raw* *vmicg-bools* nil)

; the extra hypothesis is needed: at req = 2^63 - 1 (k any integer) the guard
; holds, and a-ev of the body answers :range -- the Fortran's req + 1_int64
; overflows there
(defthm ex-aplook-range-at-huge
  (equal (mv-nth 0 (a-ev (kaddr (lkp 'ex-aplook (g-defs *vmfg-raw*)))
                         (pairlis$ '(req k) (list 9223372036854775807 0)) (g-defs *vmfg-raw*) 100))
         :range)
  :hints (("Goal" :in-theory (enable a-ev a-ev-list))))
