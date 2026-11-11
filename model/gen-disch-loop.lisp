; gen-disch-loop: the per-function discharge (GEN.md) for clotran's
; tail-recursive hpg-size-class: gen-loopthm's g-fn-sem-loop instantiated on
; it (as gen-inst's gen-fn-thm instantiates g-fn-sem), and its hypotheses
; discharged as gen-disch does, with the n-dependent fuel bound.
;   hpg-size-class-a-ev: on int64 arguments, a-ev of the body with fuel
;     m >= 22 + 2 (64 - c) answers the function's value with no error --
;     in particular no :range: c + 1 is reached only for c < 64 and 2p only
;     for p <= 2^40, so both stay int64;
;   hpg-size-class-fortran-correct: the generated procedure, on int64
;     arguments under the guard, answers hpg-size-class's value.

(in-package "ACL2")

(include-book "gen-disch")
(include-book "gen-loopthm")

; clotran's definition (model/heapsw there; check-gen.bb checks the copy)
(defun hpg-size-class (n c p)
  (declare (xargs :measure (nfix (- (+ 1 1099511627776) (nfix p)))
                  :guard (and (natp n) (<= n 1099511627776) (natp c) (<= c 64) (natp p) (<= 1 p)
                              (<= p (* 2 1099511627776)))))
  (if (or (not (natp p)) (< p 1) (<= n p) (< 1099511627776 p) (not (natp c)) (<= 64 c))
      c
    (hpg-size-class n (+ 1 c) (* 2 p))))

; ---- the instance of g-fn-sem-loop, as gen-inst's gen-fn-thm

(defthm hpg-size-class-gen
  (let ((d (lkp 'hpg-size-class (g-defs *heapgn-raw*)))
        (p (find-proc "hpg_size_class" (mv-nth 1 (g-module *heapgn-raw* *heapgn-bools*)))))
    (implies (and (int64-listp args) (equal (len args) (len (kadr d)))
                  (not (mv-nth 0 (a-ev (kaddr d) (pairlis$ (kadr d) args) (g-defs *heapgn-raw*) n)))
                  (integerp fuel) (< (+ 6 (len args) (* (nfix n) (+ 2 (acl2-count p)))) fuel))
             (equal (f-invoke p (g-lits args) caller heap procs fuel)
                    (mv nil (mv-nth 1 (a-ev (kaddr d) (pairlis$ (kadr d) args) (g-defs *heapgn-raw*) n)) heap))))
  :hints (("Goal" :in-theory (disable a-ev f-invoke int64-listp g-lits pairlis$ len)
           :use (:instance g-fn-sem-loop (fn 'hpg-size-class) (defs (g-defs *heapgn-raw*))
                           (sigs (g-sigs *heapgn-raw* *heapgn-bools*))))))

; ---- a-ev of the body: one iteration, then the induction

(defconst *hsc-body* (kaddr (lkp 'hpg-size-class (g-defs *heapgn-raw*))))

; a-ev opened on a quoted term at symbolic fuel, except on the body itself:
; the self-call's a-ev is left for the induction hypothesis
(defthm a-ev-open-nb
  (implies (and (syntaxp (and (quotep x) (not (equal x (kwote *hsc-body*))))) (not (zp n)))
           (equal (a-ev x env defs n)
                  (cond ((symbolp x) (let ((b (lkp x env))) (if (consp b) (mv nil (cdr b)) (mv :unbound nil))))
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

(defthm a-ev-list-open-q
  (implies (and (syntaxp (quotep xs)) (not (zp n)))
           (equal (a-ev-list xs env defs n)
                  (cond ((atom xs) (mv nil nil))
                        (t (mv-let (e v) (a-ev (car xs) env defs (1- n))
                             (if e (mv e nil)
                               (mv-let (e vs) (a-ev-list (cdr xs) env defs (1- n))
                                 (if e (mv e nil) (mv nil (cons v vs))))))))))
  :hints (("Goal" :expand ((a-ev-list xs env defs n)))))

(in-theory (disable a-ev a-ev-list a-ev-quoted a-ev-list-quoted))

(defconst *hsc-defs* (g-defs *heapgn-raw*))

; one iteration: the self-call's a-ev at fuel m - 2
(defthm hsc-step
  (implies (and (int64p n) (int64p c) (int64p p) (natp m) (< 20 m))
           (equal (a-ev *hsc-body* (list (cons 'n n) (cons 'c c) (cons 'p p)) *hsc-defs* m)
                  (if (or (not (natp p)) (< p 1) (<= n p) (< 1099511627776 p) (not (natp c)) (<= 64 c))
                      (mv nil c)
                    (a-ev *hsc-body* (list (cons 'n n) (cons 'c (+ 1 c)) (cons 'p (* 2 p))) *hsc-defs* (- m 2)))))
  :hints (("Goal" :in-theory (enable int64p)
           :expand ((a-ev *hsc-body* (list (cons 'n n) (cons 'c c) (cons 'p p)) *hsc-defs* m)))))

(in-theory (disable a-ev-open-nb a-ev-list-open-q))

(defun hsc-ind (n c p m)
  (declare (xargs :measure (nfix (- (+ 1 1099511627776) (nfix p)))))
  (if (or (not (natp p)) (< p 1) (<= n p) (< 1099511627776 p) (not (natp c)) (<= 64 c))
      (list n c p m)
    (hsc-ind n (+ 1 c) (* 2 p) (- m 2))))

; at most 64 - c iterations, 2 fuel each; c + 1 and 2p stay int64
(defthm hpg-size-class-a-ev-m
  (implies (and (int64p n) (int64p c) (int64p p) (natp m)
                (<= (+ 22 (* 2 (nfix (- 64 (nfix c))))) m))
           (equal (a-ev *hsc-body* (list (cons 'n n) (cons 'c c) (cons 'p p)) *hsc-defs* m)
                  (mv nil (hpg-size-class n c p))))
  :hints (("Goal" :induct (hsc-ind n c p m)
           :in-theory (e/d (int64p) (a-ev-if a-ev-list-open a-ev-prim a-ev-sym a-ev-quote)))))

; the guard's c >= 0 gives at most 64 iterations: fuel 22 + 2 * 64
(defthm hpg-size-class-a-ev
  (implies (and (int64p n) (int64p c) (int64p p))
           (equal (a-ev *hsc-body* (pairlis$ '(n c p) (list n c p)) *hsc-defs* 150)
                  (mv nil (hpg-size-class n c p))))
  :hints (("Goal" :in-theory (disable hpg-size-class-a-ev-m)
           :use (:instance hpg-size-class-a-ev-m (m 150)))))

(defthm hpg-size-class-fortran-correct
  (let ((pr (find-proc "hpg_size_class" (mv-nth 1 (g-module *heapgn-raw* *heapgn-bools*)))))
    (implies (and (int64p n) (int64p c) (int64p p)
                  (integerp fuel) (< (+ 9 (* 150 (+ 2 (acl2-count pr)))) fuel))
             (equal (f-invoke pr (g-lits (list n c p)) caller heap procs fuel)
                    (mv nil (hpg-size-class n c p) heap))))
  :hints (("Goal" :in-theory (disable a-ev f-invoke g-lits hpg-size-class hpg-size-class-gen hpg-size-class-a-ev hpg-size-class-a-ev-m hsc-step a-ev-if a-ev-list-open a-ev-prim a-ev-sym a-ev-quote)
           :use ((:instance hpg-size-class-gen (args (list n c p)) (n 150)) hpg-size-class-a-ev))))
