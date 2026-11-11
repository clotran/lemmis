; gen-disch-call: the per-function discharge (GEN.md) for clotran's
; hpg-class-len, the 12th checked function: a tail-recursive loop that calls
; hpg-n40. g-fn-sem-loop is instantiated with cs = (hpg-n40) (as
; gen-disch-loop does with cs = nil); its oracle hypotheses (a-orc, p-orc)
; are about the unconstrained f-call-val, so the instance is functionally
; instantiated with hcl-orc, the oracle that answers hpg-n40 on "hpg_n40",
; and the two defun-sks copied with hcl-orc in its place. Then:
;   a-orc-h: hcl-orc is a-ev's answer on hpg-n40 (its body opened at any fuel);
;   p-orc-h: hcl-orc is what the procedures answer, when hpg_n40 is the
;     generated procedure (f-invoke-args, then hpg-n40-fortran-correct);
;   hpg-class-len-a-ev: a-ev of the body, by induction as hpg-size-class's
;     (at most 64 iterations; 2 * (hpg-n40 p) <= 2^41 stays int64).

(in-package "ACL2")

(include-book "gen-disch-loop")
(include-book "gen-callarg")

; a-ev's openers unroll a recursive body without limit
(in-theory (disable a-ev-if a-ev-sym a-ev-prim a-ev-list-open a-ev-quote a-ev-defined-call))

(defmacro hproc (name) `(find-proc ,name (mv-nth 1 (g-module *heapgn-raw* *heapgn-bools*))))

; ---- the instance of g-fn-sem-loop, cs = (hpg-n40)

(defthm hpg-class-len-gen
  (let ((d (lkp 'hpg-class-len (g-defs *heapgn-raw*))))
    (implies (and (int64-listp args) (equal (len args) (len (kadr d)))
                  (not (mv-nth 0 (a-ev (kaddr d) (pairlis$ (kadr d) args) (g-defs *heapgn-raw*) n)))
                  (a-orc (g-defs *heapgn-raw*) (g-sigs *heapgn-raw* *heapgn-bools*) '(hpg-n40))
                  (p-orc procs heap b) (natp b)
                  (natp c) (<= (* (+ 3 b) (+ 2 (acl2-count (hproc "hpg_class_len")))) c)
                  (integerp fuel) (< (+ 6 (len args) (* (nfix n) c)) fuel))
             (equal (f-invoke (hproc "hpg_class_len") (g-lits args) caller heap procs fuel)
                    (mv nil (mv-nth 1 (a-ev (kaddr d) (pairlis$ (kadr d) args) (g-defs *heapgn-raw*) n)) heap))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable a-ev f-invoke int64-listp g-lits pairlis$ len p-orc a-orc)
           :use ((:instance g-fn-sem-loop (fn 'hpg-class-len) (defs (g-defs *heapgn-raw*))
                            (sigs (g-sigs *heapgn-raw* *heapgn-bools*)) (cs '(hpg-n40)))))))

; ---- the oracle, and a-orc and p-orc with it in f-call-val's place

(defun hcl-orc (name vals)
  (if (and (equal name "hpg_n40") (int64-listp vals) (equal (len vals) 1))
      (mv nil (hpg-n40 (car vals)))
    (mv :unknown nil)))

(defun-sk a-orc-h (defs sigs cs)
  (forall (f vals n)
    (implies (and (member-equal f cs) (int64-listp vals) (equal (len vals) (len (kar (cdr (lkp f sigs)))))
                  (not (mv-nth 0 (a-call f vals defs n))))
             (and (equal (hcl-orc (g-sym f nil) vals) (mv nil (mv-nth 1 (a-call f vals defs n))))
                  (scalar-ok (kadr (cdr (lkp f sigs))) (mv-nth 1 (a-call f vals defs n)))))))

(defun-sk p-orc-h (procs heap b)
  (forall (x fr ks fuel)
    (implies (and (eq (kar x) :fcall) (not (mv-nth 0 (hcl-orc (kadr x) ks)))
                  (evs-at (kaddr x) fr heap procs (- fuel 2) ks) (integerp fuel) (< b fuel))
             (equal (f-ev x fr heap procs fuel) (mv nil (mv-nth 1 (hcl-orc (kadr x) ks)))))))

(defthm hpg-class-len-gen-h
  (let ((d (lkp 'hpg-class-len (g-defs *heapgn-raw*))))
    (implies (and (int64-listp args) (equal (len args) (len (kadr d)))
                  (not (mv-nth 0 (a-ev (kaddr d) (pairlis$ (kadr d) args) (g-defs *heapgn-raw*) n)))
                  (a-orc-h (g-defs *heapgn-raw*) (g-sigs *heapgn-raw* *heapgn-bools*) '(hpg-n40))
                  (p-orc-h procs heap b) (natp b)
                  (natp c) (<= (* (+ 3 b) (+ 2 (acl2-count (hproc "hpg_class_len")))) c)
                  (integerp fuel) (< (+ 6 (len args) (* (nfix n) c)) fuel))
             (equal (f-invoke (hproc "hpg_class_len") (g-lits args) caller heap procs fuel)
                    (mv nil (mv-nth 1 (a-ev (kaddr d) (pairlis$ (kadr d) args) (g-defs *heapgn-raw*) n)) heap))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable hcl-orc hpg-n40 a-orc-h p-orc-h a-ev f-invoke f-ev evs-at a-call)
           :use ((:functional-instance hpg-class-len-gen
                  (f-call-val hcl-orc)
                  (a-orc a-orc-h) (a-orc-witness a-orc-h-witness)
                  (p-orc p-orc-h) (p-orc-witness p-orc-h-witness))
                 (:definition a-orc-h) a-orc-h-necc (:definition p-orc-h) p-orc-h-necc))
          ("Subgoal 4" :in-theory (disable hcl-orc hpg-n40 p-orc-h f-ev evs-at) :use (p-orc-h-necc))
          ("Subgoal 3" :in-theory (e/d (p-orc-h) (hcl-orc hpg-n40 f-ev evs-at)))
          ("Subgoal 2" :in-theory (disable hcl-orc hpg-n40 a-orc-h a-ev a-call) :use (a-orc-h-necc))
          ("Subgoal 1" :in-theory (e/d (a-orc-h) (hcl-orc hpg-n40 a-ev a-call)))))

; ---- a-orc-h: hcl-orc is a-ev's answer on hpg-n40, at any fuel

(defconst *n40-body* (kaddr (lkp 'hpg-n40 (g-defs *heapgn-raw*))))
(defconst *hcl-body* (kaddr (lkp 'hpg-class-len (g-defs *heapgn-raw*))))

(defthm a-ev-zp (implies (zp n) (equal (a-ev x env defs n) (mv :fuel nil))) :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm a-ev-open-hcl
  (implies (and (syntaxp (and (quotep x) (not (equal x (kwote *hcl-body*))))) (not (zp n)))
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

(defthm a-ev-nonnat (implies (not (natp n)) (car (a-ev x env defs n))) :rule-classes nil
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm n40-a-ev-any
  (implies (and (int64p x) (natp n) (not (car (a-ev *n40-body* (list (cons 'x x)) *hsc-defs* n))))
           (equal (mv-nth 1 (a-ev *n40-body* (list (cons 'x x)) *hsc-defs* n)) (hpg-n40 x)))
  :hints (("Goal" :in-theory (enable int64p a-ev-open-hcl a-ev-list-open-q a-ev-zp) :cases ((equal n 0) (equal n 1) (equal n 2) (equal n 3) (equal n 4) (equal n 5) (equal n 6) (equal n 7) (equal n 8) (< 8 n)))))

(defthm a-call-n40
  (implies (and (int64-listp vals) (equal (len vals) 1) (not (car (a-call 'hpg-n40 vals *hsc-defs* n))))
           (equal (mv-nth 1 (a-call 'hpg-n40 vals *hsc-defs* n)) (hpg-n40 (car vals))))
  :hints (("Goal" :in-theory (disable n40-a-ev-any a-ev hpg-n40) :expand ((int64-listp vals) (int64-listp (cdr vals)))
           :use ((:instance n40-a-ev-any (x (car vals))) (:instance a-ev-nonnat (x *n40-body*) (env (list (cons 'x (car vals)))) (defs *hsc-defs*))))))

(defthm int64p-hpg-n40 (int64p (hpg-n40 x)) :hints (("Goal" :in-theory (enable int64p))))

(defthm a-orc-h-hcl
  (a-orc-h (g-defs *heapgn-raw*) (g-sigs *heapgn-raw* *heapgn-bools*) '(hpg-n40))
  :hints (("Goal" :in-theory (e/d (a-orc-h) (a-call hpg-n40 int64-listp)))))

; ---- p-orc-h: hcl-orc is what hpg_n40's procedure answers

(defun int64-cars (ks) (if (consp ks) (and (int64p (car ks)) (int64-cars (cdr ks))) t))

(defthm evs-at-args-at
  (implies (and (evs-at as fr heap procs fuel ks) (int64-cars ks)) (args-at as fr heap procs fuel ks))
  :hints (("Goal" :induct (evs-at as fr heap procs fuel ks) :in-theory (disable f-ev))))

(defthm int64-listp-cars (implies (int64-listp ks) (int64-cars ks)))

(defthm int64-list-one
  (implies (and (int64-listp ks) (equal (len ks) 1)) (equal (list (car ks)) ks))
  :hints (("Goal" :expand ((int64-listp ks) (int64-listp (cdr ks))))))

(defthm p-orc-h-hcl
  (implies (equal (find-proc "hpg_n40" procs) (hproc "hpg_n40"))
           (p-orc-h procs heap (+ 8 (acl2-count (hproc "hpg_n40")))))
  :hints (("Goal" :in-theory (e/d (p-orc-h) (f-ev f-invoke evs-at args-at hpg-n40 g-lits f-invoke-args
                                             hpg-n40-fortran-correct))
           :expand ((:free (x fr fuel) (f-ev x fr heap procs fuel)))
           :use ((:instance f-invoke-args (p (hproc "hpg_n40")) (vs '(x)) (caller2 (mv-nth 1 (p-orc-h-witness procs heap (+ 8 (acl2-count (hproc "hpg_n40"))))))
                            (as (kaddr (mv-nth 0 (p-orc-h-witness procs heap (+ 8 (acl2-count (hproc "hpg_n40")))))))
                            (caller (mv-nth 1 (p-orc-h-witness procs heap (+ 8 (acl2-count (hproc "hpg_n40"))))))
                            (ks (mv-nth 2 (p-orc-h-witness procs heap (+ 8 (acl2-count (hproc "hpg_n40"))))))
                            (fuel (+ -1 (mv-nth 3 (p-orc-h-witness procs heap (+ 8 (acl2-count (hproc "hpg_n40"))))))))
                 (:instance hpg-n40-fortran-correct
                            (x (car (mv-nth 2 (p-orc-h-witness procs heap (+ 8 (acl2-count (hproc "hpg_n40")))))))
                            (caller (mv-nth 1 (p-orc-h-witness procs heap (+ 8 (acl2-count (hproc "hpg_n40"))))))
                            (fuel (+ -1 (mv-nth 3 (p-orc-h-witness procs heap (+ 8 (acl2-count (hproc "hpg_n40"))))))))))))

; ---- a-ev of hpg-class-len's body: one iteration, then the induction

(defmacro hcl-exit (c k) `(or (not (natp ,c)) (not (natp ,k)) (<= ,c ,k) (< 64 ,c)))

(defthm hcl-step
  (implies (and (int64p c) (int64p k) (int64p p) (natp m) (< 40 m))
           (equal (a-ev *hcl-body* (list (cons 'c c) (cons 'k k) (cons 'p p)) *hsc-defs* m)
                  (if (hcl-exit c k)
                      (mv nil (hpg-n40 p))
                    (a-ev *hcl-body* (list (cons 'c c) (cons 'k (+ 1 k)) (cons 'p (hpg-n40 (* 2 (hpg-n40 p)))))
                          *hsc-defs* (- m 2)))))
  :hints (("Goal" :in-theory (enable int64p a-ev-open-hcl a-ev-list-open-q)
           :expand ((a-ev *hcl-body* (list (cons 'c c) (cons 'k k) (cons 'p p)) *hsc-defs* m)))))

(in-theory (disable a-ev-open-hcl a-ev-list-open-q))

(defun hcl-ind (c k p m)
  (declare (xargs :measure (nfix (- (nfix c) (nfix k)))))
  (if (hcl-exit c k) (list c k p m) (hcl-ind c (+ 1 k) (hpg-n40 (* 2 (hpg-n40 p))) (- m 2))))

; at most 64 - k iterations, 2 fuel each; k + 1 and 2 * (hpg-n40 p) <= 2^41 stay int64
(defthm hpg-class-len-a-ev-m
  (implies (and (int64p c) (int64p k) (int64p p) (natp m) (< 40 m) (<= 170 (+ m (* 2 (nfix k)))))
           (equal (a-ev *hcl-body* (list (cons 'c c) (cons 'k k) (cons 'p p)) *hsc-defs* m)
                  (mv nil (hpg-class-len c k p))))
  :hints (("Goal" :induct (hcl-ind c k p m) :in-theory (e/d (int64p) (hpg-n40)))))

(defthm hpg-class-len-a-ev
  (implies (and (int64p c) (int64p k) (int64p p))
           (equal (a-ev *hcl-body* (pairlis$ '(c k p) (list c k p)) *hsc-defs* 200)
                  (mv nil (hpg-class-len c k p))))
  :hints (("Goal" :in-theory (disable hpg-class-len-a-ev-m hcl-step hpg-class-len hpg-n40 a-ev) :use ((:instance hpg-class-len-a-ev-m (m 200))))))

; ---- the theorem: the generated procedure answers hpg-class-len, when the
; procedures' hpg_n40 is the generated one; b = 8 + its size, so the fuel
; factor is (3 + b) * (2 + size)

(defthm hpg-class-len-fortran-correct
  (let ((pr (hproc "hpg_class_len")))
    (implies (and (int64p c) (int64p k) (int64p p)
                  (equal (find-proc "hpg_n40" procs) (hproc "hpg_n40"))
                  (integerp fuel)
                  (< (+ 9 (* 200 (* (+ 11 (acl2-count (hproc "hpg_n40"))) (+ 2 (acl2-count pr))))) fuel))
             (equal (f-invoke pr (g-lits (list c k p)) caller heap procs fuel)
                    (mv nil (hpg-class-len c k p) heap))))
  :hints (("Goal" :in-theory (disable a-ev f-invoke g-lits hpg-class-len hpg-class-len-a-ev hpg-class-len-a-ev-m hcl-step
                                      p-orc-h a-orc-h p-orc-h-hcl a-orc-h-hcl)
           :use ((:instance hpg-class-len-gen-h (args (list c k p)) (n 200) (b (+ 8 (acl2-count (hproc "hpg_n40"))))
                            (c (* (+ 11 (acl2-count (hproc "hpg_n40"))) (+ 2 (acl2-count (hproc "hpg_class_len"))))))
                 hpg-class-len-a-ev p-orc-h-hcl a-orc-h-hcl))))
