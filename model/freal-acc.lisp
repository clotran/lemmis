; freal-acc: what fl-round guarantees (stage S1 of STUDY-fp-2026-11-20), and
; the single-rounding statement for + - * / and conversion built on it (S2).
; Nothing here changes fsem; it states facts about freal.lisp's definitions.
;
; Proved from fl-round's definition with arithmetic-5, not via RTL: see
; SCOPE.md (kestrel/floats/rtl pulls in rtl/rel11, and relating fl-round
; to rtl::rne/drnd costs as much as the direct proofs below).
;
; Public names:
;   fl-ulp-of k q      the spacing of format k at q (2^(max(flog2|q|,emin)-p+1))
;   fl-repr-p k x      x is a finite value of format k (0, or a multiple of its
;                      ulp below 2^(emax+1))
;   fl-err-bound k q   max(2^-p |q|, 2^(emin-p)): u|q| normal, half the least
;                      subnormal below 2^emin
; S1: fl-round-neg, fl-round-mono, fl-round-repr (fixes representable values),
;   fl-round-repr-p (rounds onto them), fl-round-idem, fl-round-nearest,
;   fl-round-even (ties to even), fl-round-half-ulp, fl-round-rel-err,
;   fl-round-sub-err, fl-round-err, fl-round-finite (no overflow up to HUGE)
; S2: fl-{add,sub,mul,div,conv}-round (the result is fl-round of the exact
;   value), -err, -nearest, -exact; fl-sterbenz, fl-sub-sterbenz. SQRT:
;   fsqrt-acc.lisp (fl-sqrt-correct).

(in-package "ACL2")
(include-book "freal")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fla-ex (k a) (declare (xargs :guard (and (rationalp a) (< 0 a)))) (max (flog2 a) (fl-emin k)))
(defun fla-ulp (k a)
  (declare (xargs :guard (and (rationalp a) (< 0 a))))
  (expt 2 (- (fla-ex k a) (- (fl-prec k) 1))))
(defun fl-ulp-of (k q)
  (declare (xargs :guard (rationalp q)))
  (if (and (rationalp q) (not (= q 0))) (fla-ulp k (abs q)) (expt 2 (- (fl-emin k) (- (fl-prec k) 1)))))
(defun fl-repr-p (k x)
  (declare (xargs :guard t))
  (and (rationalp x)
       (or (= x 0)
           (and (< (abs x) (expt 2 (+ 1 (fl-emax k))))
                (integerp (/ x (fla-ulp k (abs x))))))))
(defun fl-err-bound (k q)
  (declare (xargs :guard (rationalp q)))
  (max (* (expt 2 (- (fl-prec k))) (abs q)) (expt 2 (- (fl-emin k) (fl-prec k)))))

;; ---- flog2 and rne (as in fintr.lisp, where they are local) ----------------

(local (defthm ilen-bounds
  (implies (posp n)
           (and (<= (expt 2 (+ -1 (integer-length n))) n)
                (< n (expt 2 (integer-length n)))))
  :rule-classes :linear))

(local (defthm nd-lt-prod
  (implies (and (rationalp p) (rationalp q) (< 0 p) (< 0 q) (rationalp n) (rationalp d) (< 0 d)
                (or (and (<= p n) (< d q)) (and (< p n) (<= d q))))
           (< (* p d) (* n q)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t))))
(local (defthm nd-lt
  (implies (and (rationalp p) (rationalp q) (< 0 p) (< 0 q) (rationalp n) (rationalp d) (< 0 d)
                (or (and (<= p n) (< d q)) (and (< p n) (<= d q))))
           (< (/ p q) (/ n d)))
  :rule-classes nil
  :hints (("Goal" :use (nd-lt-prod (:instance (:theorem (implies (and (rationalp x) (rationalp y) (rationalp z) (< x y) (< 0 z)) (< (* x z) (* y z))))
                                               (x (* p d)) (y (* n q)) (z (/ (* q d)))))))))

(defthm fla-flog2-bounds                 ; exported for fsqrt-acc
  (implies (and (rationalp a) (< 0 a))
           (and (<= (expt 2 (flog2 a)) a) (< a (expt 2 (+ 1 (flog2 a))))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance nd-lt (n (numerator a)) (d (denominator a))
                                   (p (expt 2 (+ -1 (integer-length (numerator a)))))
                                   (q (expt 2 (integer-length (denominator a)))))
                        (:instance nd-lt (p (numerator a)) (q (denominator a))
                                   (n (expt 2 (integer-length (numerator a))))
                                   (d (expt 2 (+ -1 (integer-length (denominator a))))))))))

(defthm fla-flog2-int (integerp (flog2 a)) :rule-classes :type-prescription)

(local (defthm expt2-ge-1 (implies (natp n) (<= 1 (expt 2 n))) :rule-classes :linear))

(local (defthm expt2-le
  (implies (and (integerp i) (integerp j) (<= j i)) (<= (expt 2 j) (expt 2 i)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable expt2-ge-1)
                  :use ((:instance expt2-ge-1 (n (- i j)))
                        (:instance (:theorem (implies (and (integerp i) (integerp j)) (equal (expt 2 i) (* (expt 2 j) (expt 2 (- i j)))))))))))) 

(local (defthm expt-sandwich
  (implies (and (integerp i) (integerp j) (rationalp x) (<= (expt 2 i) x) (< x (expt 2 (+ 1 j))))
           (<= i j))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance expt2-le (j (+ 1 j)) (i i)))))))

(local (defthm flog2-unique     ; 2^i <= a < 2^(i+1) fixes flog2 a
  (implies (and (rationalp a) (< 0 a) (integerp i) (<= (expt 2 i) a) (< a (expt 2 (+ 1 i))))
           (equal (flog2 a) i))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable flog2)
                  :use ((:instance expt-sandwich (i i) (j (flog2 a)) (x a))
                        (:instance expt-sandwich (i (flog2 a)) (j i) (x a)))))))

(local (defthm flog2-mono
  (implies (and (rationalp a) (rationalp b) (< 0 a) (<= a b))
           (<= (flog2 a) (flog2 b)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable flog2)
                  :use ((:instance expt-sandwich (i (flog2 a)) (j (flog2 b)) (x a)))))))

(local (defthm rne-bounds
  (implies (rationalp a) (and (<= (floor a 1) (rne a)) (<= (rne a) (+ 1 (floor a 1)))))
  :rule-classes :linear))

(local (defthm floor-mono
  (implies (and (rationalp a) (rationalp b) (<= a b)) (<= (floor a 1) (floor b 1)))
  :rule-classes :linear))

(local (defthm rne-same-floor
  (implies (and (rationalp a) (rationalp b) (<= a b) (equal (floor a 1) (floor b 1)))
           (<= (rne a) (rne b)))
  :rule-classes nil))

(local (defthm rne-mono
  (implies (and (rationalp a) (rationalp b) (<= a b)) (<= (rne a) (rne b)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable rne) :use rne-same-floor :cases ((< (floor a 1) (floor b 1)))))))

(local (defthm rne-int (implies (integerp a) (equal (rne a) a))))
(local (defthm rne-integerp (implies (rationalp m) (integerp (rne m))) :rule-classes :type-prescription))

(local (defthm rne-shape
  (implies (rationalp m)
           (and (integerp (floor m 1)) (<= (floor m 1) m) (< m (+ 1 (floor m 1)))
                (or (equal (rne m) (floor m 1)) (equal (rne m) (+ 1 (floor m 1))))
                (implies (< (- m (floor m 1)) 1/2) (equal (rne m) (floor m 1)))
                (implies (< 1/2 (- m (floor m 1))) (equal (rne m) (+ 1 (floor m 1))))
                (implies (equal (- m (floor m 1)) 1/2) (evenp (rne m)))))
  :rule-classes nil))

(local (defthm rne-nearest-aux
  (implies (and (integerp f) (rationalp m) (<= f m) (< m (+ 1 f)) (integerp n)
                (or (equal x f) (equal x (+ f 1)))
                (implies (< (- m f) 1/2) (equal x f))
                (implies (< 1/2 (- m f)) (equal x (+ f 1))))
           (and (<= (abs (- x m)) (abs (- n m))) (<= (abs (- x m)) 1/2)
                (implies (equal (abs (- x m)) 1/2) (equal (- m f) 1/2))))
  :rule-classes nil
  :hints (("Goal" :cases ((<= n f))))))

(local (defthm rne-nearest-int  ; no integer is nearer to m than rne m
  (implies (and (rationalp m) (integerp n))
           (and (<= (abs (- (rne m) m)) (abs (- n m))) (<= (abs (- (rne m) m)) 1/2)
                (implies (equal (abs (- (rne m) m)) 1/2) (evenp (rne m)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne floor abs evenp)
                  :use (rne-shape (:instance rne-nearest-aux (f (floor m 1)) (x (rne m))))))))

(local (defthm rne-nonneg (implies (and (rationalp m) (<= 0 m)) (<= 0 (rne m))) :rule-classes :linear))

;; ---- the format's parameters, opaque from here on ---------------------------

(local (defthm fl-params
  (and (integerp (fl-prec k)) (<= 2 (fl-prec k)) (integerp (fl-emin k)) (integerp (fl-emax k))
       (< (fl-emin k) 0) (< 0 (fl-emax k)))
  :rule-classes ((:type-prescription :corollary (integerp (fl-prec k)))
                 (:type-prescription :corollary (integerp (fl-emin k)))
                 (:type-prescription :corollary (integerp (fl-emax k)))
                 (:linear :corollary (and (<= 2 (fl-prec k)) (< (fl-emin k) 0) (< 0 (fl-emax k)))))))
(local (in-theory (disable fl-prec fl-emin fl-emax)))

(local (defthm fla-ex-int (integerp (fla-ex k a)) :rule-classes :type-prescription))
(local (defthm fla-ex-ge (and (<= (fl-emin k) (fla-ex k a)) (<= (flog2 a) (fla-ex k a))) :rule-classes :linear))
(local (defthm fla-ulp-pos (< 0 (fla-ulp k a)) :rule-classes :linear))
(local (defthm fla-ulp-rat (rationalp (fla-ulp k a)) :rule-classes :type-prescription))

(local (defthm fla-ex-mono
  (implies (and (rationalp a) (rationalp b) (< 0 a) (<= a b)) (<= (fla-ex k a) (fla-ex k b)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable flog2)))))

(defun fla-rv (k a)                  ; fl-round's value of a > 0 before overflow
  (declare (xargs :guard (and (rationalp a) (< 0 a))))
  (* (rne (/ a (fla-ulp k a))) (fla-ulp k a)))

(defthm fl-round-pos                 ; a > 0: fla-rv, or +inf past the top (exported for fsqrt-acc)
  (implies (and (rationalp a) (< 0 a))
           (equal (fl-round k a)
                  (if (<= (expt 2 (+ 1 (fl-emax k))) (fla-rv k a)) :pinf (fla-rv k a))))
  :hints (("Goal" :in-theory (disable rne flog2))))

(local (defthm fl-round-zero (equal (fl-round k 0) 0)))

(defthm fl-round-neg               ; sign symmetry
  (implies (and (rationalp q) (not (= q 0)))
           (equal (fl-round k (- q)) (fl-neg (fl-round k q))))
  :hints (("Goal" :in-theory (disable rne flog2))))

(local (defthm abs-rational (implies (rationalp x) (and (rationalp (abs x)) (<= 0 (abs x)))) :rule-classes :type-prescription))

(local (defthm abs-scale
  (implies (and (rationalp x) (rationalp u) (< 0 u)) (equal (abs (* x u)) (* u (abs x))))
  :rule-classes nil))

(local (defthm mul-le
  (implies (and (rationalp x) (rationalp y) (rationalp u) (< 0 u) (<= x y)) (<= (* u x) (* u y)))
  :rule-classes nil))

(local (defthm rvu-nearest
  (implies (and (rationalp a) (rationalp u) (< 0 u) (integerp n))
           (and (<= (abs (- (* (rne (/ a u)) u) a)) (abs (- (* n u) a)))
                (<= (abs (- (* (rne (/ a u)) u) a)) (/ u 2))
                (implies (equal (abs (- (* (rne (/ a u)) u) a)) (/ u 2)) (evenp (rne (/ a u))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne abs evenp)
                  :use ((:instance rne-nearest-int (m (/ a u)))
                        (:instance abs-scale
                                   (x (- (rne (/ a u)) (/ a u))))
                        (:instance abs-scale
                                   (x (- n (/ a u))))
                        (:instance mul-le (x (abs (- (rne (/ a u)) (/ a u)))) (y (abs (- n (/ a u)))))
                        (:instance mul-le (x (abs (- (rne (/ a u)) (/ a u)))) (y 1/2)))))))

(local (defthm fla-rv-nearest
  (implies (and (rationalp a) (< 0 a) (integerp n))
           (and (<= (abs (- (fla-rv k a) a)) (abs (- (* n (fla-ulp k a)) a)))
                (<= (abs (- (fla-rv k a) a)) (/ (fla-ulp k a) 2))
                (implies (equal (abs (- (fla-rv k a) a)) (/ (fla-ulp k a) 2))
                         (evenp (/ (fla-rv k a) (fla-ulp k a))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne abs evenp fla-ulp)
                  :use ((:instance rvu-nearest (u (fla-ulp k a))))))))

;; ---- monotone (the argument of fintr.lisp's fl-rv-mono) ---------------------

(local (defthm fla-rv-rational (rationalp (fla-rv k a)) :rule-classes :type-prescription))
(local (defthm fla-rv-nonneg
  (implies (and (rationalp a) (< 0 a)) (<= 0 (fla-rv k a)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable rne flog2)))))

(local (defthm rvu-mono
  (implies (and (rationalp a) (rationalp b) (rationalp u) (< 0 u) (<= a b))
           (<= (* (rne (/ a u)) u) (* (rne (/ b u)) u)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne) :nonlinearp t :use ((:instance rne-mono (a (/ a u)) (b (/ b u))))))))

(local (defthm rvu-le
  (implies (and (rationalp a) (rationalp u) (< 0 u) (integerp n) (<= a (* n u))) (<= (* (rne (/ a u)) u) (* n u)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne) :nonlinearp t :use ((:instance rne-mono (a (/ a u)) (b n)))))))

(local (defthm rvu-ge
  (implies (and (rationalp a) (rationalp u) (< 0 u) (integerp n) (<= (* n u) a)) (<= (* n u) (* (rne (/ a u)) u)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne) :nonlinearp t :use ((:instance rne-mono (b (/ a u)) (a n)))))))

(local (defthm expt-chain
  (implies (and (integerp i) (integerp j) (< i j) (rationalp x) (rationalp y)
                (<= x (expt 2 (+ 1 i))) (<= (expt 2 j) y))
           (<= x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance expt2-le (j (+ 1 i)) (i j)))))))

(local (defthm fla-ulp-same
  (implies (equal (fla-ex k a) (fla-ex k b)) (equal (fla-ulp k b) (fla-ulp k a)))
  :rule-classes nil))

(local (defthm fla-ex-cases (or (equal (fla-ex k a) (flog2 a)) (equal (fla-ex k a) (fl-emin k))) :rule-classes nil))

(local (defthm fla-ex-bounds
  (implies (and (rationalp a) (< 0 a))
           (and (< a (expt 2 (+ 1 (fla-ex k a))))
                (implies (< (fl-emin k) (fla-ex k a)) (<= (expt 2 (fla-ex k a)) a))
                (implies (< (fl-emin k) (fla-ex k a)) (equal (fla-ex k a) (flog2 a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fla-ex-int fla-flog2-int fl-params) (theory 'minimal-theory))
                  :use ((:instance expt2-le (j (+ 1 (flog2 a))) (i (+ 1 (fla-ex k a))))
                                                  fla-flog2-bounds fla-ex-ge
                                                  fla-ex-cases
                                                  )))))

(local (defthm fla-rv-mono
  (implies (and (rationalp a) (rationalp b) (< 0 a) (<= a b))
           (<= (fla-rv k a) (fla-rv k b)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fl-prec fl-emin fl-emax) (fla-ulp fla-ex flog2 rne))
                  :cases ((equal (fla-ex k a) (fla-ex k b))))
          ("Subgoal 1" :use ((:instance rvu-mono (u (fla-ulp k a))) fla-ulp-same))
          ("Subgoal 2" :in-theory (e/d (fla-ulp fl-prec fl-emin fl-emax) (fla-ex flog2 rne))
                       :use ((:instance fla-ex-bounds (a a)) (:instance fla-ex-bounds (a b))
                             (:instance rvu-le (u (fla-ulp k a)) (n (expt 2 (fl-prec k))))
                             (:instance rvu-ge (a b) (u (fla-ulp k b)) (n (expt 2 (- (fl-prec k) 1))))
                             (:instance fla-flog2-bounds (a a)) (:instance fla-flog2-bounds (a b))
                             (:instance expt-chain (x (fla-rv k a)) (y (fla-rv k b)) (i (fla-ex k a)) (j (fla-ex k b)))
                             (:instance expt2-le (j (+ 1 (flog2 a))) (i (+ 1 (fla-ex k a))))
                             (:instance (:theorem (implies (and (integerp x) (integerp y) (< x y) (equal y (max z w)) (< x (max (flog2 b) w)) (<= w x)) (equal y z)))
                                        (x (fla-ex k a)) (y (fla-ex k b)) (z (flog2 b)) (w (fl-emin k))))))))

(local (in-theory (disable fla-rv fla-ulp fla-ex)))

(local (defthm fl-round-negative
  (implies (and (rationalp q) (< q 0))
           (equal (fl-round k q) (fl-neg (fl-round k (- q)))))
  :hints (("Goal" :in-theory (disable fl-round fl-round-pos) :use ((:instance fl-round-neg (q (- q))))))))

(local (defthm fl-round-sign
  (implies (rationalp q)
           (and (implies (<= 0 q) (or (equal (fl-round k q) :pinf)
                                      (and (rationalp (fl-round k q)) (<= 0 (fl-round k q)))))
                (implies (<= q 0) (or (equal (fl-round k q) :ninf) (equal (fl-round k q) :nzero)
                                      (and (rationalp (fl-round k q)) (<= (fl-round k q) 0))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fl-round fl-round-neg) :cases ((< 0 q) (< q 0)))))) 

(defthm fl-round-mono
  (implies (and (rationalp a) (rationalp b) (<= a b))
           (not (fl-less (fl-round k b) (fl-round k a))))
  :hints (("Goal" :in-theory (disable fl-round fl-round-neg)
                  :use ((:instance fl-round-sign (q a)) (:instance fl-round-sign (q b)))
                  :cases ((and (< 0 a) (< 0 b)) (and (< a 0) (< b 0)) (and (<= a 0) (<= 0 b))))
          ("Subgoal 2" :use ((:instance fla-rv-mono (a (- b)) (b (- a)))))))

;; ---- the exponent, the ulp, and representable values -------------------------

(local (defthm fla-ex-normal
  (implies (and (rationalp a) (< 0 a) (<= (expt 2 (fl-emin k)) a)) (equal (fla-ex k a) (flog2 a)))
  :hints (("Goal" :in-theory (e/d (fla-ex) (flog2)) :use ((:instance expt-sandwich (i (fl-emin k)) (j (flog2 a)) (x a)) fla-flog2-bounds)))))

(local (defthm fla-ex-sub
  (implies (and (rationalp a) (< 0 a) (< a (expt 2 (fl-emin k)))) (equal (fla-ex k a) (fl-emin k)))
  :hints (("Goal" :in-theory (e/d (fla-ex) (flog2)) :use ((:instance expt-sandwich (i (flog2 a)) (j (- (fl-emin k) 1)) (x a)) fla-flog2-bounds)))))

(local (defthm fla-ex-le          ; below 2^(j+1), j >= emin: the exponent is at most j
  (implies (and (rationalp v) (< 0 v) (integerp j) (<= (fl-emin k) j) (< v (expt 2 (+ 1 j))))
           (<= (fla-ex k v) j))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fla-ex) (flog2)) :use ((:instance expt-sandwich (i (flog2 v)) (j j) (x v)) (:instance fla-flog2-bounds (a v)))))))

(local (defthm fla-ex-pow
  (implies (and (integerp j) (<= (fl-emin k) j)) (equal (fla-ex k (expt 2 j)) j))
  :hints (("Goal" :in-theory (e/d (fla-ex) (flog2)) :use ((:instance flog2-unique (a (expt 2 j)) (i j)))))))

(local (defthm int-scale
  (implies (and (integerp n) (integerp d) (<= 0 d)) (integerp (* n (expt 2 d))))
  :rule-classes nil))

(local (defthm ulp-ratio
  (implies (and (rationalp x) (< 0 x) (rationalp y) (< 0 y))
           (equal (/ (fla-ulp k y) (fla-ulp k x)) (expt 2 (- (fla-ex k y) (fla-ex k x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fla-ulp)))))

(local (defthm ulp-multiple       ; a multiple of a coarser ulp is a multiple of a finer one
  (implies (and (rationalp x) (< 0 x) (rationalp y) (< 0 y) (<= (fla-ex k x) (fla-ex k y))
                (integerp (/ z (fla-ulp k y))))
           (integerp (/ z (fla-ulp k x))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fla-ulp)
                  :use (ulp-ratio (:instance int-scale (n (/ z (fla-ulp k y))) (d (- (fla-ex k y) (fla-ex k x)))))))))

(local (defthm fla-rv-fixes
  (implies (and (rationalp x) (< 0 x) (integerp (/ x (fla-ulp k x)))) (equal (fla-rv k x) x))
  :hints (("Goal" :in-theory (enable fla-rv)))))

(local (defthm fla-rv-int (implies (rationalp a) (integerp (/ (fla-rv k a) (fla-ulp k a))))
  :hints (("Goal" :in-theory (enable fla-rv)))))

(local (defthm expt2-int (implies (and (integerp n) (<= 0 n)) (integerp (expt 2 n))) :rule-classes nil))

(local (defthm ulp-bot
  (equal (* (expt 2 (- (fl-prec k) 1)) (fla-ulp k a)) (expt 2 (fla-ex k a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fla-ulp)))))

(local (defthm ulp-top
  (equal (* (expt 2 (fl-prec k)) (fla-ulp k a)) (expt 2 (+ 1 (fla-ex k a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fla-ulp)))))

(local (defthm fla-rv-le-top      ; v <= 2^(ea+1)
  (implies (and (rationalp a) (< 0 a)) (<= (fla-rv k a) (expt 2 (+ 1 (fla-ex k a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fla-rv fla-ulp-pos fla-ulp-rat fl-params) (theory 'minimal-theory))
                  :use (fla-ex-bounds ulp-top (:instance rvu-le (u (fla-ulp k a)) (n (expt 2 (fl-prec k))))
                        (:instance expt2-int (n (fl-prec k))))))))

(local (defthm fla-rv-repr
  (implies (and (rationalp a) (< 0 a) (< 0 (fla-rv k a)))
           (integerp (/ (fla-rv k a) (fla-ulp k (fla-rv k a)))))
  :hints (("Goal" :cases ((< (fla-rv k a) (expt 2 (+ 1 (fla-ex k a)))))
                  :use (fla-rv-le-top))
          ("Subgoal 2" :in-theory (enable fla-ulp))
          ("Subgoal 1" :use ((:instance fla-ex-le (v (fla-rv k a)) (j (fla-ex k a)))
                             (:instance ulp-multiple (x (fla-rv k a)) (y a) (z (fla-rv k a))))))))

;; ---- nearest ---------------------------------------------------------------

(local (defthm nearest-nonpos
  (implies (and (rationalp a) (< 0 a) (rationalp y) (<= y 0))
           (<= (abs (- (fla-rv k a) a)) (abs (- y a))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fla-rv-nearest (n 0)))))))

(local (defthm nearest-coarser
  (implies (and (rationalp a) (< 0 a) (rationalp y) (< 0 y) (<= (fla-ex k a) (fla-ex k y))
                (integerp (/ y (fla-ulp k y))))
           (<= (abs (- (fla-rv k a) a)) (abs (- y a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs)
                  :use ((:instance fla-rv-nearest (n (/ y (fla-ulp k a))))
                        (:instance ulp-multiple (x a) (y y) (z y)))))))

(local (defthm y-below
  (implies (and (rationalp a) (< 0 a) (rationalp y) (< 0 y) (< (fla-ex k y) (fla-ex k a)))
           (< y (expt 2 (fla-ex k a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fla-ex-int) (theory 'minimal-theory))
                  :use ((:instance fla-ex-bounds (a y))
                        (:instance expt2-le (j (+ 1 (fla-ex k y))) (i (fla-ex k a))))))))

(local (defthm nearest-finer
  (implies (and (rationalp a) (< 0 a) (rationalp y) (< 0 y) (< (fla-ex k y) (fla-ex k a)))
           (<= (abs (- (fla-rv k a) a)) (abs (- y a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable flog2 fla-ulp)
                  :use ((:instance fla-rv-nearest (n (expt 2 (- (fl-prec k) 1)))) ulp-bot
                        fla-ex-bounds y-below)))))

(local (defthm fla-rv-nearest-repr
  (implies (and (rationalp a) (< 0 a) (fl-repr-p k y))
           (<= (abs (- (fla-rv k a) a)) (abs (- y a))))
  :hints (("Goal" :use (nearest-nonpos nearest-coarser nearest-finer)))))

;; ---- error, representability and overflow on a > 0 ----------------------------

(local (defthm ulp-half
  (equal (* 1/2 (fla-ulp k a)) (* (expt 2 (- (fl-prec k))) (expt 2 (fla-ex k a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fla-ulp)))))

(local (defthm expt2-type (and (rationalp (expt 2 i)) (< 0 (expt 2 i))) :rule-classes :type-prescription))

(local (defthm fla-rv-half
  (implies (and (rationalp a) (< 0 a)) (<= (abs (- (fla-rv k a) a)) (* 1/2 (fla-ulp k a))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fla-rv-nearest (n 0)))))))

(local (defthm fla-rv-rel
  (implies (and (rationalp a) (< 0 a) (<= (expt 2 (fl-emin k)) a))
           (<= (abs (- (fla-rv k a) a)) (* (expt 2 (- (fl-prec k))) a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fla-ex-normal expt2-type abs-rational fla-rv-rational) (theory 'minimal-theory))
                  :use (fla-rv-half ulp-half fla-flog2-bounds
                        (:instance mul-le (u (expt 2 (- (fl-prec k)))) (x (expt 2 (flog2 a))) (y a)))))))

(local (defthm fla-rv-sub
  (implies (and (rationalp a) (< 0 a) (< a (expt 2 (fl-emin k))))
           (<= (abs (- (fla-rv k a) a)) (expt 2 (- (fl-emin k) (fl-prec k)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable abs) :use (fla-rv-half ulp-half fla-ex-sub)))))

(local (defthm huge-facts
  (and (equal (fl-huge k) (* (- (expt 2 (fl-prec k)) 1) (expt 2 (- (fl-emax k) (- (fl-prec k) 1)))))
       (< (fl-huge k) (expt 2 (+ 1 (fl-emax k))))
       (< (fl-emin k) (fl-emax k))
       (< (expt 2 (fl-emin k)) (fl-huge k)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fl-prec fl-emin fl-emax)))))

(local (defthm huge-ulp
  (implies (equal (fla-ex k a) (fl-emax k))
           (equal (* (- (expt 2 (fl-prec k)) 1) (fla-ulp k a)) (fl-huge k)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fla-ulp) (fl-huge)) :use huge-facts))))

(local (defthm fla-rv-top-case
  (implies (and (rationalp a) (< 0 a) (<= a (fl-huge k)) (equal (fla-ex k a) (fl-emax k)))
           (<= (fla-rv k a) (fl-huge k)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fla-rv fla-ulp-pos fla-ulp-rat fl-params) (theory 'minimal-theory))
                  :use (huge-ulp (:instance rvu-le (u (fla-ulp k a)) (n (- (expt 2 (fl-prec k)) 1)))
                        (:instance expt2-int (n (fl-prec k))))))))

(local (defthm expt2-lt (implies (integerp i) (< (expt 2 i) (expt 2 (+ 1 i)))) :rule-classes nil))

(local (defthm fla-rv-below-huge
  (implies (and (rationalp a) (< 0 a) (<= a (fl-huge k)))
           (< (fla-rv k a) (expt 2 (+ 1 (fl-emax k)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fla-ex-int fl-params) (theory 'minimal-theory))
                  :use (huge-facts fla-rv-le-top fla-rv-top-case
                        (:instance fla-ex-le (v a) (j (fl-emax k)))
                        (:instance expt2-le (j (+ 1 (fla-ex k a))) (i (fl-emax k)))
                        (:instance expt2-lt (i (fl-emax k)))
                        (:instance expt2-type (i (fl-emax k))))))))

;; ---- S1: fl-round ------------------------------------------------------------

(local (defthm repr-neg (implies (fl-repr-p k y) (fl-repr-p k (- y)))))

(local (defthm fla-rv-repr-p
  (implies (and (rationalp a) (< 0 a) (< (fla-rv k a) (expt 2 (+ 1 (fl-emax k)))))
           (fl-repr-p k (fla-rv k a)))
  :hints (("Goal" :use fla-rv-repr))))

(local (defthm repr-rational (implies (fl-repr-p k y) (rationalp y)) :rule-classes :forward-chaining))
(local (defthm repr-zero (fl-repr-p k 0)))

(local (in-theory (disable fl-repr-p fl-round fl-round-neg fla-rv-repr)))

(local (defthm fl-neg-rat (implies (and (rationalp x) (not (= x 0))) (equal (fl-neg x) (- x)))))
(local (defthm fl-neg-zero (equal (fl-neg 0) :nzero)))

(defthm fl-round-repr                ; representable values are fixed
  (implies (fl-repr-p k x) (equal (fl-round k x) x))
  :hints (("Goal" :cases ((< 0 x) (< x 0) (= x 0))
                  :use ((:instance repr-neg (y x))
                        (:instance fla-rv-fixes (x x)) (:instance fla-rv-fixes (x (- x))))
                  :in-theory (enable fl-repr-p))))

(defthm fl-round-repr-p              ; a finite result is representable
  (implies (and (rationalp q) (fl-fin-p (fl-round k q)))
           (fl-repr-p k (fl-val (fl-round k q))))
  :hints (("Goal" :cases ((< 0 q) (< q 0))
                  :use ((:instance fla-rv-repr-p (a (- q))) (:instance fla-rv-repr-p (a q))
                        (:instance repr-neg (y (fla-rv k (- q))))
                        (:instance fl-repr-p (x 0))))))

(defthm fl-round-idem
  (implies (and (rationalp q) (rationalp (fl-round k q)))
           (equal (fl-round k (fl-round k q)) (fl-round k q)))
  :hints (("Goal" :in-theory (disable fl-round-repr-p fl-round-repr)
                  :use (fl-round-repr-p (:instance fl-round-repr (x (fl-round k q)))))))

(defthm fl-round-nearest             ; no representable value is nearer to q
  (implies (and (rationalp q) (fl-repr-p k y) (fl-fin-p (fl-round k q)))
           (<= (abs (- (fl-val (fl-round k q)) q)) (abs (- y q))))
  :hints (("Goal" :cases ((< 0 q) (< q 0))
                  :use ((:instance fla-rv-nearest-repr (a q)) (:instance fla-rv-nearest-repr (a (- q)) (y (- y)))))))

(defthm fl-round-half-ulp
  (implies (and (rationalp q) (fl-fin-p (fl-round k q)))
           (<= (abs (- (fl-val (fl-round k q)) q)) (* 1/2 (fl-ulp-of k q))))
  :hints (("Goal" :cases ((< 0 q) (< q 0))
                  :use ((:instance fla-rv-half (a q)) (:instance fla-rv-half (a (- q)))))))

(local (defthm evenp-neg (implies (and (rationalp x) (evenp x)) (evenp (- x)))))

(defthm fl-round-even                ; a tie goes to the even multiple of the ulp
  (implies (and (rationalp q) (fl-fin-p (fl-round k q))
                (equal (abs (- (fl-val (fl-round k q)) q)) (* 1/2 (fl-ulp-of k q))))
           (evenp (/ (fl-val (fl-round k q)) (fl-ulp-of k q))))
  :hints (("Goal" :cases ((< 0 q) (< q 0))
                  :in-theory (disable evenp)
                  :use ((:instance fla-rv-nearest (a q) (n 0)) (:instance fla-rv-nearest (a (- q)) (n 0))))))

(defthm fl-round-finite              ; no overflow up to HUGE
  (implies (and (rationalp q) (<= (abs q) (fl-huge k)))
           (fl-fin-p (fl-round k q)))
  :hints (("Goal" :cases ((< 0 q) (< q 0))
                  :in-theory (disable fl-huge)
                  :use ((:instance fla-rv-below-huge (a q)) (:instance fla-rv-below-huge (a (- q)))))))

(defthm fl-round-rel-err             ; normal range: |error| <= 2^-p |q|
  (implies (and (rationalp q) (<= (expt 2 (fl-emin k)) (abs q)) (fl-fin-p (fl-round k q)))
           (<= (abs (- (fl-val (fl-round k q)) q)) (* (expt 2 (- (fl-prec k))) (abs q))))
  :hints (("Goal" :cases ((< 0 q) (< q 0))
                  :use ((:instance fla-rv-rel (a q)) (:instance fla-rv-rel (a (- q)))))))

(defthm fl-round-sub-err             ; below 2^emin: |error| <= 2^(emin-p), half the least subnormal
  (implies (and (rationalp q) (< (abs q) (expt 2 (fl-emin k))))
           (<= (abs (- (fl-val (fl-round k q)) q)) (expt 2 (- (fl-emin k) (fl-prec k)))))
  :hints (("Goal" :cases ((< 0 q) (< q 0))
                  :in-theory (disable fl-huge)
                  :use (huge-facts fl-round-finite (:instance fla-rv-sub (a q)) (:instance fla-rv-sub (a (- q)))))))

(defthm fl-round-err
  (implies (and (rationalp q) (fl-fin-p (fl-round k q)))
           (<= (abs (- (fl-val (fl-round k q)) q)) (fl-err-bound k q)))
  :hints (("Goal" :in-theory (disable fl-round-rel-err fl-round-sub-err abs)
                  :use (fl-round-rel-err fl-round-sub-err))))

;; ---- S2: one rounding per operation --------------------------------------------
; For finite operands each operation's result is fl-round of the exact value
; (fl-OP-round: same finiteness, same number; a zero result's sign aside), so
; fl-round's facts carry over: fl-OP-err (within fl-err-bound of the exact
; value), fl-OP-nearest (no representable value nearer), fl-OP-exact (an exact
; value that is representable comes back unchanged).

(local (defthm fl-fin-val (implies (fl-fin-p x) (rationalp (fl-val x))) :rule-classes :type-prescription))

(defthm fl-add-round
  (implies (and (fl-fin-p a) (fl-fin-p b))
           (and (equal (fl-fin-p (fl-add k a b)) (fl-fin-p (fl-round k (+ (fl-val a) (fl-val b)))))
                (equal (fl-val (fl-add k a b)) (fl-val (fl-round k (+ (fl-val a) (fl-val b)))))))
  :hints (("Goal" :in-theory (enable fl-round))))

(defthm fl-sub-round
  (implies (and (fl-fin-p a) (fl-fin-p b))
           (and (equal (fl-fin-p (fl-sub k a b)) (fl-fin-p (fl-round k (- (fl-val a) (fl-val b)))))
                (equal (fl-val (fl-sub k a b)) (fl-val (fl-round k (- (fl-val a) (fl-val b)))))))
  :hints (("Goal" :in-theory (e/d (fl-round) (fl-add)) :use ((:instance fl-add-round (b (fl-neg b)))))))

(defthm fl-mul-round
  (implies (and (fl-fin-p a) (fl-fin-p b))
           (and (equal (fl-fin-p (fl-mul k a b)) (fl-fin-p (fl-round k (* (fl-val a) (fl-val b)))))
                (equal (fl-val (fl-mul k a b)) (fl-val (fl-round k (* (fl-val a) (fl-val b)))))))
  :hints (("Goal" :in-theory (enable fl-round))))

(defthm fl-div-round
  (implies (and (fl-fin-p a) (fl-fin-p b) (not (fl-zero-p b)))
           (and (equal (fl-fin-p (fl-div k a b)) (fl-fin-p (fl-round k (/ (fl-val a) (fl-val b)))))
                (equal (fl-val (fl-div k a b)) (fl-val (fl-round k (/ (fl-val a) (fl-val b)))))))
  :hints (("Goal" :in-theory (enable fl-round))))

(defthm fl-conv-round
  (implies (rationalp x) (equal (fl-conv k x) (fl-round k x))))

(local (in-theory (disable fl-add fl-sub fl-mul fl-div fl-conv fl-err-bound)))

(defun op-name (op s) (declare (xargs :guard (and (symbolp op) (stringp s)))) (intern-in-package-of-symbol (concatenate 'string (symbol-name op) s) 'fl-round))

(defmacro def-op-acc (op hyps term q)
  `(progn
     (defthm ,(op-name op "-ERR")
       (implies (and ,@hyps (fl-fin-p ,term)) (<= (abs (- (fl-val ,term) ,q)) (fl-err-bound k ,q)))
       :hints (("Goal" :use ((:instance fl-round-err (q ,q))))))
     (defthm ,(op-name op "-NEAREST")
       (implies (and ,@hyps (fl-repr-p k y) (fl-fin-p ,term)) (<= (abs (- (fl-val ,term) ,q)) (abs (- y ,q))))
       :hints (("Goal" :use ((:instance fl-round-nearest (q ,q))))))
     (defthm ,(op-name op "-EXACT")
       (implies (and ,@hyps (fl-repr-p k ,q)) (equal (fl-val ,term) ,q))
       :hints (("Goal" :use ((:instance fl-round-repr (x ,q))))))))

(def-op-acc fl-add ((fl-fin-p a) (fl-fin-p b)) (fl-add k a b) (+ (fl-val a) (fl-val b)))
(def-op-acc fl-sub ((fl-fin-p a) (fl-fin-p b)) (fl-sub k a b) (- (fl-val a) (fl-val b)))
(def-op-acc fl-mul ((fl-fin-p a) (fl-fin-p b)) (fl-mul k a b) (* (fl-val a) (fl-val b)))
(def-op-acc fl-div ((fl-fin-p a) (fl-fin-p b) (not (fl-zero-p b))) (fl-div k a b) (/ (fl-val a) (fl-val b)))
(def-op-acc fl-conv ((rationalp x)) (fl-conv k x) x)

;; ---- Sterbenz: b/2 <= a <= 2b makes a - b representable, so fl-sub is exact ----

(local (defthm sterb-pos
  (implies (and (fl-repr-p k a) (fl-repr-p k b) (< 0 b) (< b a) (<= a (* 2 b)))
           (fl-repr-p k (- a b)))
  :hints (("Goal" :in-theory (enable fl-repr-p)
                  :use ((:instance ulp-multiple (x b) (y a) (z a))
                        (:instance ulp-multiple (x (- a b)) (y b) (z (- a b)))
                        (:instance fla-ex-mono (a b) (b a))
                        (:instance fla-ex-mono (a (- a b)) (b b)))))))

(defthm fl-sterbenz
  (implies (and (fl-repr-p k a) (fl-repr-p k b) (<= (/ b 2) a) (<= a (* 2 b)))
           (fl-repr-p k (- a b)))
  :hints (("Goal" :cases ((< b a) (< a b))
                  :use (sterb-pos (:instance sterb-pos (a b) (b a)) (:instance repr-neg (y (- b a)))))))

(defthm fl-sub-sterbenz
  (implies (and (fl-repr-p k a) (fl-repr-p k b) (<= (/ b 2) a) (<= a (* 2 b)))
           (equal (fl-val (fl-sub k a b)) (- a b)))
  :hints (("Goal" :in-theory (enable fl-repr-p) :use (fl-sterbenz (:instance fl-sub-exact)))))
