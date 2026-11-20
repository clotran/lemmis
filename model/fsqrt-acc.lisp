; fsqrt-acc: SQRT (freal.lisp fl-sqrt) is fl-round of a rational z that
; encloses the true root: the integer square root is exact (isqrt-correct),
; z*z = x when the root is exact, and otherwise z is the midpoint of an
; interval of width 2^-j that holds sqrt(x) strictly inside.

(in-package "ACL2")
(include-book "freal-acc")
(local (include-book "arithmetic-5/top" :dir :system))

;; ---- the integer square root -------------------------------------------------

(local (defthm isqrt-aux-inv
  (implies (and (natp n) (natp i) (natp r) (<= (* r r) n) (< n (* (+ r (expt 2 i)) (+ r (expt 2 i)))))
           (and (natp (isqrt-aux n i r))
                (<= (* (isqrt-aux n i r) (isqrt-aux n i r)) n)
                (< n (* (+ 1 (isqrt-aux n i r)) (+ 1 (isqrt-aux n i r))))))
  :hints (("Goal" :induct (isqrt-aux n i r) :in-theory (enable isqrt-aux))
          ("Subgoal *1/2" :nonlinearp t))))

(local (defthm ilen-top
  (implies (natp n) (< n (expt 2 (integer-length n))))
  :rule-classes :linear))

(local (defthm bits-ge (implies (natp n) (<= (integer-length n) (* 2 (isqrt-bits n)))) :rule-classes nil))
(local (defthm expt-dbl (implies (integerp b) (equal (* (expt 2 b) (expt 2 b)) (expt 2 (* 2 b)))) :rule-classes nil))
(local (defthm expt2-dbl (implies (integerp b) (equal (expt 2 (* 2 b)) (* (expt 2 b) (expt 2 b)))) :rule-classes nil))
(local (defthm expt2-int (implies (and (integerp n) (<= 0 n)) (integerp (expt 2 n))) :rule-classes nil))
(local (defthm expt2-le (implies (and (integerp a) (integerp b) (<= a b)) (<= (expt 2 a) (expt 2 b))) :rule-classes nil))

(local (defthm bits-int (and (integerp (isqrt-bits n)) (integerp (integer-length n))) :rule-classes nil))

(local (defthm isqrt-start
  (implies (natp n) (< n (* (expt 2 (isqrt-bits n)) (expt 2 (isqrt-bits n)))))
  :hints (("Goal" :in-theory (union-theories '(natp) (theory 'minimal-theory))
                  :use (ilen-top bits-ge (:instance expt-dbl (b (isqrt-bits n)))
                        (:instance expt2-le (a (integer-length n)) (b (* 2 (isqrt-bits n))))
                        bits-int)))))

(local (defthm bits-nat (and (integerp (isqrt-bits n)) (< 0 (isqrt-bits n))) :rule-classes :type-prescription))

(defthm isqrt-correct          ; s = floor(sqrt n)
  (implies (natp n)
           (and (natp (fl-isqrt n))
                (<= (* (fl-isqrt n) (fl-isqrt n)) n)
                (< n (* (+ 1 (fl-isqrt n)) (+ 1 (fl-isqrt n))))))
  :hints (("Goal" :in-theory (disable isqrt-aux-inv isqrt-bits isqrt-start)
                  :use (isqrt-start (:instance isqrt-aux-inv (i (isqrt-bits n)) (r 0))))))

;; ---- fl-sqrt's pieces ------------------------------------------------------------

(defun fl-sqrt-j (k x) (declare (xargs :guard (and (rationalp x) (< 0 x)))) (- (+ (fl-prec k) 3) (floor (flog2 x) 2)))
(defun fl-sqrt-s (k x)
  (declare (xargs :guard (and (rationalp x) (< 0 x))))
  (fl-isqrt (floor (* x (expt 4 (fl-sqrt-j k x))) 1)))
(defun fl-sqrt-exact (k x)
  (declare (xargs :guard (and (rationalp x) (< 0 x))))
  (let ((y (* x (expt 4 (fl-sqrt-j k x)))) (s (fl-sqrt-s k x))) (and (integerp y) (= (* s s) y))))

(defthm fl-sqrt-unfold
  (implies (and (rationalp x) (< 0 x))
           (equal (fl-sqrt k x)
                  (fl-round k (/ (if (fl-sqrt-exact k x) (fl-sqrt-s k x) (+ (fl-sqrt-s k x) 1/2))
                                 (expt 2 (fl-sqrt-j k x))))))
  :hints (("Goal" :in-theory (disable fl-round fl-isqrt flog2))))

(local (defthm fl-params
  (and (integerp (fl-prec k)) (<= 2 (fl-prec k)))
  :rule-classes ((:type-prescription :corollary (integerp (fl-prec k)))
                 (:linear :corollary (<= 2 (fl-prec k))))))

(local (defthm sqrt-j-int (integerp (fl-sqrt-j k x)) :rule-classes :type-prescription))

(local (defthm sq-s-bounds
  (implies (and (rationalp x) (< 0 x))
           (let ((y (* x (expt 4 (fl-sqrt-j k x)))) (s (fl-sqrt-s k x)))
             (and (natp s) (<= (* s s) y) (< y (* (+ s 1) (+ s 1)))
                  (implies (not (fl-sqrt-exact k x)) (< (* s s) y))
                  (implies (fl-sqrt-exact k x) (equal (* s s) y)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable isqrt-correct fl-isqrt fl-sqrt-j)
                  :use ((:instance isqrt-correct (n (floor (* x (expt 4 (fl-sqrt-j k x))) 1))))))))

(local (defthm floor-half (implies (integerp e) (<= (* 2 (floor e 2)) e)) :rule-classes :linear))

(local (defthm y-big-aux
  (implies (and (rationalp x) (<= (expt 2 e) x) (integerp e) (integerp p) (integerp j) (equal j (- (+ p 3) (floor e 2))))
           (<= (expt 2 (* 2 (+ p 3))) (* x (expt 4 j))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t
                  :use ((:instance expt2-le (a (* 2 (+ p 3))) (b (+ e (* 2 j)))))))))

(local (defthm y-big
  (implies (and (rationalp x) (< 0 x))
           (<= (expt 2 (* 2 (+ (fl-prec k) 3))) (* x (expt 4 (fl-sqrt-j k x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable flog2)
                  :use ((:instance y-big-aux (e (flog2 x)) (p (fl-prec k)) (j (fl-sqrt-j k x))))))))

(local (defthm sq-lt
  (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= 0 b) (< (* b b) (* a a))) (< b a))
  :rule-classes nil :hints (("Goal" :nonlinearp t))))

(local (defthm sq-s-big
  (implies (and (rationalp x) (< 0 x)) (<= (expt 2 (+ (fl-prec k) 3)) (fl-sqrt-s k x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fl-sqrt-s fl-sqrt-j fl-sqrt-exact flog2)
                  :use (y-big sq-s-bounds
                        (:instance sq-lt (a (+ 1 (fl-sqrt-s k x))) (b (expt 2 (+ (fl-prec k) 3))))
                        (:instance expt2-dbl (b (+ (fl-prec k) 3))))))))

;; ---- every rational strictly between s/2^j and (s+1)/2^j rounds alike ----------

(local (defthm flog2-ge
  (implies (and (rationalp z) (< 0 z) (integerp i) (<= (expt 2 i) z)) (<= i (flog2 z)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fla-flog2-int) (theory 'minimal-theory))
                  :use ((:instance fla-flog2-bounds (a z)) (:instance expt2-le (a (+ 1 (flog2 z))) (b i)))))))

(local (defthm flog2-le
  (implies (and (rationalp z) (< 0 z) (integerp i) (< z (expt 2 (+ 1 i)))) (<= (flog2 z) i))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fla-flog2-int) (theory 'minimal-theory))
                  :use ((:instance fla-flog2-bounds (a z)) (:instance expt2-le (a (+ 1 i)) (b (flog2 z))))))))

(local (defthm int-side
  (implies (and (integerp s) (integerp pp) (rationalp t1) (rationalp t2)
                (< s t1) (< t1 (+ s 1)) (< s t2) (< t2 (+ s 1)))
           (and (iff (<= pp t1) (<= pp t2)) (iff (< t1 pp) (< t2 pp))))
  :rule-classes nil
  :hints (("Goal" :cases ((<= pp s))))))

(local (defthm scale-lt
  (implies (and (rationalp z) (integerp i) (integerp j)) (iff (< z (expt 2 i)) (< (* z (expt 2 j)) (expt 2 (+ i j)))))
  :rule-classes nil))
(local (defthm scale-le
  (implies (and (rationalp z) (integerp i) (integerp j)) (iff (<= (expt 2 i) z) (<= (expt 2 (+ i j)) (* z (expt 2 j)))))
  :rule-classes nil))

(defmacro in-gap (q s j) (list 'and (list 'rationalp q) (list '< s (list '* q (list 'expt 2 j))) (list '< (list '* q (list 'expt 2 j)) (list '+ s 1))))

(local (defthm gap-ex-big        ; the exponent of a value in the gap is at least p + 3 - j
  (implies (and (integerp s) (integerp j) (<= (expt 2 (+ (fl-prec k) 3)) s) (in-gap z s j))
           (and (< 0 z) (<= (- (+ (fl-prec k) 3) j) (flog2 z)) (<= (- (+ (fl-prec k) 3) j) (fla-ex k z))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable flog2)
                  :use ((:instance flog2-ge (i (- (+ (fl-prec k) 3) j)))
                        (:instance scale-le (z z) (i (- (+ (fl-prec k) 3) j)) (j j)))))))

(local (defthm gap-ex-le
  (implies (and (integerp s) (integerp j) (<= (expt 2 (+ (fl-prec k) 3)) s) (in-gap z s j) (in-gap q s j))
           (<= (fla-ex k q) (fla-ex k z)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable flog2)
                  :use (gap-ex-big (:instance gap-ex-big (z q))
                        (:instance flog2-le (z z) (i (flog2 z)))
                        (:instance flog2-le (z q) (i (fla-ex k z)))
                        (:instance expt2-le (a (+ 1 (flog2 z))) (b (+ 1 (fla-ex k z))))
                        (:instance scale-lt (z z) (i (+ 1 (fla-ex k z))) (j j))
                        (:instance scale-lt (z q) (i (+ 1 (fla-ex k z))) (j j))
                        (:instance expt2-int (n (+ 1 (fla-ex k z) j)))
                        (:instance int-side (pp (expt 2 (+ 1 (fla-ex k z) j))) (t1 (* z (expt 2 j))) (t2 (* q (expt 2 j)))))))))

(local (defthm floor-unique
  (implies (and (rationalp x) (integerp n) (<= n x) (< x (+ n 1))) (equal (floor x 1) n))
  :rule-classes nil))

(local (defthm half-int
  (implies (and (rationalp m) (integerp f))
           (and (implies (equal (- m f) 1/2) (integerp (* 2 m)))
                (integerp (* 2 f)) (integerp (+ 1 (* 2 f)))
                (iff (< (- m f) 1/2) (< (* 2 m) (+ 1 (* 2 f))))
                (iff (<= f m) (<= (* 2 f) (* 2 m)))
                (iff (< m (+ f 1)) (< (* 2 m) (+ 2 (* 2 f))))
                (rationalp (* 2 m))))
  :rule-classes nil))

(local (defthm two-m-aux
  (implies (and (rationalp m) (integerp f) (<= f m) (< m (+ f 1)) (not (integerp (* 2 m))))
           (and (not (equal (- m f) 1/2))
                (equal (floor (* 2 m) 1) (if (< (- m f) 1/2) (* 2 f) (+ 1 (* 2 f))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :cases ((< (- m f) 1/2))
                  :use (half-int (:instance floor-unique (x (* 2 m)) (n (* 2 f)))
                        (:instance floor-unique (x (* 2 m)) (n (+ 1 (* 2 f)))))))))

(local (defthm floor-bnds
  (implies (rationalp m) (and (integerp (floor m 1)) (<= (floor m 1) m) (< m (+ 1 (floor m 1)))))
  :rule-classes nil))

(local (defthm two-m
  (implies (and (rationalp m) (not (integerp (* 2 m))))
           (and (not (equal (- m (floor m 1)) 1/2))
                (equal (floor (* 2 m) 1)
                       (if (< (- m (floor m 1)) 1/2) (* 2 (floor m 1)) (+ 1 (* 2 (floor m 1)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (floor-bnds (:instance two-m-aux (f (floor m 1))))))))

(local (defthm parity (implies (and (integerp a) (integerp b)) (not (equal (* 2 a) (+ 1 (* 2 b))))) :rule-classes nil))

(local (defthm rne-by-half
  (implies (and (rationalp m1) (rationalp m2) (equal (floor (* 2 m1) 1) (floor (* 2 m2) 1))
                (not (integerp (* 2 m1))) (not (integerp (* 2 m2))))
           (equal (rne m1) (rne m2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(rne) (theory 'minimal-theory))
                  :use ((:instance two-m (m m1)) (:instance two-m (m m2))
                        (:instance floor-bnds (m m1)) (:instance floor-bnds (m m2))
                        (:instance parity (a (floor m1 1)) (b (floor m2 1)))
                        (:instance parity (a (floor m2 1)) (b (floor m1 1))))))))

(local (defthm floor-open
  (implies (and (integerp s) (integerp g) (< 0 g) (rationalp tt) (< s tt) (< tt (+ s 1)))
           (and (equal (floor (/ tt g) 1) (floor (/ s g) 1)) (not (integerp (/ tt g)))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t
                  :use ((:instance int-side (pp (* g (floor (/ tt g) 1))) (t1 tt) (t2 (+ s 1/2)))
                        (:instance int-side (pp (* g (/ tt g))) (t1 tt) (t2 (+ s 1/2)))
                        (:instance floor-unique (x (/ tt g)) (n (floor (/ s g) 1)))
                        (:instance floor-unique (x (/ s g)) (n (floor (/ tt g) 1))))))))

(local (defthm rne-gap
  (implies (and (integerp s) (integerp g) (< 0 g) (rationalp t1) (rationalp t2)
                (< s t1) (< t1 (+ s 1)) (< s t2) (< t2 (+ s 1)))
           (equal (rne (/ t1 (* 2 g))) (rne (/ t2 (* 2 g)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne floor)
                  :use ((:instance floor-open (tt t1)) (:instance floor-open (tt t2))
                        (:instance rne-by-half (m1 (/ t1 (* 2 g))) (m2 (/ t2 (* 2 g)))))))))

(local (defthm scale-id
  (implies (and (rationalp q) (integerp e) (integerp p) (integerp j))
           (equal (/ q (expt 2 (- e (- p 1)))) (/ (* q (expt 2 j)) (* 2 (expt 2 (+ e (- p) j))))))
  :rule-classes nil))

(local (defthm gap-rv
  (implies (and (integerp s) (integerp j) (<= (expt 2 (+ (fl-prec k) 3)) s) (in-gap z s j) (in-gap q s j))
           (equal (fla-rv k q) (fla-rv k z)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fla-ex rne flog2)
                  :use (gap-ex-le (:instance gap-ex-le (q z) (z q)) gap-ex-big
                        (:instance scale-id (e (fla-ex k z)) (p (fl-prec k)))
                        (:instance scale-id (q z) (e (fla-ex k z)) (p (fl-prec k)))
                        (:instance expt2-int (n (+ (fla-ex k z) (- (fl-prec k)) j)))
                        (:instance rne-gap (g (expt 2 (+ (fla-ex k z) (- (fl-prec k)) j)))
                                   (t1 (* q (expt 2 j))) (t2 (* z (expt 2 j)))))))))

(local (defthm gap-round
  (implies (and (integerp s) (integerp j) (<= (expt 2 (+ (fl-prec k) 3)) s) (in-gap z s j) (in-gap q s j))
           (equal (fl-round k q) (fl-round k z)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fla-rv fla-ex rne flog2)
                  :use (gap-rv gap-ex-big (:instance gap-ex-big (z q)))))))

;; ---- SQRT is correctly rounded ------------------------------------------------------
; With j = fl-sqrt-j and s = fl-sqrt-s: either (s/2^j)^2 = x and fl-sqrt k x
; rounds s/2^j, the exact root; or sqrt(x) lies strictly between s/2^j and
; (s+1)/2^j, and every rational q there rounds to fl-sqrt k x, so the true
; root, a limit of such q, does too (rounding is constant on that interval).

(local (defthm div-iff
  (implies (and (rationalp a2) (rationalp x) (rationalp c) (< 0 c))
           (and (iff (< a2 (* x c)) (< (/ a2 c) x)) (iff (< (* x c) a2) (< x (/ a2 c)))
                (iff (equal a2 (* x c)) (equal (/ a2 c) x))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t))))

(local (defthm sq-id
  (implies (and (rationalp a) (integerp j))
           (equal (* (/ a (expt 2 j)) (/ a (expt 2 j))) (/ (* a a) (expt 4 j))))
  :rule-classes nil))

(local (defthm sq-scale
  (implies (and (rationalp a) (rationalp x) (integerp j))
           (and (iff (< (* a a) (* x (expt 4 j))) (< (* (/ a (expt 2 j)) (/ a (expt 2 j))) x))
                (iff (< (* x (expt 4 j)) (* a a)) (< x (* (/ a (expt 2 j)) (/ a (expt 2 j)))))
                (iff (equal (* a a) (* x (expt 4 j))) (equal (* (/ a (expt 2 j)) (/ a (expt 2 j))) x))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable expt)
                  :use ((:instance div-iff (a2 (* a a)) (c (expt 4 j)))
                        (:instance sq-id)
                        (:instance (:theorem (implies (integerp j) (< 0 (expt 4 j))))))))))

(local (defthm z-facts
  (implies (and (integerp s) (integerp j))
           (and (rationalp (/ (+ s 1/2) (expt 2 j))) (equal (* (/ (+ s 1/2) (expt 2 j)) (expt 2 j)) (+ s 1/2))
                (< s (+ s 1/2)) (< (+ s 1/2) (+ s 1)) (rationalp (/ s (expt 2 j)))))
  :rule-classes nil))

(defthm fl-sqrt-correct
  (implies (and (rationalp x) (< 0 x))
           (let ((j (fl-sqrt-j k x)) (s (fl-sqrt-s k x)))
             (if (fl-sqrt-exact k x)
                 (and (equal (* (/ s (expt 2 j)) (/ s (expt 2 j))) x)
                      (equal (fl-sqrt k x) (fl-round k (/ s (expt 2 j)))))
               (and (< (* (/ s (expt 2 j)) (/ s (expt 2 j))) x)
                    (< x (* (/ (+ s 1) (expt 2 j)) (/ (+ s 1) (expt 2 j))))
                    (implies (in-gap q s j) (equal (fl-sqrt k x) (fl-round k q)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(natp sqrt-j-int) (theory 'minimal-theory))
                  :use (sq-s-bounds sq-s-big fl-sqrt-unfold
                        (:instance z-facts (s (fl-sqrt-s k x)) (j (fl-sqrt-j k x)))
                        (:instance sq-scale (a (fl-sqrt-s k x)) (j (fl-sqrt-j k x)))
                        (:instance sq-scale (a (+ (fl-sqrt-s k x) 1)) (j (fl-sqrt-j k x)))
                        (:instance gap-round (s (fl-sqrt-s k x)) (j (fl-sqrt-j k x))
                                   (z (/ (+ (fl-sqrt-s k x) 1/2) (expt 2 (fl-sqrt-j k x)))))))))
