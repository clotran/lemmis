; fintr: EXP and LOG of a real (16.9.74, 16.9.120), correctly rounded.
;
; The standard gives EXP and LOG only as processor-dependent
; approximations. The model pins them: the result is the true value
; rounded (fl-round, ties to even), N = 1/2 ulp. N is the accuracy the
; constraint on fl-mag below states; a looser N would replace "the
; rounding of the true value" there with "a value within N ulps of it".
;
; No reals: the true value t of exp(x), or |log(x)|, is pinned by rational
; enclosures lo(n) <= t <= hi(n), Taylor (atanh) partial sums with a
; remainder bound, n terms. Their soundness, lo(n) <= hi(m) for every n and
; m, is proved (enc-sound). fl-mag k x is constrained to be fl-round k
; lo(n) for every depth n at which lo(n) and hi(n) round to one value
; (decides); since fl-round is monotone (fl-round-convex), all such depths
; agree (decides-agree), so that is the rounding of t. The executable
; fl-mag-impl, attached to fl-mag, searches n = 4, 8, 16, ...; t is
; transcendental (x rational, x /= 0 for EXP, x /= 1 for LOG), never on a
; rounding boundary, so some depth decides.
;
; EXP: |x| scaled to y = |x|/2^s <= 1 (s in 0, 5, 10), exp(|x|) =
; exp(y)^(2^s); exp(-a) = 1/exp(a); |x| > 1000 is past the overflow and
; underflow of both kinds: exp(1000) > 2^1400, exp(-1000) < 2^-1400.
; LOG: a = x or 1/x, a >= 1; a = 2^e f, 1 <= f < 2; log a = 2e atanh(1/3)
; + 2 atanh((f-1)/(f+1)).

(in-package "ACL2")
(include-book "freal")
(local (include-book "arithmetic-5/top" :dir :system))

;; ---- fl-round is monotone on the nonnegative rationals ---------------------

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

(local (defthm flog2-bounds
  (implies (and (rationalp a) (< 0 a))
           (and (<= (expt 2 (flog2 a)) a) (< a (expt 2 (+ 1 (flog2 a))))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance nd-lt (n (numerator a)) (d (denominator a))
                                   (p (expt 2 (+ -1 (integer-length (numerator a)))))
                                   (q (expt 2 (integer-length (denominator a)))))
                        (:instance nd-lt (p (numerator a)) (q (denominator a))
                                   (n (expt 2 (integer-length (numerator a))))
                                   (d (expt 2 (+ -1 (integer-length (denominator a)))))))))))

(local (defthm flog2-int (integerp (flog2 a)) :rule-classes :type-prescription))

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

(local (defthm flog2-mono
  (implies (and (rationalp a) (rationalp b) (< 0 a) (<= a b))
           (<= (flog2 a) (flog2 b)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable flog2)
                  :use ((:instance expt-sandwich (i (flog2 a)) (j (flog2 b)) (x a))
                        (:instance flog2-bounds (a a)) (:instance flog2-bounds (a b)))))))

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

(defun rv-at (a u) (declare (xargs :guard (and (rationalp a) (rationalp u) (< 0 u)))) (* (rne (/ a u)) u))
(defun fl-ulp (k e) (declare (xargs :guard (integerp e))) (expt 2 (- e (- (fl-prec k) 1))))
(defun fl-ex (k a) (declare (xargs :guard (and (rationalp a) (< 0 a)))) (max (flog2 a) (fl-emin k)))
(defun fl-rv (k a)                   ; fl-round's value of a > 0 before overflow
  (declare (xargs :guard (and (rationalp a) (< 0 a))))
  (rv-at a (fl-ulp k (fl-ex k a))))

(local (defthm rv-at-rational (implies (rationalp u) (rationalp (rv-at a u))) :rule-classes :type-prescription))

(local (defthm rv-at-mono
  (implies (and (rationalp a) (rationalp b) (rationalp u) (< 0 u) (<= a b)) (<= (rv-at a u) (rv-at b u)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne) :nonlinearp t :use ((:instance rne-mono (a (/ a u)) (b (/ b u))))))))

(local (defthm rv-at-le
  (implies (and (rationalp a) (rationalp u) (< 0 u) (integerp n) (<= a (* n u))) (<= (rv-at a u) (* n u)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne) :nonlinearp t :use ((:instance rne-mono (a (/ a u)) (b n)))))))

(local (defthm rv-at-ge
  (implies (and (rationalp a) (rationalp u) (< 0 u) (integerp n) (<= (* n u) a)) (<= (* n u) (rv-at a u)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable rne) :nonlinearp t :use ((:instance rne-mono (b (/ a u)) (a n)))))))

(local (defthm fl-ex-mono
  (implies (and (rationalp a) (rationalp b) (< 0 a) (<= a b)) (<= (fl-ex k a) (fl-ex k b)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable flog2)))))

(local (defthm expt-chain
  (implies (and (integerp i) (integerp j) (< i j) (rationalp x) (rationalp y)
                (<= x (expt 2 (+ 1 i))) (<= (expt 2 j) y))
           (<= x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance expt2-le (j (+ 1 i)) (i j)))))))

(local (defthm fl-ex-int (integerp (fl-ex k a)) :rule-classes :type-prescription))

(local (defthm fl-rv-mono
  (implies (and (rationalp a) (rationalp b) (< 0 a) (<= a b))
           (<= (fl-rv k a) (fl-rv k b)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable rv-at fl-ulp fl-ex flog2 rne)
                  :cases ((equal (fl-ex k a) (fl-ex k b))))
          ("Subgoal 1" :use ((:instance rv-at-mono (u (fl-ulp k (fl-ex k a))))))
          ("Subgoal 2" :in-theory (e/d (fl-ulp) (rv-at flog2 rne))
                       :use ((:instance rv-at-le (u (fl-ulp k (fl-ex k a))) (n (expt 2 (fl-prec k))))
                             (:instance rv-at-ge (a b) (u (fl-ulp k (fl-ex k b))) (n (expt 2 (- (fl-prec k) 1))))
                             (:instance flog2-bounds (a a)) (:instance flog2-bounds (a b))
                             (:instance expt-chain (x (rv-at a (fl-ulp k (fl-ex k a))))
                                        (y (rv-at b (fl-ulp k (fl-ex k b)))) (i (fl-ex k a)) (j (fl-ex k b)))
                             (:instance expt2-le (j (+ 1 (flog2 a))) (i (+ 1 (fl-ex k a))))
                             (:instance (:theorem (implies (and (integerp x) (integerp y) (< x y) (equal y (max z w)) (< x (max (flog2 b) w)) (<= w x)) (equal y z)))
                                        (x (fl-ex k a)) (y (fl-ex k b)) (z (flog2 b)) (w (fl-emin k))))))))

(local (defthm fl-rv-nonneg
  (implies (and (rationalp a) (< 0 a)) (<= 0 (fl-rv k a)))
  :rule-classes :linear))

(local (defthm fl-round-rv
  (implies (and (rationalp a) (< 0 a))
           (equal (fl-round k a)
                  (let ((v (fl-rv k a))) (cond ((<= (expt 2 (+ 1 (fl-emax k))) v) :pinf) (t v)))))))

(defthm fl-round-0 (equal (fl-round k 0) 0) :rule-classes nil)

(defthm fl-round-convex
  (implies (and (rationalp a) (rationalp b) (rationalp c) (<= 0 a) (<= a b) (<= b c)
                (equal (fl-round k a) (fl-round k c)))
           (equal (fl-round k b) (fl-round k a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fl-round fl-rv) :use ((:instance fl-round-0) (:instance fl-rv-mono (a a) (b b))
                                                            (:instance fl-rv-mono (a b) (b c)) (:instance fl-rv-nonneg (a b))) :cases ((and (equal a 0) (equal b 0)) (and (equal a 0) (< 0 b)) (< 0 a)))))

;; ---- series: exp (fn :exp) and atanh (fn :log) -----------------------------

(defun ser-ratio (fn y i)            ; term(i+1) / term(i)
  (declare (xargs :guard t))
  (let ((y (rfix y)) (i (nfix i)))
    (if (eq fn :exp) (/ y (+ i 1)) (* y y (/ (+ (* 2 i) 1) (+ (* 2 i) 3))))))
(defun ser-term (fn y i)             ; y^i/i!, y^(2i+1)/(2i+1)
  (declare (xargs :guard (natp i) :verify-guards nil))
  (if (zp i) (if (eq fn :exp) 1 (rfix y))
    (* (ser-term fn y (- i 1)) (ser-ratio fn y (- i 1)))))
(defun ser-sum (fn y n)              ; terms 0..n
  (declare (xargs :guard (natp n) :verify-guards nil))
  (if (zp n) (ser-term fn y 0) (+ (ser-term fn y n) (ser-sum fn y (- n 1)))))
(defun ser-hi (fn y n)               ; + the tail bound: terms fall by half
  (declare (xargs :guard (natp n) :verify-guards nil))
  (+ (ser-sum fn y n) (* 2 (ser-term fn y (+ 1 (nfix n))))))
(defun ser-ok (fn y)
  (declare (xargs :guard t))
  (and (rationalp y) (<= 0 y) (<= y (if (eq fn :exp) 1 1/3))))

(defthm ser-rational
  (and (rationalp (ser-term fn y i)) (rationalp (ser-sum fn y i)) (rationalp (ser-hi fn y i))))
(verify-guards ser-term)
(verify-guards ser-sum)
(verify-guards ser-hi)

(local (defthm ser-term-nonneg
  (implies (ser-ok fn y) (<= 0 (ser-term fn y i)))
  :rule-classes :linear))

(local (defthm div-le-num
  (implies (and (rationalp x) (rationalp y) (rationalp z) (< 0 z) (<= x y)) (<= (/ x z) (/ y z)))
  :rule-classes nil))

(local (defthm ser-ratio-half
  (implies (and (ser-ok fn y) (posp i)) (and (<= 0 (ser-ratio fn y i)) (<= (ser-ratio fn y i) 1/2)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance div-le-num (x y) (y (* 1/2 (+ 1 i))) (z (+ 1 i)))
                        (:instance div-le-num (x (+ 1 (* 2 i))) (y (+ 3 (* 2 i))) (z (+ 3 (* 2 i))))
                        (:instance (:theorem (implies (and (rationalp q) (rationalp r) (<= 0 q) (<= q 1/3) (<= 0 r) (<= r 1)) (<= (* q q r) 1/2)))
                                   (q y) (r (/ (+ 1 (* 2 i)) (+ 3 (* 2 i))))))
                  :nonlinearp t))))

(local (defthm ser-sum-nonneg
  (implies (ser-ok fn y) (<= 0 (ser-sum fn y n)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable ser-ok ser-term)))))

(local (defthm ser-term-half
  (implies (and (ser-ok fn y) (integerp i) (< 1 i))
           (<= (* 2 (ser-term fn y i)) (ser-term fn y (+ -1 i))))
  :rule-classes :linear
  :hints (("Goal" :expand ((ser-term fn y i)) :in-theory (disable ser-ratio)
                  :use ((:instance ser-ratio-half (i (+ -1 i)))) :nonlinearp t))))

(defun dec-ind (n m) (declare (xargs :measure (nfix n))) (if (and (natp n) (natp m) (< (+ 1 m) n)) (dec-ind (- n 1) m) t))
(defun up-ind (n m) (declare (xargs :measure (nfix m))) (if (and (natp n) (natp m) (< n m)) (up-ind n (- m 1)) t))

(local (defthm ser-tail
  (implies (and (ser-ok fn y) (natp m) (natp n) (< m n))
           (<= (+ (ser-sum fn y n) (ser-term fn y n))
               (+ (ser-sum fn y m) (* 2 (ser-term fn y (+ 1 m))))))
  :rule-classes nil
  :hints (("Goal" :induct (dec-ind n m) :expand ((ser-sum fn y n)) :in-theory (disable ser-term ser-ok)))))

(local (defthm ser-sum-step
  (implies (and (ser-ok fn y) (posp m)) (<= (ser-sum fn y (+ -1 m)) (ser-sum fn y m)))
  :rule-classes :linear :hints (("Goal" :expand ((ser-sum fn y m)) :in-theory (disable ser-term ser-ok)))))

(local (defthm ser-sum-mono
  (implies (and (ser-ok fn y) (natp m) (natp n) (<= n m))
           (<= (ser-sum fn y n) (ser-sum fn y m)))
  :rule-classes nil
  :hints (("Goal" :induct (up-ind n m) :in-theory (disable ser-sum ser-term ser-ok)))))

(defthm ser-sound                    ; the enclosure: every partial sum is below every bound
  (implies (and (ser-ok fn y) (natp n) (natp m))
           (<= (ser-sum fn y n) (ser-hi fn y m)))
  :hints (("Goal" :in-theory (disable ser-term ser-sum ser-ok) :cases ((<= n m))
                  :use (ser-tail ser-sum-mono (:instance ser-term-nonneg (i (+ 1 m)))))))

;; ---- the enclosures ---------------------------------------------------------

(defun sqpow (v s)                   ; v^(2^s), s squarings
  (declare (xargs :guard (natp s)))
  (if (zp s) (rfix v) (sqpow (* (rfix v) (rfix v)) (- s 1))))

(defun sqpow2-ind (a b s) (if (zp s) (list a b) (sqpow2-ind (* a a) (* b b) (- s 1))))

(local (defthm sqpow-mono
  (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b)) (<= (sqpow a s) (sqpow b s)))
  :rule-classes nil
  :hints (("Goal" :induct (sqpow2-ind a b s) :nonlinearp t))))

(local (defthm sqpow-ge-1
  (implies (and (rationalp a) (<= 1 a)) (<= 1 (sqpow a s)))
  :rule-classes :linear :hints (("Goal" :nonlinearp t))))

(defun exp-s (a) (declare (xargs :guard (rationalp a))) (cond ((<= a 1) 0) ((<= a 32) 5) (t 10)))
(defun exp-y (a) (declare (xargs :guard (rationalp a))) (/ (rfix a) (expt 2 (exp-s a))))
(defun exp-lo+ (a n) (declare (xargs :guard (and (rationalp a) (natp n)))) (sqpow (ser-sum :exp (exp-y a) n) (exp-s a)))
(defun exp-hi+ (a n) (declare (xargs :guard (and (rationalp a) (natp n)))) (sqpow (ser-hi :exp (exp-y a) n) (exp-s a)))

(local (defthm exp-y-ok
  (implies (and (rationalp a) (<= 0 a) (<= a 1000)) (ser-ok :exp (exp-y a)))))

(local (defthm exp-sum-ge-1
  (implies (and (ser-ok :exp y) (natp n)) (<= 1 (ser-sum :exp y n)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable ser-ok) :use ((:instance ser-sum-mono (fn :exp) (n 0) (m n)))))))

(local (defthm exp+-sound
  (implies (and (rationalp a) (<= 0 a) (<= a 1000) (natp n) (natp m))
           (and (<= 1 (exp-lo+ a n)) (<= (exp-lo+ a n) (exp-hi+ a m))))
  :hints (("Goal" :in-theory (disable ser-ok ser-sum ser-hi exp-y ser-sound)
                  :use ((:instance ser-sound (fn :exp) (y (exp-y a)))
                        (:instance sqpow-mono (a (ser-sum :exp (exp-y a) n)) (b (ser-hi :exp (exp-y a) m)) (s (exp-s a))))))))

(defun log-split (a e)               ; a = 2^e' f, 1 <= f < 2 for a >= 1: (f . e+e')
  (declare (xargs :guard t :measure (nfix (floor (rfix a) 1))))
  (if (or (not (rationalp a)) (< a 2)) (cons a (ifix e)) (log-split (/ a 2) (+ (ifix e) 1))))

(local (defthm log-split-props
  (implies (and (rationalp a) (<= 1 a) (natp e))
           (and (rationalp (car (log-split a e))) (<= 1 (car (log-split a e)))
                (< (car (log-split a e)) 2) (integerp (cdr (log-split a e))) (<= 0 (cdr (log-split a e)))))))

(defun log-z (a)                     ; (f-1)/(f+1), log a = 2e atanh(1/3) + 2 atanh(z)
  (declare (xargs :guard (and (rationalp a) (<= 1 a))
                  :guard-hints (("Goal" :in-theory (disable log-split log-split-props) :use ((:instance log-split-props (e 0)))))))
  (let ((f (rfix (car (log-split a 0))))) (/ (- f 1) (+ f 1))))
(defun log-e (a) (declare (xargs :guard t)) (nfix (cdr (log-split a 0))))
(defun log-a (x) (declare (xargs :guard (and (rationalp x) (< 0 x)))) (if (< x 1) (/ x) x))

(local (defthm log-split-rational (implies (rationalp a) (rationalp (car (log-split a e)))) :rule-classes :type-prescription))

(local (defthm scale-le
  (implies (and (rationalp a) (rationalp b) (rationalp e) (<= a b) (<= 0 e)) (<= (* e a) (* e b)))
  :rule-classes nil :hints (("Goal" :nonlinearp t))))

(local (defthm z-ok
  (implies (and (rationalp f) (<= 1 f) (< f 2)) (ser-ok :log (/ (- f 1) (+ f 1))))
  :hints (("Goal" :use ((:instance div-le-num (x (- f 1)) (y (* 1/3 (+ f 1))) (z (+ f 1))))))))

(local (defthm log-z-ok
  (implies (and (rationalp a) (<= 1 a)) (ser-ok :log (log-z a)))
  :hints (("Goal" :in-theory (disable log-split ser-ok) :use ((:instance log-split-props (e 0)) (:instance z-ok (f (car (log-split a 0)))))))))

(local (defthm log-a-ge-1
  (implies (and (rationalp x) (< 0 x)) (and (rationalp (log-a x)) (<= 1 (log-a x))))))

(local (defthm log-enc-sound
  (implies (and (rationalp a) (<= 1 a) (natp n) (natp m))
           (and (<= 0 (+ (* 2 (log-e a) (ser-sum :log 1/3 n)) (* 2 (ser-sum :log (log-z a) n))))
                (<= (+ (* 2 (log-e a) (ser-sum :log 1/3 n)) (* 2 (ser-sum :log (log-z a) n)))
                    (+ (* 2 (log-e a) (ser-hi :log 1/3 m)) (* 2 (ser-hi :log (log-z a) m))))))
  :hints (("Goal" :in-theory (disable log-e log-z ser-sum ser-hi ser-ok ser-sound)
                  :use ((:instance log-z-ok)
                        (:instance ser-sound (fn :log) (y 1/3))
                        (:instance ser-sound (fn :log) (y (log-z a)))
                        (:instance ser-sum-nonneg (fn :log) (y 1/3))
                        (:instance ser-sum-nonneg (fn :log) (y (log-z a)))
                        (:instance scale-le (e (log-e a)) (a 0) (b (ser-sum :log 1/3 n)))
                        (:instance scale-le (e (log-e a)) (a (ser-sum :log 1/3 n)) (b (ser-hi :log 1/3 m))))))))

; lo(n) and hi(n) for EXP (fn :exp) and |LOG| (else); hi nil: unbounded
(defun enc-lo (fn x n)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (rationalp x)) 0)
        ((eq fn :exp)
         (cond ((< 1000 x) (expt 2 1400)) ((< x -1000) 0)
               ((<= 0 x) (exp-lo+ x (nfix n))) (t (/ (exp-hi+ (- x) (nfix n))))))
        ((<= x 0) 0)
        (t (let ((a (log-a x)))
             (+ (* 2 (log-e a) (ser-sum :log 1/3 (nfix n))) (* 2 (ser-sum :log (log-z a) (nfix n))))))))
(defun enc-hi (fn x n)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (rationalp x)) 0)
        ((eq fn :exp)
         (cond ((< 1000 x) nil) ((< x -1000) (expt 2 -1400))
               ((<= 0 x) (exp-hi+ x (nfix n))) (t (/ (exp-lo+ (- x) (nfix n))))))
        ((<= x 0) 0)
        (t (let ((a (log-a x)))
             (+ (* 2 (log-e a) (ser-hi :log 1/3 (nfix n))) (* 2 (ser-hi :log (log-z a) (nfix n))))))))

(defthm enc-lo-type
  (and (rationalp (enc-lo fn x n)) (<= 0 (enc-lo fn x n)))
  :hints (("Goal" :in-theory (disable exp-lo+ exp-hi+ log-a log-e log-z ser-sum ser-hi ser-ok)
                  :use ((:instance exp+-sound (a x) (n (nfix n)) (m (nfix n))) (:instance exp+-sound (a (- x)) (n (nfix n)) (m (nfix n)))
                        (:instance log-a-ge-1) (:instance log-enc-sound (a (log-a x)) (n (nfix n)) (m (nfix n)))))))

(defthm enc-hi-type
  (or (null (enc-hi fn x n)) (rationalp (enc-hi fn x n)))
  :rule-classes :type-prescription)

(verify-guards enc-lo :hints (("Goal" :in-theory (disable exp-lo+ exp-hi+ log-a log-e log-z ser-sum ser-hi ser-ok exp+-sound)
                                     :use ((:instance exp+-sound (a (- x)) (n (nfix n)) (m (nfix n)))))))
(verify-guards enc-hi :hints (("Goal" :in-theory (disable exp-lo+ exp-hi+ log-a log-e log-z ser-sum ser-hi ser-ok exp+-sound)
                                     :use ((:instance exp+-sound (a (- x)) (n (nfix n)) (m (nfix n)))))))

(defthm enc-sound                    ; soundness: every lower end below every upper end
  (implies (and (natp n) (natp m) (enc-hi fn x m))
           (<= (enc-lo fn x n) (enc-hi fn x m)))
  :hints (("Goal" :in-theory (disable exp-lo+ exp-hi+ log-a log-e log-z ser-sum ser-hi ser-ok)
                  :use ((:instance exp+-sound (a x)) (:instance exp+-sound (a (- x)) (n m) (m n))
                        (:instance log-a-ge-1) (:instance log-enc-sound (a (log-a x)))))))

(defthm enc-unbounded               ; hi nil: at every depth, and lo the same at every depth
  (implies (not (enc-hi fn x m))
           (and (not (enc-hi fn x n)) (equal (enc-lo fn x n) (enc-lo fn x m))))
  :rule-classes nil)

;; ---- the correctly rounded magnitude: constrained, and its executable ---------

(defun enc-round (k q) (declare (xargs :guard t)) (if (rationalp q) (fl-round k q) :pinf))
(defun decides (fn k x n)            ; both ends of depth n round to one value
  (declare (xargs :guard t))
  (equal (fl-round k (enc-lo fn x n)) (enc-round k (enc-hi fn x n))))

(defthm decides-agree                ; every deciding depth gives one value
  (implies (and (natp n) (natp m) (decides fn k x n) (decides fn k x m))
           (equal (fl-round k (enc-lo fn x n)) (fl-round k (enc-lo fn x m))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable enc-lo enc-hi fl-round)
                  :cases ((not (enc-hi fn x m)) (<= (enc-lo fn x n) (enc-lo fn x m)))
                  :use (enc-unbounded (:instance enc-unbounded (m n) (n m))
                        (:instance enc-sound (n m) (m n)) (:instance enc-sound)
                        (:instance fl-round-convex (a (enc-lo fn x n)) (b (enc-lo fn x m)) (c (enc-hi fn x n)))
                        (:instance fl-round-convex (a (enc-lo fn x m)) (b (enc-lo fn x n)) (c (enc-hi fn x m)))))))

(defchoose dec-wit (n) (fn k x) (and (natp n) (decides fn k x n)))
(defun mag-wit (fn k x) (declare (xargs :guard t)) (fl-round k (enc-lo fn x (nfix (dec-wit fn k x)))))

(defthm mag-wit-ok
  (implies (and (natp n) (decides fn k x n))
           (equal (mag-wit fn k x) (fl-round k (enc-lo fn x n))))
  :hints (("Goal" :in-theory (disable decides fl-round enc-lo)
                  :use ((:instance dec-wit) (:instance decides-agree (m (dec-wit fn k x)))))))

; fl-mag fn k x: the rounding of the true value -- exp(x) for fn :exp, |log(x)|
; else -- the value every deciding depth's ends round to (N = 1/2)
(encapsulate (((fl-mag * * *) => *))
  (local (defun fl-mag (fn k x) (mag-wit fn k x)))
  (defthm fl-mag-correctly-rounded
    (implies (and (natp n) (decides fn k x n))
             (equal (fl-mag fn k x) (fl-round k (enc-lo fn x n))))
    :hints (("Goal" :in-theory (disable mag-wit decides fl-round enc-lo)))))

(defun mag-search (fn k x n fuel)    ; depths n, 2n, 4n, ...: fuel of them
  (declare (xargs :guard (and (natp n) (natp fuel)) :measure (nfix fuel)))
  (cond ((zp fuel) (non-exec (mag-wit fn k x)))           ; never reached: t is transcendental
        ((decides fn k x n) (fl-round k (enc-lo fn x n)))
        (t (mag-search fn k x (* 2 (nfix n)) (- fuel 1)))))

(defthm mag-search-ok
  (implies (natp n) (equal (mag-search fn k x n fuel) (mag-wit fn k x)))
  :hints (("Goal" :in-theory (disable mag-wit decides fl-round enc-lo))
          ("Subgoal *1/2" :use ((:instance mag-wit-ok)))))

(defun fl-mag-impl (fn k x) (declare (xargs :guard t)) (mag-search fn k x 4 10))

(defattach (fl-mag fl-mag-impl) :hints (("Goal" :in-theory (disable mag-search decides fl-round enc-lo)
                                              :use ((:instance mag-wit-ok) (:instance mag-search-ok (n 4) (fuel 10))))))

;; ---- EXP and LOG of a value of the format ------------------------------------

(defun fl-exp (k x)                  ; 16.9.74; ISO/IEC 60559 9.2: exp(-inf) = +0
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (not (fl-x-p x))) :nan)
        ((eq x :pinf) :pinf) ((eq x :ninf) 0) ((fl-zero-p x) 1)
        (t (fl-mag :exp k x))))

(defun fl-log (k x)                  ; 16.9.120; 9.2: log(+-0) = -inf, log(x < 0) = NaN
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (eq x :ninf) (not (fl-x-p x))) :nan)
        ((eq x :pinf) :pinf) ((fl-zero-p x) :ninf) ((< x 0) :nan)
        ((< x 1) (fl-neg (fl-mag :log k x)))
        (t (fl-mag :log k x))))

(assert-event (equal (fl-exp 8 0) 1))
(assert-event (equal (fl-log 8 1) 0))
(assert-event (equal (fl-exp 8 710) :pinf))
(assert-event (equal (fl-exp 8 1) 6121026514868073/2251799813685248))     ; 2.718281828459045
(assert-event (equal (fl-log 8 2) 6243314768165359/9007199254740992))     ; 0.6931471805599453
