; ftrig: SIN, COS, TAN, ATAN, ATAN2 of a real (16.9.180, .55, .193, .20, .21),
; correctly rounded, the way fintr.lisp does EXP and LOG.
;
; The result is the true value rounded (fl-round, ties to even), N = 1/2 ulp.
; No reals: at depth j the true value t lies in a rational enclosure
; [raw-lo j, raw-hi j] built from alternating series (atan, sin, cos: the
; partial sums of an even number of terms are below, of an odd number above,
; when the terms fall; alt-sound, proved) and pi from Machin's formula
; pi = 16 atan(1/5) - 4 atan(1/239) (pi-sound, proved: every lower end below
; every upper end), rounded outward to b bits (dpi-sound).
;
; Range reduction is exact: a = |x| > 0 rational, k = nearest integer to
; a/(pi/2) by the lower pi; r = a - k pi/2 lies in [a - k ph/2, a - k pl/2]
; for pi in [pl, ph], |r| < 1, and sin/cos/tan of a follow from those of r by
; k mod 4. pi has b = 64 2^j + log2 a + 8 bits, so 1.8e308 needs ~1100 bits
; at depth 0 and the depth grows until the ends round alike.
;
; The enclosure the constraint uses is the hull: the intersection of depths
; 0..j (trig-lo nondecreasing, trig-hi nonincreasing, hull-mono). So any two
; depths that decide (lo <= hi, one strict sign, both ends round alike) agree
; (tdec-agree) without a proof that the composed reduction encloses t -- that
; it does is the series' and pi's soundness above plus sin's monotonicity on
; |r| < pi/2, argued, not proved (no reals). fl-trig is constrained to the
; deciding depths' value; fl-trig-impl searches j = 0, 1, ..., 8. t is
; transcendental (Lindemann, Lambert: x rational nonzero), never a rounding
; boundary, so some depth decides.

(in-package "ACL2")
(include-book "fintr")
(local (include-book "arithmetic-5/top" :dir :system))

(defun qdiv (a b) (declare (xargs :guard t)) (if (and (rationalp a) (rationalp b) (not (= b 0))) (/ a b) 0))

;; ---- alternating series: atan, sin, cos ------------------------------------

(defun alt-q (fn i)                  ; term(i+1) / term(i) / y^2
  (declare (xargs :guard t))
  (let ((i (nfix i)))
    (case fn (:atan (- 1 (/ 2 (+ 3 (* 2 i)))))
      (:sin (/ (* (+ 2 (* 2 i)) (+ 3 (* 2 i)))))
      (otherwise (/ (* (+ 1 (* 2 i)) (+ 2 (* 2 i))))))))
(defun alt-ratio (fn y i) (declare (xargs :guard t)) (* (rfix y) (rfix y) (alt-q fn i)))
(defun alt-term (fn y i)             ; y^(2i+1)/(2i+1), y^(2i+1)/(2i+1)!, y^(2i)/(2i)!
  (declare (xargs :guard t :verify-guards nil))
  (if (not (posp i)) (if (eq fn :cos) 1 (rfix y))
    (* (alt-term fn y (- i 1)) (alt-ratio fn y (- i 1)))))
(defun alt-p (fn y j)                ; j pairs (term 2i - term 2i+1): a lower end
  (declare (xargs :guard t :verify-guards nil))
  (if (not (posp j)) 0
    (+ (alt-p fn y (- j 1)) (- (alt-term fn y (* 2 (- j 1))) (alt-term fn y (+ 1 (* 2 (- j 1))))))))
(defun alt-hi (fn y j) (declare (xargs :guard t :verify-guards nil)) (+ (alt-p fn y j) (alt-term fn y (* 2 (nfix j)))))

(defthm alt-rational (and (rationalp (alt-term fn y i)) (rationalp (alt-p fn y j)) (rationalp (alt-hi fn y j)))
  :rule-classes (:rewrite (:type-prescription :corollary (rationalp (alt-p fn y j)))
                          (:type-prescription :corollary (rationalp (alt-hi fn y j)))))
(verify-guards alt-term)
(verify-guards alt-p)
(verify-guards alt-hi)

(defun alt-ok (y) (declare (xargs :guard t)) (and (rationalp y) (<= 0 y) (<= y 1)))

(local (defthm alt-q-01 (and (<= 0 (alt-q fn i)) (<= (alt-q fn i) 1)) :rule-classes :linear
  :hints (("Goal" :nonlinearp t))))

(local (defthm alt-ratio-01
  (implies (alt-ok y) (and (<= 0 (alt-ratio fn y i)) (<= (alt-ratio fn y i) 1)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable alt-q)
                  :use ((:instance (:theorem (implies (and (rationalp q) (rationalp r) (<= 0 q) (<= q 1) (<= 0 r) (<= r 1))
                                                     (and (<= 0 (* q q r)) (<= (* q q r) 1))))
                                   (q y) (r (alt-q fn i))))
                  :nonlinearp t))))

(local (defthm alt-term-nonneg (implies (alt-ok y) (<= 0 (alt-term fn y i))) :rule-classes :linear
  :hints (("Goal" :in-theory (disable alt-ratio alt-ok)))))

(local (defthm alt-term-dec
  (implies (and (alt-ok y) (natp i)) (<= (alt-term fn y (+ 1 i)) (alt-term fn y i)))
  :rule-classes :linear
  :hints (("Goal" :expand ((alt-term fn y (+ 1 i))) :in-theory (disable alt-ratio alt-ok)
                  :use ((:instance alt-ratio-01) (:instance alt-term-nonneg)) :nonlinearp t))))

(local (defthm alt-p-step
  (implies (and (alt-ok y) (posp j)) (<= (alt-p fn y (+ -1 j)) (alt-p fn y j)))
  :rule-classes :linear
  :hints (("Goal" :expand ((alt-p fn y j)) :in-theory (disable alt-term alt-ok)
                  :use ((:instance alt-term-dec (i (* 2 (- j 1)))))))))

(local (defthm alt-hi-step
  (implies (and (alt-ok y) (posp j)) (<= (alt-hi fn y j) (alt-hi fn y (+ -1 j))))
  :rule-classes :linear
  :hints (("Goal" :expand ((alt-p fn y j)) :in-theory (disable alt-term alt-ok)
                  :use ((:instance alt-term-dec (i (+ 1 (* 2 (- j 1))))))))))

(local (defthm alt-p-mono
  (implies (and (alt-ok y) (natp n) (natp m) (<= n m)) (<= (alt-p fn y n) (alt-p fn y m)))
  :rule-classes nil
  :hints (("Goal" :induct (up-ind n m) :in-theory (disable alt-p alt-hi alt-ok)))))

(local (defthm alt-hi-mono
  (implies (and (alt-ok y) (natp n) (natp m) (<= n m)) (<= (alt-hi fn y m) (alt-hi fn y n)))
  :rule-classes nil
  :hints (("Goal" :induct (up-ind n m) :in-theory (disable alt-p alt-hi alt-ok)))))

(defthm alt-sound                    ; every even partial sum below every odd one
  (implies (and (alt-ok y) (natp n) (natp m)) (<= (alt-p fn y n) (alt-hi fn y m)))
  :hints (("Goal" :cases ((<= n m)) :in-theory (disable alt-p alt-term alt-ok)
                  :use (alt-p-mono (:instance alt-hi-mono (n m) (m n))
                        (:instance alt-term-nonneg (i (* 2 m))) (:instance alt-term-nonneg (i (* 2 n)))))))

;; ---- pi -----------------------------------------------------------------------

(defun pi-lo (j) (declare (xargs :guard t)) (- (* 16 (alt-p :atan 1/5 j)) (* 4 (alt-hi :atan 1/239 j))))
(defun pi-hi (j) (declare (xargs :guard t)) (- (* 16 (alt-hi :atan 1/5 j)) (* 4 (alt-p :atan 1/239 j))))

(defthm pi-sound (implies (and (natp n) (natp m)) (<= (pi-lo n) (pi-hi m)))
  :hints (("Goal" :in-theory (disable alt-p alt-hi alt-sound)
                  :use ((:instance alt-sound (fn :atan) (y 1/5)) (:instance alt-sound (fn :atan) (y 1/239) (n m) (m n))))))

(defun pi-pairs (b) (declare (xargs :guard t)) (+ 2 (floor (nfix b) 9)))   ; 5^-4 < 2^-9 a pair
(defun dn (q b) (declare (xargs :guard t)) (let ((s (expt 2 (nfix b)))) (/ (floor (* (rfix q) s) 1) s)))
(defun up (q b) (declare (xargs :guard t)) (let ((s (expt 2 (nfix b)))) (/ (ceiling (* (rfix q) s) 1) s)))
(local (defthm dn-le (<= (dn q b) (rfix q)) :rule-classes nil
  :hints (("Goal" :use ((:instance (:theorem (implies (rationalp x) (<= (floor x 1) x))) (x (* (rfix q) (expt 2 (nfix b))))))
                  :nonlinearp t))))
(local (defthm up-ge (<= (rfix q) (up q b)) :rule-classes nil
  :hints (("Goal" :use ((:instance (:theorem (implies (rationalp x) (<= x (ceiling x 1)))) (x (* (rfix q) (expt 2 (nfix b))))))
                  :nonlinearp t))))
(defun dpi-lo (b) (declare (xargs :guard t)) (dn (pi-lo (pi-pairs b)) b))     ; pi to b bits, outward
(defun dpi-hi (b) (declare (xargs :guard t)) (up (pi-hi (pi-pairs b)) b))

(defthm dpi-sound (<= (dpi-lo b) (dpi-hi c))
  :hints (("Goal" :in-theory (disable pi-lo pi-hi pi-sound dn up)
                  :use ((:instance pi-sound (n (pi-pairs b)) (m (pi-pairs c)))
                        (:instance dn-le (q (pi-lo (pi-pairs b)))) (:instance up-ge (q (pi-hi (pi-pairs c))) (b c))))))

(assert-event (and (< (dpi-lo 64) 314159265358979323847/100000000000000000000)
                   (< 314159265358979323846/100000000000000000000 (dpi-hi 64))
                   (< (- (dpi-hi 64) (dpi-lo 64)) (expt 2 -60))))

;; ---- the raw enclosures at depth j ---------------------------------------------

(defun ilo (iv) (declare (xargs :guard t)) (if (consp iv) (rfix (car iv)) 0))
(defun ihi (iv) (declare (xargs :guard t)) (if (consp iv) (rfix (cdr iv)) 0))

(defthm dpi-lo-rational (rationalp (dpi-lo b)) :rule-classes :type-prescription)
(defthm dpi-hi-rational (rationalp (dpi-hi b)) :rule-classes :type-prescription)
(defthm flog2-integer (integerp (flog2 a)) :rule-classes :type-prescription)
(in-theory (disable dpi-lo dpi-hi flog2))

(defun ineg (iv) (declare (xargs :guard t)) (cons (- (ihi iv)) (- (ilo iv))))
(defun pt-sin (r j hi)               ; a bound on sin r, |r| <= 1
  (declare (xargs :guard t))
  (let ((r (rfix r)))
    (if (<= 0 r) (if hi (alt-hi :sin r j) (alt-p :sin r j))
      (- (if hi (alt-p :sin (- r) j) (alt-hi :sin (- r) j))))))
(defun iv-div+ (nl nh dl dh)           ; [nl,nh]/[dl,dh], 0 < dl <= dh
  (declare (xargs :guard t))
  (cond ((<= 0 (rfix nl)) (cons (qdiv nl dh) (qdiv nh dl)))
        ((<= (rfix nh) 0) (cons (qdiv nl dl) (qdiv nh dh)))
        (t (cons (qdiv nl dl) (qdiv nh dl)))))
(defun iv-div (n d)                    ; n/d over intervals; d across 0: unbounded (+-2^4000)
  (declare (xargs :guard t))
  (cond ((< 0 (ilo d)) (iv-div+ (ilo n) (ihi n) (ilo d) (ihi d)))
        ((< (ihi d) 0) (iv-div+ (- (ihi n)) (- (ilo n)) (- (ihi d)) (- (ilo d))))
        (t (cons (- (expt 2 4000)) (expt 2 4000)))))

(defun reduce-iv (fn a j)            ; sin, cos, tan of a > 0
  (declare (xargs :guard t :guard-hints (("Goal" :in-theory (disable pt-sin alt-p alt-hi iv-div ineg floor mod evenp (:e dpi-lo) (:e dpi-hi))))))
  (let* ((a (rfix a)) (g (* 64 (expt 2 (nfix j))))
         (b (+ g 8 (if (< 1 a) (flog2 a) 0)))
         (pl (dpi-lo b)) (ph (dpi-hi b))
         (k (nfix (floor (+ (qdiv (* 2 a) pl) 1/2) 1)))
         (rl (- a (* k ph 1/2))) (rh (- a (* k pl 1/2)))
         (ns (+ 2 (floor g 8)))
         (s (cons (pt-sin rl ns nil) (pt-sin rh ns t)))
         (big (max (abs rl) (abs rh)))
         (small (if (and (<= rl 0) (<= 0 rh)) 0 (min (abs rl) (abs rh))))
         (c (cons (alt-p :cos big ns) (alt-hi :cos small ns)))
         (q (mod k 4)))
    (case fn
      (:sin (case q (0 s) (1 c) (2 (ineg s)) (otherwise (ineg c))))
      (:cos (case q (0 c) (1 (ineg s)) (2 (ineg c)) (otherwise s)))
      (otherwise (if (evenp k) (iv-div s c) (ineg (iv-div c s)))))))

(defun atan01 (y n hi)               ; a bound on atan y, 0 <= y <= 1: y > 1/2 by atan 1/2 + atan z
  (declare (xargs :guard t))
  (let ((y (rfix y)))
    (if (<= y 1/2) (if hi (alt-hi :atan y n) (alt-p :atan y n))
      (let ((z (qdiv (- (* 2 y) 1) (+ 2 y))))
        (if hi (+ (alt-hi :atan 1/2 n) (alt-hi :atan z n)) (+ (alt-p :atan 1/2 n) (alt-p :atan z n)))))))

(defun trig-raw (fn x j)             ; :sin :cos :tan :atan of x > 0; :patan pi - atan x; :pim x pi
  (declare (xargs :guard t :guard-hints (("Goal" :in-theory (disable reduce-iv atan01 floor (:e dpi-lo) (:e dpi-hi))))))
  (let ((iv (if (member-eq fn '(:sin :cos :tan)) (reduce-iv fn x j)
              (let* ((x (rfix x)) (g (* 64 (expt 2 (nfix j)))) (pl (dpi-lo (+ g 8))) (ph (dpi-hi (+ g 8)))
                     (n (+ 2 (floor g 4)))
                     (at (if (<= x 1) (cons (atan01 x n nil) (atan01 x n t))
                           (cons (- (/ pl 2) (atan01 (qdiv 1 x) n t)) (- (/ ph 2) (atan01 (qdiv 1 x) n nil))))))
                (case fn
                  (:atan at)
                  (:patan (cons (- pl (ihi at)) (- ph (ilo at))))
                  (otherwise (cons (* x pl) (* x ph))))))))
    (cons (ilo iv) (ihi iv))))

(defthm trig-raw-rational (and (rationalp (ilo (trig-raw fn x j))) (rationalp (ihi (trig-raw fn x j))))
  :hints (("Goal" :in-theory (disable reduce-iv atan01 dpi-lo dpi-hi))))
(in-theory (disable trig-raw))

;; ---- the hull and the deciding depths -------------------------------------------

(defun trig-hull (fn x j)
  (declare (xargs :guard t))
  (let ((r (trig-raw fn x j)))
    (if (not (posp j)) r
      (let ((h (trig-hull fn x (- j 1))))
        (cons (max (ilo h) (ilo r)) (min (ihi h) (ihi r)))))))
(defun trig-lo (fn x j) (declare (xargs :guard t)) (ilo (trig-hull fn x j)))
(defun trig-hi (fn x j) (declare (xargs :guard t)) (ihi (trig-hull fn x j)))

(defthm trig-hull-rational (and (rationalp (trig-lo fn x j)) (rationalp (trig-hi fn x j))))
(in-theory (disable trig-lo trig-hi))

(local (defthm hull-step
  (implies (posp j) (and (<= (trig-lo fn x (+ -1 j)) (trig-lo fn x j)) (<= (trig-hi fn x j) (trig-hi fn x (+ -1 j)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable trig-lo trig-hi) :expand ((trig-hull fn x j))))))

(defthm hull-mono                    ; the hull shrinks with the depth
  (implies (and (natp n) (natp m) (<= n m))
           (and (<= (trig-lo fn x n) (trig-lo fn x m)) (<= (trig-hi fn x m) (trig-hi fn x n))))
  :rule-classes nil
  :hints (("Goal" :induct (up-ind n m))))

(defun tval (k lo hi) (declare (xargs :guard (and (rationalp lo) (rationalp hi))))
  (if (< 0 lo) (fl-round k lo) (fl-neg (fl-round k (- hi)))))
(defun tdec (fn k x j)               ; lo <= hi, one strict sign, both ends round to one value
  (declare (xargs :guard t))
  (let ((lo (trig-lo fn x j)) (hi (trig-hi fn x j)))
    (and (<= lo hi)
         (or (and (< 0 lo) (equal (fl-round k lo) (fl-round k hi)))
             (and (< hi 0) (equal (fl-round k (- hi)) (fl-round k (- lo))))))))
(defun tdec-val (fn k x j) (declare (xargs :guard t)) (tval k (trig-lo fn x j) (trig-hi fn x j)))

(local (defthm tdec-agree-le
  (implies (and (natp n) (natp m) (<= n m) (tdec fn k x n) (tdec fn k x m))
           (equal (tdec-val fn k x m) (tdec-val fn k x n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fl-round fl-neg)
                  :use (hull-mono
                        (:instance fl-round-convex (a (trig-lo fn x n)) (b (trig-lo fn x m)) (c (trig-hi fn x n)))
                        (:instance fl-round-convex (a (- (trig-hi fn x n))) (b (- (trig-hi fn x m))) (c (- (trig-lo fn x n)))))))))

(defthm tdec-agree                   ; every deciding depth gives one value
  (implies (and (natp n) (natp m) (tdec fn k x n) (tdec fn k x m))
           (equal (tdec-val fn k x m) (tdec-val fn k x n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable tdec tdec-val) :cases ((<= n m))
                  :use (tdec-agree-le (:instance tdec-agree-le (n m) (m n))))))

(defchoose tdec-wit (j) (fn k x) (and (natp j) (tdec fn k x j)))
(defun trig-wit (fn k x) (declare (xargs :guard t)) (tdec-val fn k x (nfix (tdec-wit fn k x))))

(defthm trig-wit-ok
  (implies (and (natp j) (tdec fn k x j)) (equal (trig-wit fn k x) (tdec-val fn k x j)))
  :hints (("Goal" :in-theory (disable tdec tdec-val)
                  :use ((:instance tdec-wit) (:instance tdec-agree (n j) (m (tdec-wit fn k x)))))))

; fl-trig fn k x: the rounding of the true value (sin x, cos x, tan x, atan x,
; pi - atan x, x pi for fn :sin :cos :tan :atan :patan :pim), N = 1/2
(encapsulate (((fl-trig * * *) => *))
  (local (defun fl-trig (fn k x) (trig-wit fn k x)))
  (defthm fl-trig-correctly-rounded
    (implies (and (natp j) (tdec fn k x j)) (equal (fl-trig fn k x) (tdec-val fn k x j)))
    :hints (("Goal" :in-theory (disable trig-wit tdec tdec-val)))))

(defun trig-search (fn k x j fuel)   ; depths j, j+1, ...: fuel of them
  (declare (xargs :guard (natp j) :measure (nfix fuel)))
  (cond ((not (posp fuel)) (non-exec (trig-wit fn k x)))         ; never reached: t is transcendental
        ((tdec fn k x j) (tdec-val fn k x j))
        (t (trig-search fn k x (+ 1 (nfix j)) (- fuel 1)))))

(defthm trig-search-ok
  (implies (natp j) (equal (trig-search fn k x j fuel) (trig-wit fn k x)))
  :hints (("Goal" :in-theory (disable trig-wit tdec tdec-val))
          ("Subgoal *1/2" :use ((:instance trig-wit-ok)))))

(defun fl-trig-impl (fn k x) (declare (xargs :guard t)) (trig-search fn k x 0 9))

(defattach (fl-trig fl-trig-impl) :hints (("Goal" :in-theory (disable trig-search tdec tdec-val)
                                                :use ((:instance trig-wit-ok) (:instance trig-search-ok (j 0) (fuel 9))))))

;; ---- the intrinsics on values of the format ---------------------------------------

(defun fl-odd (fn k x)               ; an odd function: f(-x) = -f(x), f(+-0) = +-0
  (declare (xargs :guard t))
  (cond ((fl-zero-p x) x) ((< (fl-val x) 0) (fl-neg (fl-trig fn k (- (fl-val x))))) (t (fl-trig fn k x))))
(defun fl-sin (k x) (declare (xargs :guard t))     ; 16.9.180; 60559 9.2: sin(+-inf) = NaN
  (if (or (not (fl-fin-p x))) :nan (fl-odd :sin k x)))
(defun fl-tan (k x) (declare (xargs :guard t))     ; 16.9.193
  (if (or (not (fl-fin-p x))) :nan (fl-odd :tan k x)))
(defun fl-cos (k x) (declare (xargs :guard t))     ; 16.9.55
  (cond ((not (fl-fin-p x)) :nan) ((fl-zero-p x) 1) (t (fl-trig :cos k (abs (fl-val x))))))
(defun fl-atan (k x) (declare (xargs :guard t))    ; 16.9.20; atan(+-inf) = +-pi/2
  (case x (:nan :nan) (:pinf (fl-trig :pim k 1/2)) (:ninf (fl-neg (fl-trig :pim k 1/2)))
    (otherwise (if (fl-fin-p x) (fl-odd :atan k x) :nan))))

(defun fl-atan2 (k y x)              ; 16.9.21 ATAN2 (Y, X); 60559 9.2.1's special cases
  (declare (xargs :guard t))
  (if (not (and (fl-x-p x) (fl-x-p y) (not (eq x :nan)) (not (eq y :nan)))) :nan
    (let ((m (cond ((fl-zero-p y) (if (fl-neg-p x) (fl-trig :pim k 1) 0))
                   ((fl-inf-p y) (case x (:pinf (fl-trig :pim k 1/4)) (:ninf (fl-trig :pim k 3/4)) (otherwise (fl-trig :pim k 1/2))))
                   ((fl-zero-p x) (fl-trig :pim k 1/2))
                   ((eq x :pinf) 0) ((eq x :ninf) (fl-trig :pim k 1))
                   (t (fl-trig (if (< 0 (fl-val x)) :atan :patan) k (abs (/ (fl-val y) (fl-val x))))))))
      (if (fl-neg-p y) (fl-neg m) m))))

(assert-event (equal (fl-sin 8 1) 3789648413623927/4503599627370496))      ; 0.8414709848078965
(assert-event (equal (fl-cos 8 1) 1216652631687587/2251799813685248))      ; 0.5403023058681398
(assert-event (equal (fl-sin 8 :nzero) :nzero))
(assert-event (equal (fl-cos 8 :pinf) :nan))
