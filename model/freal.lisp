; freal: real arithmetic for fmean (Stage A, item 2): the binary32 and
; binary64 formats of ISO/IEC 60559 (IEEE 754), kinds 4 and 8, with
; round-to-nearest-even, signed zeros, infinities and NaN.
;
; What the standard says, and what it leaves to the processor:
;   - A real kind's values are the processor's (19.3.?, 16.4). With
;     IEEE_SUPPORT_DATATYPE true (gfortran and flang, kinds 4 and 8) the
;     normal numbers are exactly an ISO/IEC 60559 format, and + - * conform
;     for at least one rounding mode (17.1); / and SQRT conform where
;     IEEE_SUPPORT_DIVIDE and IEEE_SUPPORT_SQRT are true (17.?, item 5, 6),
;     infinities, NaNs and subnormals where IEEE_SUPPORT_INF, _NAN and
;     _SUBNORMAL are (items 2-4). Both compilers answer true for all of
;     them on kinds 4 and 8, round to nearest by default, and do not trap.
;     The model is that processor.
;   - 10.1.5.2.4p2: the processor may evaluate any mathematically
;     equivalent expression, parentheses kept. The model evaluates the
;     interpretation the expression's form establishes (10.1.5), one
;     rounding per operation, as gfortran and flang do without -ffast-math
;     and with -ffp-contract=off (flang -O2 fuses a*b + c into one fused
;     multiply-add by default, parentheses or not, which that paragraph
;     allows: check-fsem compiles with -ffp-contract=off).
;   - What the standard gives only as a processor-dependent approximation
;     -- SIN, EXP, LOG and the rest (16.9), x**y of reals, SUM and PRODUCT
;     of reals once a rounding happens (16.9.201, 16.9.165), MAX and MIN
;     and SIGN where a NaN or two zeros of either sign leave the choice
;     open (16.9.135, 16.9.141, 16.9.189) -- fmean answers :pd, a
;     processor-dependent value, and check-fsem records what each
;     compiler printed there.
;
; A real value's representation x: a rational (a finite value of the
; format, +0 as 0), or :nzero (-0), :pinf, :ninf, :nan.

(in-package "ACL2")

(defun rkind-p (k) (declare (xargs :guard t)) (and (member k '(4 8)) t))
(defun fl-prec (k) (declare (xargs :guard t)) (if (equal k 4) 24 53))       ; p
(defun fl-emin (k) (declare (xargs :guard t)) (if (equal k 4) -126 -1022))
(defun fl-emax (k) (declare (xargs :guard t)) (if (equal k 4) 127 1023))

(defun fl-special-p (x) (declare (xargs :guard t)) (and (member-eq x '(:nzero :pinf :ninf :nan)) t))
(defun fl-x-p (x) (declare (xargs :guard t)) (or (rationalp x) (fl-special-p x)))
(defun fl-inf-p (x) (declare (xargs :guard t)) (or (eq x :pinf) (eq x :ninf)))
(defun fl-fin-p (x) (declare (xargs :guard t)) (or (rationalp x) (eq x :nzero)))
(defun fl-val (x) (declare (xargs :guard t)) (if (rationalp x) x 0))       ; a finite value's number
(defun fl-neg-p (x)                  ; the sign bit (a NaN's is not looked at)
  (declare (xargs :guard t))
  (or (eq x :nzero) (eq x :ninf) (and (rationalp x) (< x 0))))
(defun fl-zero-p (x) (declare (xargs :guard t)) (or (eq x :nzero) (equal x 0)))

; floor(log2 a), a a positive rational: n/d lies in (2^(e-1), 2^(e+1))
; for e the difference of their lengths
(defun flog2 (a)
  (declare (xargs :guard (and (rationalp a) (< 0 a))))
  (let ((e (- (integer-length (numerator a)) (integer-length (denominator a)))))
    (if (< a (expt 2 e)) (- e 1) e)))

(defun rne (m)                       ; m >= 0 to the nearest integer, ties to even
  (declare (xargs :guard (rationalp m)))
  (let* ((f (floor m 1)) (r (- m f)))
    (cond ((< r 1/2) f) ((< 1/2 r) (+ f 1)) ((evenp f) f) (t (+ f 1)))))

; the value of the format nearest q (ties to even), q a rational: a
; nonzero q that rounds to zero keeps its sign, one too large is an
; infinity (ISO/IEC 60559 4.3.1, 7.4)
(defun fl-round (k q)
  (declare (xargs :guard (rationalp q)))
  (if (or (not (rationalp q)) (= q 0)) 0
    (let* ((a (abs q)) (p (fl-prec k))
           (e (max (flog2 a) (fl-emin k)))
           (ulp (expt 2 (- e (- p 1))))
           (v (* (rne (/ a ulp)) ulp)))
      (cond ((<= (expt 2 (+ 1 (fl-emax k))) v) (if (< q 0) :ninf :pinf))
            ((= v 0) (if (< q 0) :nzero 0))
            (t (if (< q 0) (- v) v))))))

(defun fl-neg (x)
  (declare (xargs :guard t))
  (case x (:nan :nan) (:pinf :ninf) (:ninf :pinf) (:nzero 0)
    (otherwise (if (equal x 0) :nzero (if (rationalp x) (- x) :nan)))))

(defun fl-signed-zero (neg) (declare (xargs :guard t)) (if neg :nzero 0))

(defun fl-add (k a b)
  (declare (xargs :guard t))
  (cond ((or (eq a :nan) (eq b :nan) (not (fl-x-p a)) (not (fl-x-p b))) :nan)
        ((and (fl-inf-p a) (fl-inf-p b)) (if (eq a b) a :nan))
        ((fl-inf-p a) a)
        ((fl-inf-p b) b)
        (t (let ((q (+ (fl-val a) (fl-val b))))
             ; an exact zero sum is +0, unless both were -0 (6.3)
             (if (= q 0) (fl-signed-zero (and (eq a :nzero) (eq b :nzero))) (fl-round k q))))))
(defun fl-sub (k a b) (declare (xargs :guard t)) (fl-add k a (fl-neg b)))

(defun fl-xor-neg (a b) (declare (xargs :guard t)) (not (equal (fl-neg-p a) (fl-neg-p b))))

(defun fl-mul (k a b)
  (declare (xargs :guard t))
  (cond ((or (eq a :nan) (eq b :nan) (not (fl-x-p a)) (not (fl-x-p b))) :nan)
        ((or (fl-inf-p a) (fl-inf-p b))
         (if (or (fl-zero-p a) (fl-zero-p b)) :nan (if (fl-xor-neg a b) :ninf :pinf)))
        (t (let ((q (* (fl-val a) (fl-val b))))
             (if (= q 0) (fl-signed-zero (fl-xor-neg a b)) (fl-round k q))))))

(defun fl-div (k a b)
  (declare (xargs :guard t))
  (cond ((or (eq a :nan) (eq b :nan) (not (fl-x-p a)) (not (fl-x-p b))) :nan)
        ((fl-inf-p a) (if (fl-inf-p b) :nan (if (fl-xor-neg a b) :ninf :pinf)))
        ((fl-inf-p b) (fl-signed-zero (fl-xor-neg a b)))
        ((fl-zero-p b) (if (fl-zero-p a) :nan (if (fl-xor-neg a b) :ninf :pinf)))
        ((fl-zero-p a) (fl-signed-zero (fl-xor-neg a b)))
        (t (fl-round k (/ (fl-val a) (fl-val b))))))

; the integer square root, bit by bit from the top: i steps
(defun isqrt-aux (n i r)
  (declare (xargs :guard t :measure (nfix i)))
  (if (not (posp i)) r
    (let ((c (+ (nfix r) (expt 2 (- i 1)))))
      (isqrt-aux n (- i 1) (if (<= (* c c) (nfix n)) c r)))))
(defun isqrt-bits (n) (declare (xargs :guard t)) (+ 1 (floor (integer-length (nfix n)) 2)))
(defun fl-isqrt (n) (declare (xargs :guard t)) (isqrt-aux (nfix n) (isqrt-bits n) 0))

; SQRT correctly rounded (ISO/IEC 60559 5.4.1, 17.? item 6): a scaled by
; 4^j has an integer square root S of p + 3 bits at least; between S and
; S + 1 there is no rounding boundary of the format, so S + 1/2 stands for
; an inexact root
(defun fl-sqrt (k x)
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (eq x :ninf) (not (fl-x-p x))) :nan)
        ((eq x :pinf) :pinf)
        ((eq x :nzero) :nzero)
        ((equal x 0) 0)
        ((< x 0) :nan)
        (t (let* ((j (- (+ (fl-prec k) 3) (floor (flog2 x) 2)))
                  (y (* x (expt 4 j)))
                  (s (fl-isqrt (floor y 1)))
                  (exact (and (integerp y) (= (* s s) y))))
             (fl-round k (/ (if exact s (+ s 1/2)) (expt 2 j)))))))

(defun fl-abs (x)
  (declare (xargs :guard t))
  (cond ((eq x :nan) :nan) ((fl-inf-p x) :pinf) ((eq x :nzero) 0) ((rationalp x) (abs x)) (t :nan)))

; comparisons (10.1.5.5, ISO/IEC 60559 5.11): a NaN is unordered, the
; zeros are equal
(defun fl-less (a b)
  (declare (xargs :guard t))
  (cond ((or (eq a :nan) (eq b :nan) (not (fl-x-p a)) (not (fl-x-p b))) nil)
        ((eq a :ninf) (not (eq b :ninf)))
        ((eq b :pinf) (not (eq a :pinf)))
        ((or (eq a :pinf) (eq b :ninf)) nil)
        (t (< (fl-val a) (fl-val b)))))
(defun fl-eql (a b)
  (declare (xargs :guard t))
  (cond ((or (eq a :nan) (eq b :nan) (not (fl-x-p a)) (not (fl-x-p b))) nil)
        ((or (fl-inf-p a) (fl-inf-p b)) (eq a b))
        (t (= (fl-val a) (fl-val b)))))

(defun fl-conv (k x)                 ; to kind k: the nearest value (10.2.1.3, 16.9.170)
  (declare (xargs :guard t))
  (if (rationalp x) (fl-round k x) (if (fl-special-p x) x :nan)))

; to an integer: INT truncates, NINT rounds half away from zero, FLOOR,
; CEILING (16.9.110, 16.9.153, 16.9.80, 16.9.39); nil for an infinity or
; a NaN, which no integer is
(defun fl-to-int (mode x)
  (declare (xargs :guard t))
  (if (not (fl-fin-p x)) nil
    (let ((v (fl-val x)))
      (case mode
        (:floor (floor v 1))
        (:ceiling (ceiling v 1))
        (:nint (if (< v 0) (- (floor (+ (- v) 1/2) 1)) (floor (+ v 1/2) 1)))
        (otherwise (truncate v 1))))))

; the model numbers' extremes (16.9.96 HUGE, 16.9.210 TINY, 16.9.76 EPSILON)
(defun fl-huge (k) (declare (xargs :guard t)) (* (- 2 (expt 2 (- 1 (fl-prec k)))) (expt 2 (fl-emax k))))
(defun fl-tiny (k) (declare (xargs :guard t)) (expt 2 (fl-emin k)))
(defun fl-epsilon (k) (declare (xargs :guard t)) (expt 2 (- 1 (fl-prec k))))

; MOD (A, P) for reals is A - INT (A/P) * P (16.9.145): exactly
; representable when A and P are, so here exact (as fmod is)
(defun fl-mod (k a p)
  (declare (xargs :guard t))
  (cond ((or (not (fl-fin-p a)) (not (fl-fin-p p)) (fl-zero-p p)) :nan)
        (t (let ((r (- (fl-val a) (* (truncate (/ (fl-val a) (fl-val p)) 1) (fl-val p)))))
             (if (= r 0) (fl-signed-zero (fl-neg-p a)) (fl-round k r))))))

; ---- cost: the integer square root takes isqrt-bits steps, half the
; length of its argument, plus one

(defun isqrt-steps (n i r)
  (declare (xargs :guard t :measure (nfix i)) (irrelevant n r))
  (if (not (posp i)) 1
    (let ((c (+ (nfix r) (expt 2 (- i 1)))))
      (+ 1 (isqrt-steps n (- i 1) (if (<= (* c c) (nfix n)) c r))))))
(defthm isqrt-cost (equal (isqrt-steps n i r) (+ 1 (nfix i))))
(defthm fl-isqrt-cost       ; floor(length(n)/2) + 2 steps
  (equal (isqrt-steps (nfix n) (isqrt-bits n) 0) (+ 2 (floor (integer-length (nfix n)) 2))))

; ---- tests: known values of the formats

(assert-event (equal (fl-round 8 1/10) 3602879701896397/36028797018963968))   ; 0.1d0
(assert-event (equal (fl-round 4 1/10) 13421773/134217728))                   ; 0.1
(assert-event (equal (fl-add 8 (fl-round 8 1/10) (fl-round 8 2/10)) 1351079888211149/4503599627370496)) ; 0.30000000000000004
(assert-event (equal (fl-round 8 (+ (expt 2 53) 1)) (expt 2 53)))             ; a tie, to even
(assert-event (equal (fl-round 8 (+ (expt 2 53) 3)) (+ (expt 2 53) 4)))
(assert-event (equal (fl-mul 8 (fl-huge 8) 2) :pinf))
(assert-event (equal (fl-round 8 (expt 2 -1074)) (expt 2 -1074)))             ; the least subnormal
(assert-event (equal (fl-round 8 (expt 2 -1075)) 0))                          ; half of it: a tie, to even 0
(assert-event (equal (fl-round 8 (- (expt 2 -1076))) :nzero))
(assert-event (equal (fl-div 8 1 0) :pinf))
(assert-event (equal (fl-div 8 1 :nzero) :ninf))
(assert-event (equal (fl-div 8 0 0) :nan))
(assert-event (equal (fl-add 8 :nzero :nzero) :nzero))
(assert-event (equal (fl-add 8 1 -1) 0))
(assert-event (equal (fl-sqrt 8 2) 6369051672525773/4503599627370496))         ; sqrt(2d0)
(assert-event (equal (fl-sqrt 8 :nzero) :nzero))
(assert-event (equal (fl-sqrt 8 -1) :nan))
(assert-event (equal (fl-sqrt 4 2) 11863283/8388608))
(assert-event (equal (fl-sqrt 8 (expt 2 -1074)) (expt 2 -537)))
(assert-event (not (fl-less :nan 1)))
(assert-event (fl-eql 0 :nzero))
(assert-event (equal (fl-to-int :nint -5/2) -3))
(assert-event (equal (fl-mod 8 -7 2) -1))
