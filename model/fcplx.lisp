; fcplx: CSQRT of a complex (16.9.191), correctly rounded in each part.
;
; The standard gives it as a processor-dependent approximation; the model
; pins it the way fintr pins EXP: each part is the true value rounded
; (fl-round, ties to even). With s = x^2 + y^2 (exact), the parts are
; t = sqrt((sqrt(s) + sx)/2), sx = x (real part) or -x (|imaginary part|).
; "t versus a rational b >= 0" is decided exactly (t > b iff sqrt(s) > 2b^2
; - sx, then compare squares), so no series: t is bracketed by bisection of
; [2^e, 2^(e+1)) until both ends round to one value; t = a bisection point
; is caught by the exact comparison. Fuel out (a near-tie closer than 2^-400
; relative): :pd, the processor-dependent value.
; The sign of a zero part is C99's csqrt: the imaginary part has the sign of
; Y; (+0, Y) for X = +-0, Y = +-0. Infinities and NaN: :pd.

(in-package "ACL2")
(include-book "freal")
(local (include-book "arithmetic-5/top" :dir :system))

(defun cs-cmp (s sx b)               ; sign of t - b: 1, 0, -1 (s >= 0, b >= 0)
  (declare (xargs :guard (and (rationalp s) (rationalp sx) (rationalp b))))
  (let ((c (- (* 2 b b) sx)))
    (cond ((< c 0) 1) ((< (* c c) s) 1) ((= (* c c) s) 0) (t -1))))

(defun cs-exp (s sx lo hi)           ; largest e in [lo, hi) with t >= 2^e, given t >= 2^lo, t < 2^hi
  (declare (xargs :guard (and (rationalp s) (rationalp sx) (integerp lo) (integerp hi))
                  :measure (nfix (- hi lo))))
  (if (or (not (integerp lo)) (not (integerp hi)) (<= (- hi lo) 1)) lo
    (let ((m (floor (+ lo hi) 2)))
      (if (<= 0 (cs-cmp s sx (expt 2 m))) (cs-exp s sx m hi) (cs-exp s sx lo m)))))

(defun cs-refine (k s sx lo hi fuel) ; lo <= t <= hi; nil when fuel runs out
  (declare (xargs :guard (and (rationalp s) (rationalp sx) (rationalp lo) (rationalp hi) (natp fuel))
                  :measure (nfix fuel)))
  (cond ((equal (fl-round k lo) (fl-round k hi)) (fl-round k lo))
        ((zp fuel) nil)
        (t (let* ((m (/ (+ lo hi) 2)) (c (cs-cmp s sx m)))
             (cond ((= c 0) (fl-round k m))
                   ((= c 1) (cs-refine k s sx m hi (- fuel 1)))
                   (t (cs-refine k s sx lo m (- fuel 1))))))))

(defun cs-root (k s sx)              ; t rounded, or nil
  (declare (xargs :guard (and (rationalp s) (rationalp sx))))
  (let ((lo (- (- (fl-emin k) (fl-prec k)) 2)))
    (cond ((< (cs-cmp s sx (expt 2 lo)) 0) 0)      ; below half the least subnormal
          (t (let ((e (cs-exp s sx lo (+ (fl-emax k) 2))))
               (if (= (cs-cmp s sx (expt 2 e)) 0) (fl-round k (expt 2 e))
                 (cs-refine k s sx (expt 2 e) (expt 2 (+ e 1)) 400)))))))

(defun fl-csqrt (k x y)              ; (re . im) of the principal root, or :pd
  (declare (xargs :guard t))
  (let ((a (fl-val x)) (b (fl-val y)))
    (cond ((not (and (rkind-p k) (fl-fin-p x) (fl-fin-p y))) :pd)
          ((fl-zero-p y)
           (cond ((fl-zero-p x) (cons 0 y))
                 ((< 0 a) (cons (fl-sqrt k a) y))
                 (t (cons 0 (let ((r (fl-sqrt k (- a)))) (if (fl-neg-p y) (fl-neg r) r))))))
          (t (let* ((s (+ (* a a) (* b b))) (re (cs-root k s a)) (im (cs-root k s (- a))))
               (if (and re im) (cons re (if (fl-neg-p y) (fl-neg im) im)) :pd))))))

(assert-event (equal (fl-csqrt 4 3 4) '(2 . 1)))
(assert-event (equal (fl-csqrt 4 -4 0) '(0 . 2)))
(assert-event (equal (fl-csqrt 4 -4 :nzero) (cons 0 -2)))
(assert-event (equal (fl-csqrt 4 0 2) '(1 . 1)))
(assert-event (equal (fl-csqrt 8 1 1) (cons 4948033364011513/4503599627370496 1024771263224069/2251799813685248)))
(assert-event (equal (fl-csqrt 8 :pinf 1) :pd))
