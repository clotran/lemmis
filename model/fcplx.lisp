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
(include-book "fhyp")
(local (include-book "arithmetic-5/top" :dir :system))

(defun cq-cmp (s sx b)               ; sign of t - b: 1, 0, -1 (s >= 0, b >= 0)
  (declare (xargs :guard (and (rationalp s) (rationalp sx) (rationalp b))))
  (let ((c (- (* 2 b b) sx)))
    (cond ((< c 0) 1) ((< (* c c) s) 1) ((= (* c c) s) 0) (t -1))))

(defun cq-exp (s sx lo hi)           ; largest e in [lo, hi) with t >= 2^e, given t >= 2^lo, t < 2^hi
  (declare (xargs :guard (and (rationalp s) (rationalp sx) (integerp lo) (integerp hi))
                  :measure (nfix (- hi lo))))
  (if (or (not (integerp lo)) (not (integerp hi)) (<= (- hi lo) 1)) lo
    (let ((m (floor (+ lo hi) 2)))
      (if (<= 0 (cq-cmp s sx (expt 2 m))) (cq-exp s sx m hi) (cq-exp s sx lo m)))))

(defun cq-refine (k s sx lo hi fuel) ; lo <= t <= hi; nil when fuel runs out
  (declare (xargs :guard (and (rationalp s) (rationalp sx) (rationalp lo) (rationalp hi) (natp fuel))
                  :measure (nfix fuel)))
  (cond ((equal (fl-round k lo) (fl-round k hi)) (fl-round k lo))
        ((zp fuel) nil)
        (t (let* ((m (/ (+ lo hi) 2)) (c (cq-cmp s sx m)))
             (cond ((= c 0) (fl-round k m))
                   ((= c 1) (cq-refine k s sx m hi (- fuel 1)))
                   (t (cq-refine k s sx lo m (- fuel 1))))))))

(defun cq-root (k s sx)              ; t rounded, or nil
  (declare (xargs :guard (and (rationalp s) (rationalp sx))))
  (let ((lo (- (- (fl-emin k) (fl-prec k)) 2)))
    (cond ((< (cq-cmp s sx (expt 2 lo)) 0) 0)      ; below half the least subnormal
          (t (let ((e (cq-exp s sx lo (+ (fl-emax k) 2))))
               (if (= (cq-cmp s sx (expt 2 e)) 0) (fl-round k (expt 2 e))
                 (cq-refine k s sx (expt 2 e) (expt 2 (+ e 1)) 400)))))))

(defun fl-csqrt (k x y)              ; (re . im) of the principal root, or :pd
  (declare (xargs :guard t))
  (let ((a (fl-val x)) (b (fl-val y)))
    (cond ((not (and (rkind-p k) (fl-fin-p x) (fl-fin-p y))) :pd)
          ((fl-zero-p y)
           (cond ((fl-zero-p x) (cons 0 y))
                 ((< 0 a) (cons (fl-sqrt k a) y))
                 (t (cons 0 (let ((r (fl-sqrt k (- a)))) (if (fl-neg-p y) (fl-neg r) r))))))
          (t (let* ((s (+ (* a a) (* b b))) (re (cq-root k s a)) (im (cq-root k s (- a))))
               (if (and re im) (cons re (if (fl-neg-p y) (fl-neg im) im)) :pd))))))

(assert-event (equal (fl-csqrt 4 3 4) '(2 . 1)))
(assert-event (equal (fl-csqrt 4 -4 0) '(0 . 2)))
(assert-event (equal (fl-csqrt 4 -4 :nzero) (cons 0 -2)))
(assert-event (equal (fl-csqrt 4 0 2) '(1 . 1)))
(assert-event (equal (fl-csqrt 8 1 1) (cons 4948033364011513/4503599627370496 1024771263224069/2251799813685248)))
(assert-event (equal (fl-csqrt 8 :pinf 1) :pd))

;; ---- CEXP CLOG CSIN CCOS (16.9.74, .120, .180, .55), correctly rounded in each part ----
;
; Each part is a product of two real factors (cexp: e^x cos y, e^x sin y;
; csin: sin x cosh y, cos x sinh y; ccos: cos x cosh y, -(sin x sinh y)), each
; enclosed at depth j by the real books' enclosures (fintr xe-lo/hi, ftrig
; trig-lo/hi, fhyp hy-lo/hi). No differences, so no cancellation: the product
; of the factor intervals shrinks to the true part, which is nonzero (a factor
; of a rational nonzero argument is transcendental), and a depth decides when
; the product interval has one strict sign and both ends round alike (tval).
; A zero argument makes sin/sinh an exact signed zero and cos/cosh/exp an exact
; 1; a zero part's sign is the IEEE product's (C99 Annex G's for these cases).
; CLOG: (log|z|, atan2(y, x)); log|z| = log(x^2+y^2)/2 by fintr's |LOG|
; enclosure (+0 for |z| = 1), the imaginary part is ftrig's fl-atan2.
; Depths 0..8 (fl-trig's search); none decides, or a part overflows, or an
; argument of exp/sinh/cosh is past 1000 in magnitude, or an infinity/NaN: :pd.

(defun cx-fac (fn x j)               ; factor fn(x), x finite: (lo . hi), or (:z . neg) an exact signed zero
  (declare (xargs :guard t))
  (let* ((a (fl-val x)) (b (abs a)))
    (cond ((fl-zero-p x) (if (member-eq fn '(:sin :sinh)) (cons :z (fl-neg-p x)) '(1 . 1)))
          ((eq fn :exp) (cons (xe-lo a (+ 3 (nfix j))) (xe-hi a (+ 3 (nfix j)))))
          (t (let ((iv (if (member-eq fn '(:sin :cos)) (cons (trig-lo fn b j) (trig-hi fn b j))
                         (cons (hy-lo fn b (+ 3 (nfix j))) (hy-hi fn b (+ 3 (nfix j)))))))
               (if (and (< a 0) (member-eq fn '(:sin :sinh))) (ineg iv) iv))))))

(defun cx-sgn (f)                    ; :pos :neg of a factor, nil undecided
  (declare (xargs :guard t))
  (cond ((not (consp f)) nil)
        ((eq (car f) :z) (if (cdr f) :neg :pos))
        ((< 0 (rfix (car f))) :pos) ((< (rfix (cdr f)) 0) :neg) (t nil)))

(defun cx-iv (k lo hi)               ; the rounding of t in [lo, hi], or nil
  (declare (xargs :guard t))
  (let ((lo (rfix lo)) (hi (rfix hi)))
    (and (<= lo hi)
         (or (and (< 0 lo) (equal (fl-round k lo) (fl-round k hi)))
             (and (< hi 0) (equal (fl-round k (- hi)) (fl-round k (- lo)))))
         (tval k lo hi))))

(defun cx-part (k f g)               ; f g rounded, or nil
  (declare (xargs :guard t))
  (if (or (and (consp f) (eq (car f) :z)) (and (consp g) (eq (car g) :z)))
      (let ((s (cx-sgn f)) (u (cx-sgn g)))
        (and s u (if (eq s u) 0 :nzero)))
    (let* ((a (* (ilo f) (ilo g))) (b (* (ilo f) (ihi g))) (c (* (ihi f) (ilo g))) (d (* (ihi f) (ihi g))))
      (cx-iv k (min (min a b) (min c d)) (max (max a b) (max c d))))))

(defun cx-depth (fn k x y j)         ; (re . im) at depth j, or nil
  (declare (xargs :guard t))
  (let ((re (case fn
              (:exp (cx-part k (cx-fac :exp x j) (cx-fac :cos y j)))
              (:sin (cx-part k (cx-fac :sin x j) (cx-fac :cosh y j)))
              (:cos (cx-part k (cx-fac :cos x j) (cx-fac :cosh y j)))
              (otherwise (let ((s (+ (* (fl-val x) (fl-val x)) (* (fl-val y) (fl-val y)))))
                           (cond ((= s 1) 0)
                                 ((< 1 s) (cx-iv k (/ (lg-lo s (+ 3 (nfix j))) 2) (/ (lg-hi s (+ 3 (nfix j))) 2)))
                                 (t (cx-iv k (- (/ (lg-hi s (+ 3 (nfix j))) 2)) (- (/ (lg-lo s (+ 3 (nfix j))) 2)))))))))
        (im (case fn
              (:exp (cx-part k (cx-fac :exp x j) (cx-fac :sin y j)))
              (:sin (cx-part k (cx-fac :cos x j) (cx-fac :sinh y j)))
              (:cos (let ((v (cx-part k (cx-fac :sin x j) (cx-fac :sinh y j)))) (and v (fl-neg v))))
              (otherwise (fl-atan2 k y x)))))
    (and re im (cons re im))))

(defun cx-search (fn k x y j fuel)
  (declare (xargs :guard (natp j) :measure (nfix fuel)))
  (cond ((not (posp fuel)) :pd)
        ((cx-depth fn k x y j))
        (t (cx-search fn k x y (+ 1 j) (- fuel 1)))))

(defun fl-cfun (fn k x y)            ; fn :exp :log :sin :cos of x + iy: (re . im), or :pd
  (declare (xargs :guard t))
  (let ((r (if (and (rkind-p k) (fl-fin-p x) (fl-fin-p y)
                    (or (eq fn :log) (<= (abs (fl-val (if (eq fn :exp) x y))) 1000))
                    (not (and (eq fn :log) (fl-zero-p x) (fl-zero-p y))))
               (cx-search fn k x y 0 9) :pd)))
    (if (and (consp r) (fl-fin-p (car r)) (fl-fin-p (cdr r))) r :pd)))

; expected values: complex(16) (libquadmath) rounded to the format, ties even (bb, exact)
(assert-event (equal (fl-cfun :exp 8 1 1) (cons 3307204740263243/2251799813685248 1287666552375321/562949953421312)))
(assert-event (equal (fl-cfun :exp 8 -1 :nzero) (cons 828390857088487/2251799813685248 :nzero)))
(assert-event (equal (fl-cfun :exp 4 10 3) (cons -5582345/256 24867/8)))
(assert-event (equal (fl-cfun :exp 8 :pinf 0) :pd))
(assert-event (equal (fl-cfun :log 8 1 1) (cons 6243314768165359/18014398509481984 884279719003555/1125899906842624)))
(assert-event (equal (fl-cfun :log 8 -1 :nzero) (cons 0 -884279719003555/281474976710656)))
(assert-event (equal (fl-cfun :log 4 -3 1/4) (cons 4622427/4194304 12828075/4194304)))
(assert-event (equal (fl-cfun :log 8 0 :nzero) :pd))
