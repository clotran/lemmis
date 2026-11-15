; fhyp: ASIN, ACOS, SINH, COSH, TANH, LOG10 of a real (16.9.17, .4, .183, .54, .195, .121),
; correctly rounded, the way ftrig.lisp does SIN ... ATAN2: no composition of
; rounded operations.  For a = |x| (or x for LOG10) the true value t is
; enclosed by a rational interval at each depth j, built from the existing
; pieces: the EXP enclosure of fintr (SINH (e^a - e^-a)/2, COSH (e^a + e^-a)/2,
; TANH (E-1)/(E+1), E = e^2a), the |LOG| enclosure of fintr (LOG10 =
; |log x| / log 10, an interval quotient), and ftrig's ATAN enclosure and pi
; (ASIN a = atan(a / sqrt(1-a^2)), the sqrt rounded outward to g+64 bits;
; ACOS a = pi/2 -+ asin).  The enclosure the constraint uses is the hull of
; depths 0..j (as in ftrig); a deciding depth has lo > 0 and both ends round alike.
;
; PROVED here: sq-sound (the outward sqrt bounds: lo^2 <= q <= hi^2, by
; construction with runtime checks, no isqrt proof needed), and for SINH, COSH,
; TANH, LOG10 that every depth's lower end is below every depth's upper end
; (sinh-sound ... log10-sound), from enc-sound and interval monotonicity; the
; correctly-rounded theorem fl-hyp-correctly-rounded, and tdec-agree-style
; agreement of any two deciding depths (hdec-agree, from hull monotonicity).
; NOT PROVED (no reals): that the true value lies in every enclosure (what
; "enclosure" means), as in ftrig; for ASIN/ACOS additionally that atan
; is monotone, i.e. lo(atan yl) <= atan a/sqrt(1-a^2) <= hi(atan yh)
; (argued, not proved: no cross-depth atan soundness at different arguments).
; The thresholds are arguments of the model: SINH/COSH |x| > 1000 overflow
; (e^1000 > 2^1442), TANH |x| > 25 rounds to 1 (1 - 2e^-50 is within 2^-54 of 1).

(in-package "ACL2")
(include-book "ftrig")
(local (include-book "arithmetic-5/top" :dir :system))

(defun hn (j) (declare (xargs :guard t)) (* 4 (expt 2 (nfix j))))
(defun xe-lo (x j) (declare (xargs :guard t)) (enc-lo :exp x (hn j)))
(defun xe-hi (x j) (declare (xargs :guard t)) (rfix (enc-hi :exp x (hn j))))
(defun lg-lo (x j) (declare (xargs :guard t)) (enc-lo :log x (hn j)))
(defun lg-hi (x j) (declare (xargs :guard t)) (rfix (enc-hi :log x (hn j))))

;; ---- the square root, outward -------------------------------------------------

(defun sq-n (q b) (declare (xargs :guard t)) (floor (* (rfix q) (expt 2 (nfix b)) (expt 2 (nfix b))) 1))
(defun sq-lo (q b)                   ; <= sqrt q, 0 <= q
  (declare (xargs :guard t))
  (let ((s (fl-isqrt (sq-n q b))))
    (if (<= (* s s) (sq-n q b)) (/ s (expt 2 (nfix b))) 0)))
(defun sq-hi (q b)                   ; >= sqrt q, 0 <= q < 1 (the fallback 1)
  (declare (xargs :guard t))
  (let ((s (+ 1 (fl-isqrt (sq-n q b)))))
    (if (< (sq-n q b) (* s s)) (/ s (expt 2 (nfix b))) 1)))

(defthm isqrt-aux-nat (implies (natp r) (natp (isqrt-aux n i r))) :rule-classes :type-prescription)
(defthm fl-isqrt-nat (natp (fl-isqrt n)) :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fl-isqrt))))
(defthm sq-n-int (integerp (sq-n q b)) :rule-classes :type-prescription)
(defthm sq-n-le (<= (sq-n q b) (* (rfix q) (expt 2 (nfix b)) (expt 2 (nfix b)))) :rule-classes :linear)
(defthm sq-n-gt (< (* (rfix q) (expt 2 (nfix b)) (expt 2 (nfix b))) (+ 1 (sq-n q b))) :rule-classes :linear)
(in-theory (disable sq-n))
(defthm two-pos (< 0 (expt 2 (nfix b))) :rule-classes :type-prescription)
(defthm mult-le (implies (and (rationalp a) (rationalp x) (rationalp y) (<= 0 a) (<= x y)) (<= (* a x) (* a y)))
  :hints (("Goal" :nonlinearp t)))
(defthm sq-step (implies (and (rationalp u) (< 0 u) (rationalp q) (integerp s) (<= (* s s) n) (<= n (* q u u)))
                         (<= (* (/ s u) (/ s u)) q))
  :hints (("Goal" :in-theory (disable mult-le) :use ((:instance mult-le (a (/ (* u u))) (x (* s s)) (y (* q u u)))))))
(defthm sq-step2 (implies (and (rationalp u) (< 0 u) (rationalp q) (integerp s) (< (* q u u) n) (<= n (* s s)))
                         (<= q (* (/ s u) (/ s u))))
  :hints (("Goal" :in-theory (disable mult-le) :use ((:instance mult-le (a (/ (* u u))) (x (* q u u)) (y (* s s)))))))
(defthm sq-sound
  (implies (and (rationalp q) (<= 0 q) (< q 1))
           (and (<= (* (sq-lo q b) (sq-lo q b)) q) (<= 0 (sq-lo q b))
                (<= q (* (sq-hi q b) (sq-hi q b))) (< 0 (sq-hi q b))))
  :hints (("Goal" :in-theory (disable fl-isqrt-nat sq-n-le sq-n-gt sq-step sq-step2 two-pos)
                  :use (sq-n-le sq-n-gt (:instance sq-step (u (expt 2 (nfix b))) (s (fl-isqrt (sq-n q b))) (n (sq-n q b)))
                        (:instance sq-step2 (u (expt 2 (nfix b))) (s (+ 1 (fl-isqrt (sq-n q b)))) (n (+ 1 (sq-n q b))))))))

;; ---- the enclosures -------------------------------------------------------------

(defun asin-iv (a j)                 ; atan(a / sqrt(1-a^2)), 0 < a < 1
  (declare (xargs :guard t))
  (let* ((a (rfix a)) (b (+ (* 64 (expt 2 (nfix j))) 64)) (q (- 1 (* a a)))
         (sl (sq-lo q b)) (sh (sq-hi q b))
         (yl (qdiv a sh)) (yh (if (< 0 sl) (/ a sl) (expt 2 4000))))
    (cons (ilo (trig-raw :atan yl j)) (ihi (trig-raw :atan yh j)))))

(defun hy-raw (fn x j)               ; x > 0: :sinh :cosh :tanh :log10 :asin, acos x (:acosp), acos -x (:acosn)
  (declare (xargs :guard t))
  (let ((x (rfix x)))
    (case fn
      (:sinh (cons (/ (- (xe-lo x j) (xe-hi (- x) j)) 2) (/ (- (xe-hi x j) (xe-lo (- x) j)) 2)))
      (:cosh (cons (/ (+ (xe-lo x j) (xe-lo (- x) j)) 2) (/ (+ (xe-hi x j) (xe-hi (- x) j)) 2)))
      (:tanh (let ((el (xe-lo (* 2 x) j)) (eh (xe-hi (* 2 x) j)))
               (cons (- 1 (qdiv 2 (+ el 1))) (- 1 (qdiv 2 (+ eh 1))))))
      (:log10 (cons (qdiv (lg-lo x j) (lg-hi 10 j)) (qdiv (lg-hi x j) (lg-lo 10 j))))
      (:asin (asin-iv x j))
      (otherwise (let ((s (asin-iv x j)) (p (trig-raw :pim 1/2 j)))
                   (if (eq fn :acosp) (cons (- (ilo p) (ihi s)) (- (ihi p) (ilo s)))
                     (cons (+ (ilo p) (ilo s)) (+ (ihi p) (ihi s)))))))))

;; soundness of the exp/log pieces: every depth's lower end is below every depth's upper end
(defthm xe-hi-rat (implies (and (rationalp x) (<= x 1000)) (enc-hi :exp x (hn j)))
  :hints (("Goal" :in-theory (enable enc-hi) :expand ((enc-hi :exp x (hn j))))))
(defthm lg-hi-rat (implies (and (rationalp x) (< 0 x)) (enc-hi :log x (hn j)))
  :hints (("Goal" :in-theory (enable enc-hi) :expand ((enc-hi :log x (hn j))))))

(defthm xe-sound (implies (and (rationalp x) (<= x 1000) (natp j) (natp k)) (<= (xe-lo x j) (xe-hi x k)))
  :hints (("Goal" :in-theory (disable enc-sound enc-lo enc-hi)
                  :use ((:instance enc-sound (fn :exp) (n (hn j)) (m (hn k))) xe-hi-rat (:instance xe-hi-rat (j k))))))
(defthm lg-sound (implies (and (rationalp x) (< 0 x) (natp j) (natp k)) (<= (lg-lo x j) (lg-hi x k)))
  :hints (("Goal" :in-theory (disable enc-sound enc-lo enc-hi)
                  :use ((:instance enc-sound (fn :log) (n (hn j)) (m (hn k))) (:instance lg-hi-rat (j k))))))
(defthm xe-lo-nonneg (<= 0 (xe-lo x j)) :rule-classes :linear
  :hints (("Goal" :use ((:instance enc-lo-type (fn :exp) (n (hn j)))) :in-theory (disable enc-lo-type))))
(defthm lg-lo-nonneg (<= 0 (lg-lo x j)) :rule-classes :linear
  :hints (("Goal" :use ((:instance enc-lo-type (fn :log) (n (hn j)))) :in-theory (disable enc-lo-type))))

(defthm sinh-sound
  (implies (and (rationalp x) (<= (abs x) 1000) (natp j) (natp k))
           (<= (ilo (hy-raw :sinh x j)) (ihi (hy-raw :sinh x k))))
  :hints (("Goal" :in-theory (disable xe-sound xe-lo xe-hi) :use (xe-sound (:instance xe-sound (x (- x)) (j k) (k j))))))
(defthm cosh-sound
  (implies (and (rationalp x) (<= (abs x) 1000) (natp j) (natp k))
           (<= (ilo (hy-raw :cosh x j)) (ihi (hy-raw :cosh x k))))
  :hints (("Goal" :in-theory (disable xe-sound xe-lo xe-hi) :use (xe-sound (:instance xe-sound (x (- x)))))))

(defthm inv-mono (implies (and (rationalp a) (rationalp b) (< 0 a) (<= a b)) (<= (/ b) (/ a)))
  :hints (("Goal" :nonlinearp t)))
(defthm tanh-sound
  (implies (and (rationalp x) (<= (abs x) 500) (natp j) (natp k))
           (<= (ilo (hy-raw :tanh x j)) (ihi (hy-raw :tanh x k))))
  :hints (("Goal" :in-theory (disable xe-sound xe-lo xe-hi inv-mono xe-lo-nonneg) :expand ((qdiv 2 (+ 1 (xe-lo (* 2 x) j))) (qdiv 2 (+ 1 (xe-hi (* 2 x) k))))
                  :use ((:instance xe-sound (x (* 2 x))) (:instance xe-lo-nonneg (x (* 2 x)))
                        (:instance inv-mono (a (+ 1 (xe-lo (* 2 x) j))) (b (+ 1 (xe-hi (* 2 x) k))))))))

(defthm quot-1 (implies (and (rationalp a) (rationalp d) (rationalp e) (<= 0 a) (< 0 d) (<= d e)) (<= (* a (/ e)) (* a (/ d))))
  :hints (("Goal" :in-theory (disable inv-mono mult-le) :use ((:instance inv-mono (a d) (b e)) (:instance mult-le (x (/ e)) (y (/ d)))))))
(defthm quot-2 (implies (and (rationalp a) (rationalp b) (rationalp d) (<= a b) (< 0 d)) (<= (* a (/ d)) (* b (/ d))))
  :hints (("Goal" :in-theory (disable mult-le) :use ((:instance mult-le (a (/ d)) (x a) (y b))))))
(defthm quot-step (implies (and (rationalp a) (rationalp b) (rationalp d) (rationalp e) (<= 0 a) (<= a b) (< 0 d) (<= d e))
                           (<= (/ a e) (/ b d)))
  :hints (("Goal" :in-theory (theory (quote minimal-theory)) :use ((:instance quot-1) (:instance quot-2)))))
(defthm lg-st-nn (implies (and (rationalp y) (<= 0 y)) (<= 0 (ser-term :log y i)))
  :hints (("Goal" :induct (ser-term :log y i) :in-theory (enable ser-ratio))))
(defthm lg-ss-ge (implies (and (rationalp y) (<= 0 y)) (<= y (ser-sum :log y n)))
  :hints (("Goal" :induct (ser-sum :log y n) :in-theory (disable ser-term lg-st-nn))
          ("Subgoal *1/2" :in-theory (enable ser-term) :use ((:instance lg-st-nn (i n))))
          ("Subgoal *1/1" :in-theory (enable ser-term))))
(defthm lg10-pos (< 0 (lg-lo 10 j)) :rule-classes :linear
  :hints (("Goal" :in-theory (disable ser-sum lg-ss-ge)
                  :use ((:instance lg-ss-ge (y 1/3) (n (hn j))) (:instance lg-ss-ge (y 1/9) (n (hn j)))))))
(defthm log10-sound
  (implies (and (rationalp x) (< 0 x) (natp j) (natp k))
           (<= (ilo (hy-raw :log10 x j)) (ihi (hy-raw :log10 x k))))
  :hints (("Goal" :in-theory (disable lg-sound lg-lo lg-hi quot-step lg-lo-nonneg lg10-pos)
                  :use (lg-lo-nonneg (:instance lg-sound (x 10) (j k) (k j)) lg-sound lg10-pos (:instance lg10-pos (j k))
                        (:instance quot-step (a (lg-lo x j)) (b (lg-hi x k)) (d (lg-lo 10 k)) (e (lg-hi 10 j)))))))

;; ---- the hull and the deciding depths ---------------------------------------------

(defun hy-hull (fn x j)
  (declare (xargs :guard t))
  (let ((r (hy-raw fn x j)))
    (if (not (posp j)) (cons (rfix (car r)) (rfix (cdr r)))
      (let ((h (hy-hull fn x (- j 1))))
        (cons (max (ilo h) (rfix (car r))) (min (ihi h) (rfix (cdr r))))))))
(in-theory (disable hy-hull))
(defun hy-lo (fn x j) (declare (xargs :guard t)) (ilo (hy-hull fn x j)))
(defun hy-hi (fn x j) (declare (xargs :guard t)) (ihi (hy-hull fn x j)))

(in-theory (disable hy-raw))
(defthm hy-hull-rational (and (rationalp (hy-lo fn x j)) (rationalp (hy-hi fn x j)))
  :hints (("Goal" :in-theory (enable ilo ihi) :expand ((hy-hull fn x j)))))
(in-theory (disable hy-lo hy-hi))

(local (defthm hull-step
  (implies (posp j) (and (<= (hy-lo fn x (+ -1 j)) (hy-lo fn x j)) (<= (hy-hi fn x j) (hy-hi fn x (+ -1 j)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable hy-lo hy-hi) :expand ((hy-hull fn x j))))))

(defthm hy-hull-mono                 ; the hull shrinks with the depth
  (implies (and (natp n) (natp m) (<= n m))
           (and (<= (hy-lo fn x n) (hy-lo fn x m)) (<= (hy-hi fn x m) (hy-hi fn x n))))
  :rule-classes nil
  :hints (("Goal" :induct (up-ind n m))))

(defun hdec (fn k x j)               ; 0 < lo <= hi, both ends round to one value
  (declare (xargs :guard t))
  (let ((lo (hy-lo fn x j)) (hi (hy-hi fn x j)))
    (and (< 0 lo) (<= lo hi) (equal (fl-round k lo) (fl-round k hi)))))
(defun hdec-val (fn k x j) (declare (xargs :guard t)) (fl-round k (hy-lo fn x j)))

(local (defthm hdec-agree-le
  (implies (and (natp n) (natp m) (<= n m) (hdec fn k x n) (hdec fn k x m))
           (equal (hdec-val fn k x m) (hdec-val fn k x n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fl-round)
                  :use (hy-hull-mono (:instance fl-round-convex (a (hy-lo fn x n)) (b (hy-lo fn x m)) (c (hy-hi fn x n))))))))

(defthm hdec-agree                   ; every deciding depth gives one value
  (implies (and (natp n) (natp m) (hdec fn k x n) (hdec fn k x m))
           (equal (hdec-val fn k x m) (hdec-val fn k x n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable hdec hdec-val) :cases ((<= n m))
                  :use (hdec-agree-le (:instance hdec-agree-le (n m) (m n))))))

(defchoose hdec-wit (j) (fn k x) (and (natp j) (hdec fn k x j)))
(defun hyp-wit (fn k x) (declare (xargs :guard t)) (hdec-val fn k x (nfix (hdec-wit fn k x))))

(defthm hyp-wit-ok
  (implies (and (natp j) (hdec fn k x j)) (equal (hyp-wit fn k x) (hdec-val fn k x j)))
  :hints (("Goal" :in-theory (disable hdec hdec-val)
                  :use ((:instance hdec-wit) (:instance hdec-agree (n j) (m (hdec-wit fn k x)))))))

; fl-hyp fn k x: the rounding of the true value (sinh x, cosh x, tanh x, log10 x,
; asin x, acos x, acos -x for fn :sinh :cosh :tanh :log10 :asin :acosp :acosn), N = 1/2
(encapsulate (((fl-hyp * * *) => *))
  (local (defun fl-hyp (fn k x) (hyp-wit fn k x)))
  (defthm fl-hyp-correctly-rounded
    (implies (and (natp j) (hdec fn k x j)) (equal (fl-hyp fn k x) (hdec-val fn k x j)))
    :hints (("Goal" :in-theory (disable hyp-wit hdec hdec-val)))))

(defun hyp-search (fn k x j fuel)    ; depths j, j+1, ...: fuel of them
  (declare (xargs :guard (natp j) :measure (nfix fuel)))
  (cond ((not (posp fuel)) (non-exec (hyp-wit fn k x)))         ; never reached: t is transcendental
        ((hdec fn k x j) (hdec-val fn k x j))
        (t (hyp-search fn k x (+ 1 (nfix j)) (- fuel 1)))))

(defthm hyp-search-ok
  (implies (natp j) (equal (hyp-search fn k x j fuel) (hyp-wit fn k x)))
  :hints (("Goal" :in-theory (disable hyp-wit hdec hdec-val))
          ("Subgoal *1/2" :use ((:instance hyp-wit-ok)))))

(defun fl-hyp-impl (fn k x) (declare (xargs :guard t)) (hyp-search fn k x 0 9))

(defattach (fl-hyp fl-hyp-impl) :hints (("Goal" :in-theory (disable hyp-search hdec hdec-val)
                                                :use ((:instance hyp-wit-ok) (:instance hyp-search-ok (j 0) (fuel 9))))))

;; ---- the intrinsics on values of the format ---------------------------------------

(defun fl-hodd (fn k x)              ; odd: f(-x) = -f(x), f(+-0) = +-0
  (declare (xargs :guard t))
  (cond ((fl-zero-p x) x) ((< (fl-val x) 0) (fl-neg (fl-hyp fn k (- (fl-val x))))) (t (fl-hyp fn k x))))

(defun fl-sinh (k x)                 ; 16.9.183; sinh(+-inf) = +-inf; |x| > 1000 overflows
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (not (fl-x-p x))) :nan) ((member x '(:pinf :ninf)) x)
        ((< 1000 (abs (fl-val x))) (if (< (fl-val x) 0) :ninf :pinf))
        (t (fl-hodd :sinh k x))))
(defun fl-cosh (k x)                 ; 16.9.54
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (not (fl-x-p x))) :nan) ((member x '(:pinf :ninf)) :pinf) ((fl-zero-p x) 1)
        ((< 1000 (abs (fl-val x))) :pinf)
        (t (fl-hyp :cosh k (abs (fl-val x))))))
(defun fl-tanh (k x)                 ; 16.9.195; tanh(+-inf) = +-1; |x| > 25 rounds to +-1
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (not (fl-x-p x))) :nan) ((eq x :pinf) 1) ((eq x :ninf) -1)
        ((fl-zero-p x) x)
        ((< 25 (abs (fl-val x))) (if (< (fl-val x) 0) -1 1))
        (t (fl-hodd :tanh k x))))
(defun fl-log10 (k x)                ; 16.9.121, as fl-log: log10(1) = +0
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (eq x :ninf) (not (fl-x-p x))) :nan)
        ((eq x :pinf) :pinf) ((fl-zero-p x) :ninf) ((< x 0) :nan) ((= x 1) 0)
        ((< x 1) (fl-neg (fl-hyp :log10 k x)))
        (t (fl-hyp :log10 k x))))
(defun fl-asin (k x)                 ; 16.9.17: |x| <= 1 (else NaN; el1 reports the domain error)
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (not (fl-fin-p x))) :nan) ((fl-zero-p x) x)
        ((< 1 (abs (fl-val x))) :nan)
        ((= (abs (fl-val x)) 1) (let ((m (fl-trig :pim k 1/2))) (if (< (fl-val x) 0) (fl-neg m) m)))
        (t (fl-hodd :asin k x))))
(defun fl-acos (k x)                 ; 16.9.4
  (declare (xargs :guard t))
  (cond ((or (eq x :nan) (not (fl-fin-p x))) :nan) ((fl-zero-p x) (fl-trig :pim k 1/2))
        ((< 1 (abs (fl-val x))) :nan)
        ((= (fl-val x) 1) 0) ((= (fl-val x) -1) (fl-trig :pim k 1))
        ((< 0 (fl-val x)) (fl-hyp :acosp k x))
        (t (fl-hyp :acosn k (- (fl-val x))))))

(assert-event (equal (fl-sinh 8 1) 2646317828889793/2251799813685248))   ; 1.1752011936438014
(assert-event (equal (fl-cosh 8 :nzero) 1))
(assert-event (equal (fl-sinh 8 :nzero) :nzero))
(assert-event (equal (fl-sinh 8 1000) :pinf))
(assert-event (equal (fl-tanh 8 100) 1))
(assert-event (equal (fl-log10 8 1000) 3))
(assert-event (equal (fl-asin 8 1) (fl-trig :pim 8 1/2)))
(assert-event (equal (fl-acos 8 1/2) (fl-trig :pim 8 1/3)))     ; pi/3
(assert-event (equal (fl-asin 8 1/2) (fl-trig :pim 8 1/6)))     ; pi/6
