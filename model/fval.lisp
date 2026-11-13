; fval: the values, the state and the intrinsics of fmean.lisp's meaning
; of a program (Stage A, item 2); fhelp.lisp and fmean.lisp build on them.
;
; Values (J3/24-007 clause 7):
;   (:i k n)   integer of kind k (7.4.3.1): k 1 2 4 8, the processor's kinds
;              for gfortran and flang (iso_fortran_env int8 .. int64,
;              16.10.2), n in -2^(8k-1) .. 2^(8k-1)-1; default kind 4
;   (:l k b)   logical of kind k (7.4.5), b t or nil; default kind 4
;   (:c n s)   character of length n (7.4.4), s a string of n characters;
;              the default kind only, compared in ASCII order (gfortran's
;              and flang's collating sequence, 7.4.4.4)
;   (:a ty k lbs ubs es)  an array (8.5.8, 9.5.3): ty :i :r :l or :c, kind k
;              (for :c, the length), its
;              bounds, its elements in array element order (9.5.3.2), each
;              an integer, t or nil, or :u (undefined)
;   (:z k (x . y))  complex of kind k (7.4.3.3): x, y its real and imaginary
;              parts, values of real kind k (freal.lisp); arrays of it hold (x . y)
;   (:u ty k)  an undefined scalar (19.6)
;
; What the standard prohibits or leaves undefined is an error that stops
; the run, never a value guessed: :overflow (10.1.5.2.4), :divide
; (10.1.5.2.2: no quotient), :bounds (9.5.3.1), :undefined (19.6),
; :intent (C846, 15.5.2.5), :type (Table 10.2, 10.2.1.2), :shape
; (10.1.10, 10.2.1.2), :pure (C1597-C1599), :do-var (11.1.7.4.3,
; 19.6.6: a DO variable redefined), :undeclared (the subset has no
; implicit typing), :step (11.1.7.4.1: incrementation parameter 0),
; :fuel (the model's own bound).
;
; Evaluation: every operand is evaluated, left to right. 10.1.7 lets a
; processor skip an operand or a function reference that is not needed
; to determine the value; a program whose answer depends on such a
; skipped reference (its side effect, or its error) does not conform
; (10.1.4p2: a function reference shall not affect or be affected by
; another entity in the statement), so the model is the meaning of every
; conforming program. Where the value is known without an operand --
; .AND. after false, .OR. after true (10.1.7 NOTE 1) -- an error in that
; operand is the processor's choice: the model answers :pd there, and
; stops with the error elsewhere, where a processor might skip it.

(in-package "ACL2")

(include-book "fprog-cost")
(include-book "flex")
(include-book "freal")

; logic mode, guards not yet verified: the meaning runs, and theorems can
; be proved about it; verifying its guards is owed
(set-verify-guards-eagerness 0)

; ---- alists

(defun alk (k al)
  (declare (xargs :guard t))
  (cond ((atom al) nil) ((and (consp (car al)) (equal (caar al) k)) (car al)) (t (alk k (cdr al)))))
(defun aput (k v al)
  (declare (xargs :guard t))
  (cond ((atom al) (list (cons k v)))
        ((and (consp (car al)) (equal (caar al) k)) (cons (cons k v) (cdr al)))
        (t (cons (car al) (aput k v (cdr al))))))

; ---- kinds and values

(defun ikind-p (k) (declare (xargs :guard t)) (and (member k '(1 2 4 8)) t))
(defun ihuge (k) (declare (xargs :guard t)) (if (ikind-p k) (+ -1 (expt 2 (+ -1 (* 8 k)))) 0))
(defun in-kind (k n)                 ; n representable in integer kind k
  (declare (xargs :guard t))
  (and (ikind-p k) (integerp n) (<= (- (- (ihuge k)) 1) n) (<= n (ihuge k))))

(defun vi (k n) (declare (xargs :guard t)) (list :i k n))
(defun vl (k b) (declare (xargs :guard t)) (list :l k b))
(defun ival-p (v) (declare (xargs :guard t)) (and (consp v) (eq (car v) :i)))
(defun lval-p (v) (declare (xargs :guard t)) (and (consp v) (eq (car v) :l)))
(defun aval-p (v) (declare (xargs :guard t)) (and (consp v) (eq (car v) :a)))
(defun cval-p (v) (declare (xargs :guard t)) (and (consp v) (eq (car v) :c) (stringp (kaddr v))))
(defun vc (s) (declare (xargs :guard t)) (let ((s (if (stringp s) s ""))) (list :c (length s) s)))

; two character values compared (10.1.5.5.1): the shorter as if padded
; with blanks; -1, 0 or 1
(defun cs-cmp (xs ys)
  (declare (xargs :guard t :measure (+ (len xs) (len ys))))
  (if (and (atom xs) (atom ys)) 0
    (let ((a (if (and (consp xs) (characterp (car xs))) (char-code (car xs)) 32))
          (b (if (and (consp ys) (characterp (car ys))) (char-code (car ys)) 32)))
      (cond ((< a b) -1) ((> a b) 1) (t (cs-cmp (if (consp xs) (cdr xs) nil) (if (consp ys) (cdr ys) nil)))))))
(defun c-chars (v) (declare (xargs :guard t)) (if (cval-p v) (coerce (kaddr v) 'list) nil))
; a character value of length n: truncated, or padded with blanks (10.2.1.3p10)
(defun c-fit (n v)
  (declare (xargs :guard t))
  (let ((n (nfix n))) (list :c n (coerce (take n (append (c-chars v) (make-list n :initial-element #\Space))) 'string))))
(defun c-trim (cs) (declare (xargs :guard t)) (if (atom cs) nil (let ((r (c-trim (cdr cs)))) (if (and (null r) (eql (car cs) #\Space)) nil (cons (car cs) r)))))
(defun v-kind (v) (declare (xargs :guard t)) (kadr v))
(defun v-num (v) (declare (xargs :guard t)) (kaddr v))

(defun err (k) (declare (xargs :guard t)) (list :error k))
(defun errp (x) (declare (xargs :guard t)) (and (consp x) (eq (car x) :error)))

; an integer result of kind k, or :overflow (10.1.5.2.4)
(defun mk-int (k n) (declare (xargs :guard t)) (if (in-kind k n) (vi k n) (err :overflow)))

; the kind of x1 op x2 for integers: the greater range (10.1.9.3)
(defun kmax (a b) (declare (xargs :guard t)) (if (and (rationalp a) (rationalp b) (< a b)) b a))

; integer division: toward zero (10.1.5.2.2)
(defun idiv (a b)
  (declare (xargs :guard t))
  (if (and (integerp a) (integerp b) (not (= b 0)))
      (if (equal (< a 0) (< b 0)) (floor (abs a) (abs b)) (- (floor (abs a) (abs b))))
    0))

; x1 ** x2 for integers: x2 < 0 is 1/(x1**|x2|) in integer division (10.1.5.2.1p5)
(defun ipow (a b)
  (declare (xargs :guard t))
  (cond ((not (and (integerp a) (integerp b))) :divide)
        ((<= 0 b) (expt a b))
        ((= a 0) :divide)
        (t (idiv 1 (expt a (- b))))))


; ---- reals (freal.lisp): (:r k x), k 4 or 8, x a value of the format;
; (:pd ty k) a value the standard leaves to the processor

(defun rval-p (v) (declare (xargs :guard t)) (and (consp v) (eq (car v) :r)))
(defun pd-p (v) (declare (xargs :guard t)) (and (consp v) (eq (car v) :pd)))
(defun vr (k x) (declare (xargs :guard t)) (list :r k x))
(defun num-p (v) (declare (xargs :guard t)) (or (ival-p v) (rval-p v)))
(defun rel-op-p (op)
  (declare (xargs :guard t))
  (and (member-equal op '("==" "/=" "<" "<=" ">" ">=" ".eq." ".ne." ".lt." ".le." ".gt." ".ge.")) t))
(defun to-fl (k v)                   ; a numeric value as a value of real kind k (10.1.5.2.1, Table 10.2)
  (declare (xargs :guard t))
  (if (ival-p v) (if (integerp (v-num v)) (fl-round k (v-num v)) :nan) (fl-conv k (v-num v))))

; x1 ** x2 with a real: an integer power 0, 1, 2, -1 is one exact
; operation (or none); any other is the processor's approximation
; (10.1.5.2.1), as is a real power; a negative real to a real power is
; prohibited (10.1.5.2.4p1)
(defun real-pow (k a b)
  (declare (xargs :guard t))
  (let ((x (to-fl k a)))
    (cond ((ival-p b)
           (let ((n (v-num b)))
             (cond ((equal n 1) (vr k x))
                   ((equal n 2) (vr k (fl-mul k x x)))
                   ((equal n -1) (vr k (fl-div k 1 x)))
                   ((and (equal n 0) (rationalp x) (not (= x 0))) (vr k 1))
                   (t (list :pd :r k)))))
          ((and (fl-neg-p x) (not (fl-zero-p x))) (err :domain))
          (t (list :pd :r k)))))
(in-theory (disable real-pow))

; + - * / ** and the relations when an operand is real: the other is
; converted to the real's kind, the greater precision when both are
; real (10.1.9.3); the relations are ISO/IEC 60559's (a NaN unordered)
(defun real-op (op a b)
  (declare (xargs :guard t))
  (let ((k (cond ((and (rval-p a) (rval-p b)) (kmax (v-kind a) (v-kind b))) ((rval-p a) (v-kind a)) (t (v-kind b)))))
    (if (not (rkind-p k)) (err :type)
      (if (equal op "**") (real-pow k a b)
        (let ((x (to-fl k a)) (y (to-fl k b)))
          (cond ((equal op "+") (vr k (fl-add k x y)))
                ((equal op "-") (vr k (fl-sub k x y)))
                ((equal op "*") (vr k (fl-mul k x y)))
                ((equal op "/") (vr k (fl-div k x y)))
                ((member-equal op '("==" ".eq.")) (vl 4 (fl-eql x y)))
                ((member-equal op '("/=" ".ne.")) (vl 4 (not (fl-eql x y))))
                ((member-equal op '("<" ".lt.")) (vl 4 (fl-less x y)))
                ((member-equal op '("<=" ".le.")) (vl 4 (or (fl-less x y) (fl-eql x y))))
                ((member-equal op '(">" ".gt.")) (vl 4 (fl-less y x)))
                ((member-equal op '(">=" ".ge.")) (vl 4 (or (fl-less y x) (fl-eql x y))))
                (t (err :type))))))))
(in-theory (disable real-op))

 ; ---- complex (7.4.3.3, 10.1.5.2): + - and the relations == /= exact,
; part by part; * / ** and ABS are the processor's approximations
; (10.1.5.2.4), answered here only where every step of the textbook
; formula (and, for /, of Smith's) is exact, so that every method gives
; the value: else :pd. ponytail: a zero part's sign is the textbook's,
; not checked against Smith's.
(defun zval-p (v) (declare (xargs :guard t)) (and (consp v) (eq (car v) :z)))
(defun vz (k x y) (declare (xargs :guard t)) (list :z k (cons x y)))
(defun z-re (v) (declare (xargs :guard t)) (kar (kaddr v)))
(defun z-im (v) (declare (xargs :guard t)) (kdr (kaddr v)))
(defun to-z (k v)                    ; a numeric value as complex of kind k (10.1.5.2.1, Table 10.2)
  (declare (xargs :guard t))
  (if (zval-p v) (vz k (fl-conv k (z-re v)) (fl-conv k (z-im v))) (vz k (to-fl k v) 0)))
(defun fl-exact (k q) (declare (xargs :guard t)) (and (rationalp q) (equal (fl-round k q) q)))
(defun z-fin (x y) (declare (xargs :guard t)) (and (fl-fin-p (z-re x)) (fl-fin-p (z-im x)) (fl-fin-p (z-re y)) (fl-fin-p (z-im y))))
(defun z-mul (k x y)
  (declare (xargs :guard t))
  (let ((a (fl-val (z-re x))) (b (fl-val (z-im x))) (c (fl-val (z-re y))) (d (fl-val (z-im y))))
    (if (and (z-fin x y) (fl-exact k (* a c)) (fl-exact k (* b d)) (fl-exact k (* a d)) (fl-exact k (* b c))
             (fl-exact k (- (* a c) (* b d))) (fl-exact k (+ (* a d) (* b c))))
        (vz k (fl-sub k (fl-mul k (z-re x) (z-re y)) (fl-mul k (z-im x) (z-im y)))
            (fl-add k (fl-mul k (z-re x) (z-im y)) (fl-mul k (z-im x) (z-re y))))
      (list :pd :z k))))
(defun z-div (k x y)                 ; a divisor (c, 0): each part over c, one rounding
  (declare (xargs :guard t))
  (let ((a (fl-val (z-re x))) (b (fl-val (z-im x))) (c (fl-val (z-re y))))
    (if (and (z-fin x y) (fl-zero-p (z-im y)) (not (= c 0))
             (fl-exact k (* c c)) (fl-exact k (* a c)) (fl-exact k (* b c)))
        (vz k (fl-div k (z-re x) (z-re y)) (fl-div k (z-im x) (z-re y)))
      (list :pd :z k))))
(defun z-op (op a b)                 ; an operand complex, the other numeric
  (declare (xargs :guard t))
  (let ((k (kmax (if (ival-p a) (v-kind b) (v-kind a)) (if (ival-p b) (v-kind a) (v-kind b)))))
    (if (not (rkind-p k)) (err :type)
      (let ((x (to-z k a)) (y (to-z k b)))
        (cond ((equal op "**")       ; an integer power 1 or 2, of a complex base
               (cond ((not (and (zval-p a) (ival-p b))) (list :pd :z k))
                     ((equal (v-num b) 1) x)
                     ((equal (v-num b) 2) (z-mul k x x))
                     (t (list :pd :z k))))
              ((equal op "+") (vz k (fl-add k (z-re x) (z-re y)) (fl-add k (z-im x) (z-im y))))
              ((equal op "-") (vz k (fl-sub k (z-re x) (z-re y)) (fl-sub k (z-im x) (z-im y))))
              ((equal op "*") (z-mul k x y))
              ((equal op "/") (z-div k x y))
              ((member-equal op '("==" ".eq.")) (vl 4 (and (fl-eql (z-re x) (z-re y)) (fl-eql (z-im x) (z-im y)))))
              ((member-equal op '("/=" ".ne.")) (vl 4 (not (and (fl-eql (z-re x) (z-re y)) (fl-eql (z-im x) (z-im y))))))
              (t (err :type)))))))   ; complex is unordered (10.1.5.5.1)
(in-theory (disable z-mul z-div z-op))

(defun pd-result (op a b)            ; an operation on a processor-dependent value
  (declare (xargs :guard t))
  (cond ((rel-op-p op) (list :pd :l 4))
        ((pd-p a) (list :pd (kadr a) (kaddr a)))
        (t (list :pd (kadr b) (kaddr b)))))

; a numeric or relational or logical binary operation on two scalars
(defun scalar-op (op a b)
  (declare (xargs :guard t))
  (cond
   ((or (pd-p a) (pd-p b)) (pd-result op a b))
   ((and (num-p a) (num-p b) (or (rval-p a) (rval-p b))) (real-op op a b))
   ((and (or (zval-p a) (zval-p b)) (or (num-p a) (zval-p a)) (or (num-p b) (zval-p b))) (z-op op a b))
   ((and (ival-p a) (ival-p b) (integerp (v-num a)) (integerp (v-num b)))
    (let ((x (v-num a)) (y (v-num b)) (k (kmax (v-kind a) (v-kind b))))
      (cond ((equal op "+") (mk-int k (+ x y)))
            ((equal op "-") (mk-int k (- x y)))
            ((equal op "*") (mk-int k (* x y)))
            ((equal op "/") (if (= y 0) (err :divide) (mk-int k (idiv x y))))
            ((equal op "**") (let ((r (ipow x y))) (if (integerp r) (mk-int k r) (err :divide))))
            ((member-equal op '("==" ".eq.")) (vl 4 (= x y)))
            ((member-equal op '("/=" ".ne.")) (vl 4 (not (= x y))))
            ((member-equal op '("<" ".lt.")) (vl 4 (< x y)))
            ((member-equal op '("<=" ".le.")) (vl 4 (<= x y)))
            ((member-equal op '(">" ".gt.")) (vl 4 (> x y)))
            ((member-equal op '(">=" ".ge.")) (vl 4 (>= x y)))
            (t (err :type)))))
   ((and (cval-p a) (cval-p b))           ; 10.1.5.3 concatenation, 10.1.5.5 character relations
    (let ((c (cs-cmp (c-chars a) (c-chars b))))
      (cond ((equal op "//") (vc (concatenate 'string (kaddr a) (kaddr b))))
            ((member-equal op '("==" ".eq.")) (vl 4 (= c 0)))
            ((member-equal op '("/=" ".ne.")) (vl 4 (not (= c 0))))
            ((member-equal op '("<" ".lt.")) (vl 4 (< c 0)))
            ((member-equal op '("<=" ".le.")) (vl 4 (<= c 0)))
            ((member-equal op '(">" ".gt.")) (vl 4 (> c 0)))
            ((member-equal op '(">=" ".ge.")) (vl 4 (>= c 0)))
            (t (err :type)))))
   ((and (lval-p a) (lval-p b) (booleanp (v-num a)) (booleanp (v-num b)))
    ; mixed logical kinds: processor dependent (10.1.9.3); the greater here
    (let ((x (v-num a)) (y (v-num b)) (k (kmax (v-kind a) (v-kind b))))
      (cond ((equal op ".and.") (vl k (and x y)))
            ((equal op ".or.") (vl k (or x y)))
            ((equal op ".eqv.") (vl k (equal x y)))
            ((equal op ".neqv.") (vl k (not (equal x y))))
            (t (err :type)))))
   ((or (and (consp a) (eq (car a) :u)) (and (consp b) (eq (car b) :u))) (err :undefined))
   (t (err :type))))
(in-theory (disable scalar-op))

(defun scalar-neg (a)
  (declare (xargs :guard t))
  (cond ((and (ival-p a) (integerp (v-num a))) (mk-int (v-kind a) (- (v-num a))))
        ((rval-p a) (vr (v-kind a) (fl-neg (v-num a))))
        ((zval-p a) (vz (v-kind a) (fl-neg (z-re a)) (fl-neg (z-im a))))
        ((pd-p a) a)
        (t (err :type))))
(defun scalar-not (a)
  (declare (xargs :guard t))
  (if (and (lval-p a) (booleanp (v-num a))) (vl (v-kind a) (not (v-num a))) (err :type)))

; ---- arrays

(defun extents (lbs ubs)
  (declare (xargs :guard t))
  (if (or (atom lbs) (atom ubs)) nil
    (cons (if (and (integerp (car lbs)) (integerp (car ubs))) (max 0 (+ 1 (- (car ubs) (car lbs)))) 0)
          (extents (cdr lbs) (cdr ubs)))))
(defun prod (xs) (declare (xargs :guard t)) (if (atom xs) 1 (* (nfix (car xs)) (prod (cdr xs)))))

; the offset of subscripts idx in array element order (9.5.3.2), or nil out of bounds
(defun arr-offset (idx lbs ubs)
  (declare (xargs :guard t))
  (cond ((and (atom idx) (atom lbs)) 0)
        ((or (atom idx) (atom lbs) (atom ubs)) nil)
        ((not (and (integerp (car idx)) (integerp (car lbs)) (integerp (car ubs))
                   (<= (car lbs) (car idx)) (<= (car idx) (car ubs)))) nil)
        (t (let ((rest (arr-offset (cdr idx) (cdr lbs) (cdr ubs))))
             (and rest (+ (- (car idx) (car lbs)) (* (+ 1 (- (car ubs) (car lbs))) rest)))))))

(defun a-ty (a) (declare (xargs :guard t)) (kadr a))
(defun a-k (a) (declare (xargs :guard t)) (kaddr a))
(defun a-lbs (a) (declare (xargs :guard t)) (kadddr a))
(defun a-ubs (a) (declare (xargs :guard t)) (kar (kdr (kdr (kdr (kdr a))))))
(defun a-es (a) (declare (xargs :guard t)) (kadr (kdr (kdr (kdr (kdr a))))))
(defun mk-arr (ty k lbs ubs es) (declare (xargs :guard t)) (list :a ty k lbs ubs es))

(defun wrap (ty k e)                 ; an element as a scalar value; a structure's element its components
  (declare (xargs :guard t))
  (cond ((eq e :u) (list :u ty k)) ((eq e :pd) (list :pd ty k)) ((eq ty :i) (vi k e)) ((eq ty :r) (vr k e)) ((eq ty :z) (list :z k e)) ((eq ty :c) (list :c k e)) ((eq ty :s) (list :s (kar k) e)) (t (vl k e))))
(defun raw (v) (declare (xargs :guard t)) (cond ((and (consp v) (eq (car v) :u)) :u) ((pd-p v) :pd) (t (kaddr v))))
(defun scal-ty (v) (declare (xargs :guard t)) (case (kar v) (:i :i) (:l :l) (:r :r) (:z :z) (:c :c) ((:u :pd) (kadr v)) (otherwise nil)))
(defun scal-k (v) (declare (xargs :guard t)) (if (member-eq (kar v) '(:u :pd)) (kaddr v) (kadr v)))

(defun nth-safe (n xs) (declare (xargs :guard t)) (if (atom xs) nil (if (not (posp n)) (car xs) (nth-safe (1- n) (cdr xs)))))
(defun upd-safe (n v xs)
  (declare (xargs :guard t))
  (if (atom xs) nil (if (not (posp n)) (cons v (cdr xs)) (cons (car xs) (upd-safe (1- n) v (cdr xs))))))
(defun repeat-v (n v) (declare (xargs :guard t)) (if (not (posp n)) nil (cons v (repeat-v (1- n) v))))
(defun ones (n) (declare (xargs :guard t)) (if (not (posp n)) nil (cons 1 (ones (1- n)))))

(defun arr-get (a idx)
  (declare (xargs :guard t))
  (let ((o (arr-offset idx (a-lbs a) (a-ubs a))))
    (if (natp o) (wrap (a-ty a) (a-k a) (nth-safe o (a-es a))) (err :bounds))))

(defun arr-set (a idx e)             ; e a raw element
  (declare (xargs :guard t))
  (let ((o (arr-offset idx (a-lbs a) (a-ubs a))))
    (if (natp o) (mk-arr (a-ty a) (a-k a) (a-lbs a) (a-ubs a) (upd-safe o e (a-es a))) (err :bounds))))

; elementwise: a scalar is broadcast (10.1.10); arrays must have one shape;
; the result's lower bounds are 1
(defun ew-scalars (op xs ys ty1 k1 ty2 k2)   ; raw elements -> (mv err raws ty k)
  (declare (xargs :guard t))
  (if (or (atom xs) (atom ys)) (mv nil nil nil nil)
    (let ((r (if (eq op :neg) (scalar-neg (wrap ty1 k1 (car xs)))
               (if (eq op :not) (scalar-not (wrap ty1 k1 (car xs)))
                 (scalar-op op (wrap ty1 k1 (car xs)) (wrap ty2 k2 (car ys)))))))
      (if (errp r) (mv r nil nil nil)
        (mv-let (e rs ty k) (ew-scalars op (cdr xs) (cdr ys) ty1 k1 ty2 k2)
          (declare (ignore ty k))
          (if e (mv e nil nil nil) (mv nil (cons (raw r) rs) (scal-ty r) (scal-k r))))))))

(defun shape-of (v) (declare (xargs :guard t)) (if (aval-p v) (extents (a-lbs v) (a-ubs v)) nil))

; op on values a, b (b ignored for :neg, :not)
(defun val-op (op a b)
  (declare (xargs :guard t))
  (cond ((or (errp a) (errp b)) (if (errp a) a b))
        ((and (not (aval-p a)) (or (member-eq op '(:neg :not)) (not (aval-p b))))
         (cond ((eq op :neg) (scalar-neg a)) ((eq op :not) (scalar-not a)) (t (scalar-op op a b))))
        (t (let* ((un (member-eq op '(:neg :not)))
                  (sh (if (aval-p a) (shape-of a) (shape-of b)))
                  (n (prod sh)))
             (if (and (aval-p a) (aval-p b) (not un) (not (equal (shape-of a) (shape-of b))))
                 (err :shape)
               (let* ((xs (if (aval-p a) (a-es a) (repeat-v n (raw a))))
                     (ys (cond (un xs) ((aval-p b) (a-es b)) (t (repeat-v n (raw b)))))
                     (ty1 (if (aval-p a) (a-ty a) (scal-ty a))) (k1 (if (aval-p a) (a-k a) (scal-k a)))
                     (ty2 (cond (un nil) ((aval-p b) (a-ty b)) (t (scal-ty b))))
                     (k2 (cond (un nil) ((aval-p b) (a-k b)) (t (scal-k b)))))
                 (mv-let (e rs ty k) (ew-scalars op xs ys ty1 k1 ty2 k2)
                   (cond (e e)
                         ((not (posp n)) (mk-arr (if (member-equal op '("==" "/=" "<" "<=" ">" ">=" ".eq." ".ne." ".lt." ".le." ".gt." ".ge." :not)) :l ty1)
                                         (if (member-eq op '(:neg :not)) k1 (kmax k1 k2)) (ones (len sh)) sh nil))
                         (t (mk-arr ty k (ones (len sh)) sh rs))))))))))
(in-theory (disable val-op))

; intrinsic assignment's conversion (10.2.1.3): value v into a variable of
; type ty and kind k; integer to another integer kind keeps the value or
; overflows; logical kinds keep the truth
(defun conv1 (ty k v)
  (declare (xargs :guard t))
  (cond ((and (eq ty :i) (ival-p v)) (mk-int k (v-num v)))
        ((and (eq ty :i) (rval-p v))       ; INT (expr, KIND (variable)), Table 10.8
         (let ((n (fl-to-int :trunc (v-num v)))) (if (integerp n) (mk-int k n) (err :overflow))))
        ((and (eq ty :r) (num-p v)) (vr k (to-fl k v)))   ; REAL (expr, KIND (variable))
        ((and (eq ty :z) (or (num-p v) (zval-p v))) (to-z k v))   ; CMPLX (expr, KIND = KIND (variable))
        ((and (eq ty :r) (zval-p v)) (vr k (fl-conv k (z-re v))))
        ((and (eq ty :i) (zval-p v))
         (let ((n (fl-to-int :trunc (z-re v)))) (if (integerp n) (mk-int k n) (err :overflow))))
        ((and (pd-p v) (member-eq ty '(:i :r :z)) (member-eq (kadr v) '(:i :r :z))) (list :pd ty k))
        ((and (pd-p v) (eq ty :l) (eq (kadr v) :l)) (list :pd ty k))
        ((and (eq ty :l) (lval-p v)) (vl k (v-num v)))
        ((and (eq ty :c) (cval-p v)) (if (eq k :star) v (c-fit k v)))   ; :star, an assumed length (8.5.13)
        ((eq ty :s) (if (and (eq (kar v) :s) (equal (kadr v) (kar k))) v (err :type)))   ; 10.2.1.3p13: k (tname . defaults)
        ((and (consp v) (eq (car v) :u)) (err :undefined))
        (t (err :type))))
(defun conv-raws (ty k fty fk es)
  (declare (xargs :guard t))
  (if (atom es) nil
    (let ((r (if (eq (car es) :u) (list :u ty k) (conv1 ty k (wrap fty fk (car es))))))
      (if (errp r) r
        (let ((rest (conv-raws ty k fty fk (cdr es))))
          (if (errp rest) rest (cons (raw r) rest)))))))

; ---- the state: the store, the next location, the lines printed (newest
; first), the active DO variables' locations, the saved variables
; (8.5.16: a variable initialized in its declaration has SAVE) by key, and
; inside a DO CONCURRENT the trace of its accesses, (:on entry ...) newest
; first, else nil; and the input records still to read (fio.lisp)

(defun write-list (loc ds) (declare (xargs :guard t)) (if (atom ds) nil (cons (list :w loc (car ds)) (write-list loc (cdr ds)))))
(defun read-list (loc ds) (declare (xargs :guard t)) (if (atom ds) nil (cons (list :r loc (car ds)) (read-list loc (cdr ds)))))
(defun st-store (st) (declare (xargs :guard t)) (kar st))
(defun st-next (st) (declare (xargs :guard t)) (nfix (kadr st)))
(defun st-out (st) (declare (xargs :guard t)) (kaddr st))
(defun st-dovars (st) (declare (xargs :guard t)) (kadddr st))
(defun st-saves (st) (declare (xargs :guard t)) (kar (kdr (kdr (kdr (kdr st))))))
(defun st-trace (st) (declare (xargs :guard t)) (kadr (kdr (kdr (kdr (kdr st))))))
(defun st-in (st) (declare (xargs :guard t)) (kadr (kdr (kdr (kdr (kdr (kdr st)))))))   ; the input: (records . position)
(defun mk-st7 (store next out dovars saves trace in) (declare (xargs :guard t)) (list store next out dovars saves trace in))
(defmacro mk-st (store next out dovars saves) `(mk-st7 ,store ,next ,out ,dovars ,saves (st-trace st) (st-in st)))
(defun st-trace-set (tr st)
  (declare (xargs :guard t))
  (mk-st7 (st-store st) (st-next st) (st-out st) (st-dovars st) (st-saves st) tr (st-in st)))
(defun st-in-set (in st)
  (declare (xargs :guard t))
  (mk-st7 (st-store st) (st-next st) (st-out st) (st-dovars st) (st-saves st) (st-trace st) in))
(defun st-out-set (out st)
  (declare (xargs :guard t))
  (mk-st7 (st-store st) (st-next st) out (st-dovars st) (st-saves st) (st-trace st) (st-in st)))
; an access (k loc off): k :r or :w, off an element's offset or :all
(defun st-log (es st)
  (declare (xargs :guard t))
  (if (st-trace st) (st-trace-set (cons :on (append es (true-list-fix (cdr (st-trace st))))) st) st))
(defun diff-offs (xs ys i)          ; the offsets where two element lists differ
  (declare (xargs :guard t))
  (if (or (atom xs) (atom ys)) nil
    (append (if (equal (car xs) (car ys)) nil (list (nfix i))) (diff-offs (cdr xs) (cdr ys) (+ 1 (nfix i))))))
(defun write-entries (loc old new)  ; a definition: its changed elements, or the whole
  (declare (xargs :guard t))
  (if (and (aval-p old) (aval-p new) (equal (len (a-es old)) (len (a-es new))))
      (let ((ds (diff-offs (a-es old) (a-es new) 0)))
        (if (consp ds) (write-list loc ds) nil))
    (list (list :w loc :all))))

(defun st-get (loc st) (declare (xargs :guard t)) (cdr (alk loc (st-store st))))
(defun st-put (loc v st)
  (declare (xargs :guard t))
  (let ((st (if (st-trace st) (st-log (write-entries loc (st-get loc st) v) st) st)))
    (mk-st (aput loc v (st-store st)) (st-next st) (st-out st) (st-dovars st) (st-saves st))))
(defun st-new (v st)                 ; (mv loc st)
  (declare (xargs :guard t))
  (let ((loc (st-next st)))
    (mv loc (mk-st (aput loc v (st-store st)) (+ 1 loc) (st-out st) (st-dovars st) (st-saves st)))))
(defun st-print (line st)
  (declare (xargs :guard t))
  (mk-st (st-store st) (st-next st) (cons line (st-out st)) (st-dovars st) (st-saves st)))
(defun st-dovars-set (ds st)
  (declare (xargs :guard t))
  (mk-st (st-store st) (st-next st) (st-out st) ds (st-saves st)))
(defun st-save (key loc st)
  (declare (xargs :guard t))
  (mk-st (st-store st) (st-next st) (st-out st) (st-dovars st) (cons (cons key loc) (st-saves st))))

; ---- scopes: a list of frames, innermost first; a frame binds names to
;   (:var loc mode)   a variable, mode :rw or :in (INTENT(IN), or an
;                     actual argument that is not a variable, 15.5.2.4)
;   (:const v)        a named constant (8.5.13 PARAMETER)
;   (:proc u host)    a procedure: its unit tree, and where its host is:
;                     :host (the frame binding it), (:mod m), or :ext

(defun env-lookup (n env)            ; (mv binding suffix depth)
  (declare (xargs :guard t))
  (if (atom env) (mv nil nil 0)
    (let ((b (alk n (car env))))
      (if b (mv (cdr b) env 0)
        (mv-let (bb suf d) (env-lookup n (cdr env)) (mv bb suf (+ 1 (nfix d))))))))

(defun tok-name (tk) (declare (xargs :guard t)) (kadr tk))

; ---- rendering what PRINT * writes (13.10.4: list-directed; the form of
; each value is processor dependent, so the model answers the values and
; check-fsem compares them token by token)

(defun int-str (n)
  (declare (xargs :guard t))
  (if (integerp n)
      (coerce (if (< n 0) (cons #\- (explode-nonnegative-integer (- n) 10 nil)) (explode-nonnegative-integer n 10 nil)) 'string)
    "?"))
; a real is written exactly, ~Rk:n/d (or -0, +Inf, -Inf, NaN): check-fsem
; reads what a compiler printed as a value of kind k and compares
(defun rat-str (x)
  (declare (xargs :guard t))
  (if (integerp x) (int-str x) (if (rationalp x) (concatenate 'string (int-str (numerator x)) "/" (int-str (denominator x))) "?")))
(defun real-str (k x)
  (declare (xargs :guard t))
  (concatenate 'string "~R" (int-str k) ":"
               (case x (:nzero "-0") (:pinf "+Inf") (:ninf "-Inf") (:nan "NaN") (otherwise (rat-str x)))))
(defun render1 (v)
  (declare (xargs :guard t))
  (case (kar v) (:i (int-str (kaddr v))) (:l (if (kaddr v) "T" "F")) (:c (if (stringp (kaddr v)) (kaddr v) ""))
    (:r (real-str (kadr v) (kaddr v))) (:pd "~PD")
    (:z (concatenate 'string "(" (real-str (kadr v) (z-re v)) "," (real-str (kadr v) (z-im v)) ")"))
    (otherwise "?")))
(defun wrap-all (ty k es)
  (declare (xargs :guard t))
  (if (atom es) nil (cons (wrap ty k (car es)) (wrap-all ty k (cdr es)))))
(defun wrap-onto (ty k es acc)       ; (append (wrap-all ty k es) acc)
  (declare (xargs :guard t))
  (if (atom es) acc (cons (wrap ty k (car es)) (wrap-onto ty k (cdr es) acc))))
; the scalars of an output list, then acc: an array's in array element
; order (9.5.3.2), a structure's its components in component order (12.6.3p7)
(mutual-recursion
 (defun flat-val (v acc)
   (declare (xargs :guard t :measure (acl2-count v)))
   (cond ((and (aval-p v) (eq (a-ty v) :s)) (flat-ses (a-es v) acc))
         ((aval-p v) (wrap-onto (a-ty v) (a-k v) (a-es v) acc))
         ((eq (kar v) :s) (flat-cs (kaddr v) acc))
         (t (cons v acc))))
 (defun flat-cs (cs acc)
   (declare (xargs :guard t :measure (acl2-count cs)))
   (if (atom cs) acc (flat-cs (cdr cs) (flat-val (kdr (car cs)) acc))))   ; cs latest component first
 (defun flat-ses (es acc)
   (declare (xargs :guard t :measure (acl2-count es)))
   (if (atom es) acc (flat-cs (car es) (flat-ses (cdr es) acc)))))
(defun flat-vals (vs)
  (declare (xargs :guard t))
  (if (atom vs) nil (flat-val (car vs) (flat-vals (cdr vs)))))
; adjacent character items are written with no value separator between
; them (13.10.4, under the delimiter mode NONE, PRINT's)
(defun render-flat (xs)
  (declare (xargs :guard t :measure (len xs)))
  (cond ((atom xs) nil)
        ((and (cval-p (car xs)) (consp (cdr xs)) (cval-p (cadr xs)))
         (render-flat (cons (vc (concatenate 'string (kaddr (car xs)) (kaddr (cadr xs)))) (cddr xs))))
        (t (cons (render1 (car xs)) (render-flat (cdr xs))))))
(defun render (vs) (declare (xargs :guard t)) (render-flat (flat-vals vs)))

; ---- the intrinsic procedures (16.9) the subset has, on argument values
; vs (positional) and kw (an alist of keyword arguments, "dim" "kind")

(defun ival-scalar (v) (declare (xargs :guard t)) (and (ival-p v) (integerp (v-num v))))

(defun conv-kind-ty (name k ty kk)   ; the result type and kind of an elemental intrinsic
  (declare (xargs :guard t))
  (cond ((member-equal name '("real" "dble")) (mv :r (if (equal name "dble") 8 k)))
        ((member-equal name '("int" "nint" "floor" "ceiling")) (mv :i k))
        ((and (member-equal name '("abs" "aimag")) (eq ty :z)) (mv :r kk))
        (t (mv ty kk))))

(defconst *pd-real-fns*              ; processor-dependent approximations (16.9)
  '("sin" "cos" "tan" "asin" "acos" "atan" "exp" "log" "log10" "sinh" "cosh" "tanh"))

(defun el1 (name k a)                ; an elemental intrinsic of one argument; k from KIND=
  (declare (xargs :guard t))
  (cond ((eq (kar a) :u) (err :undefined))
        ((pd-p a) (mv-let (ty kk) (conv-kind-ty name k (kadr a) (kaddr a)) (list :pd ty kk)))
        ((equal name "abs")                                                  ; 16.9.2
         (cond ((ival-scalar a) (mk-int (v-kind a) (abs (v-num a))))
               ((rval-p a) (vr (v-kind a) (fl-abs (v-num a))))
               ((zval-p a)          ; 16.9.2: the processor's approximation of the modulus
                (let* ((k (v-kind a)) (x (fl-val (z-re a))) (y (fl-val (z-im a))) (r (fl-sqrt k (+ (* x x) (* y y)))))
                  (if (and (z-fin a a) (fl-exact k (+ (* x x) (* y y))) (rationalp r) (= (* r r) (+ (* x x) (* y y))))
                      (vr k r) (list :pd :r k))))
               (t (err :type))))
        ((zval-p a)
         (cond ((equal name "aimag") (vr (v-kind a) (z-im a)))                ; 16.9.6
               ((equal name "conjg") (vz (v-kind a) (z-re a) (fl-neg (z-im a))))   ; 16.9.59
               ((equal name "real") (if (rkind-p k) (vr k (fl-conv k (z-re a))) (err :type)))   ; 16.9.170
               (t (err :type))))
        ((not (num-p a)) (err :type))
        ((member-equal name '("real" "dble"))                                ; 16.9.170, 16.9.68
         (let ((kk (if (equal name "dble") 8 k))) (if (rkind-p kk) (vr kk (to-fl kk a)) (err :type))))
        ((and (equal name "int") (ival-scalar a)) (mk-int k (v-num a)))      ; 16.9.110
        ((member-equal name '("int" "nint" "floor" "ceiling"))               ; 16.9.110, .153, .80, .39
         (if (not (rval-p a)) (err :type)
           (let ((n (fl-to-int (cond ((equal name "nint") :nint) ((equal name "floor") :floor)
                                     ((equal name "ceiling") :ceiling) (t :trunc))
                               (v-num a))))
             (if (integerp n) (mk-int k n) (err :overflow)))))
        ((not (rval-p a)) (err :type))
        ((equal name "sqrt")                                                 ; 16.9.191, 17.? item 6
         (let ((x (v-num a)))
           (if (or (eq x :nan) (and (fl-neg-p x) (not (fl-zero-p x)))) (err :domain)   ; X shall be >= 0
             (vr (v-kind a) (fl-sqrt (v-kind a) x)))))
        ((member-equal name *pd-real-fns*) (list :pd :r (v-kind a)))
        (t (err :type))))
(in-theory (disable el1))

(defun real-el2 (name a p)           ; MAX MIN MOD MODULO SIGN of two reals of one kind
  (declare (xargs :guard t))
  (let ((k (v-kind a)) (x (v-num a)) (y (v-num p)))
    (cond ((member-equal name '("max" "min"))
           ; the largest (smallest) argument: open for a NaN, or two zeros of either sign
           (cond ((or (eq x :nan) (eq y :nan)) (list :pd :r k))
                 ((and (fl-zero-p x) (fl-zero-p y) (not (equal x y))) (list :pd :r k))
                 ((equal name "max") (if (fl-less x y) p a))
                 (t (if (fl-less y x) p a))))
          ((equal name "sign")                                     ; 16.9.189: case (iv) for zeros
           (if (eq y :nan) (list :pd :r k)
             (vr k (if (fl-neg-p y) (fl-neg (fl-abs x)) (fl-abs x)))))
          ((fl-zero-p y) (err :divide))                            ; P shall not be zero
          ; a zero result's sign the standard leaves open (16.9.145, 16.9.146 give the value):
          ; gfortran answers A's for MOD and P's for MODULO, flang other signs for MOD
          ((equal name "mod") (let ((r (fl-mod k x y))) (if (fl-zero-p r) (list :pd :r k) (vr k r))))   ; A - INT (A/P) * P
          ((equal name "modulo")                                   ; A - FLOOR (A/P) * P
           (if (not (and (fl-fin-p x) (fl-fin-p y))) (vr k :nan)
             (let ((r (- (fl-val x) (* (floor (/ (fl-val x) (fl-val y)) 1) (fl-val y)))))
               (if (= r 0) (list :pd :r k) (vr k (fl-round k r))))))
          (t (err :type)))))
(in-theory (disable real-el2))

(defun el2 (name a p)                ; MOD, MODULO (16.9.145, 16.9.146), MAX, MIN, SIGN of two
  (declare (xargs :guard t))
  (cond ((or (eq (kar a) :u) (eq (kar p) :u)) (err :undefined))
        ((or (pd-p a) (pd-p p)) (if (pd-p a) a (list :pd (scal-ty a) (scal-k a))))
        ((and (rval-p a) (rval-p p))
         (if (equal (v-kind a) (v-kind p)) (real-el2 name a p) (err :type)))
        ((not (and (ival-scalar a) (ival-scalar p))) (err :type))
        ((not (equal (v-kind a) (v-kind p))) (err :type))   ; same kind (16.9.135, 16.9.145)
        ((equal name "max") (vi (v-kind a) (max (v-num a) (v-num p))))
        ((equal name "min") (vi (v-kind a) (min (v-num a) (v-num p))))
        ((equal name "sign") (mk-int (v-kind a) (if (< (v-num p) 0) (- (abs (v-num a))) (abs (v-num a)))))
        ((= (v-num p) 0) (err :divide))                      ; P shall not be zero
        ((equal name "mod") (mk-int (v-kind a) (- (v-num a) (* (idiv (v-num a) (v-num p)) (v-num p)))))
        ((equal name "modulo") (mk-int (v-kind a) (mod (v-num a) (v-num p))))
        (t (err :type))))

(defun ew1-list (name k ty kk es)
  (declare (xargs :guard t))
  (if (atom es) nil
    (let ((r (el1 name k (wrap ty kk (car es)))))
      (if (errp r) r (let ((rest (ew1-list name k ty kk (cdr es)))) (if (errp rest) rest (cons (raw r) rest)))))))

(defun ew1 (name k a)                ; elemental over an array
  (declare (xargs :guard t))
  (if (not (aval-p a)) (el1 name k a)
    (let ((rs (ew1-list name k (a-ty a) (a-k a) (a-es a))))
      (if (errp rs) rs
        (mv-let (ty kk) (conv-kind-ty name k (a-ty a) (a-k a))
          (mk-arr ty kk (ones (len (a-lbs a))) (extents (a-lbs a) (a-ubs a)) rs))))))

(defun ew2-list (name ta ka tb kb xs ys)
  (declare (xargs :guard t))
  (if (or (atom xs) (atom ys)) nil
    (let ((r (el2 name (wrap ta ka (car xs)) (wrap tb kb (car ys)))))
      (if (errp r) r (let ((rest (ew2-list name ta ka tb kb (cdr xs) (cdr ys)))) (if (errp rest) rest (cons (raw r) rest)))))))

(defun ew2 (name a b)                ; two arguments, broadcast (10.1.10)
  (declare (xargs :guard t))
  (cond ((and (not (aval-p a)) (not (aval-p b))) (el2 name a b))
        ((and (aval-p a) (aval-p b) (not (equal (shape-of a) (shape-of b)))) (err :shape))
        (t (let* ((sh (if (aval-p a) (shape-of a) (shape-of b))) (n (prod sh))
                  (ta (if (aval-p a) (a-ty a) (scal-ty a))) (ka (if (aval-p a) (a-k a) (scal-k a)))
                  (tb (if (aval-p b) (a-ty b) (scal-ty b))) (kb (if (aval-p b) (a-k b) (scal-k b)))
                  (xs (if (aval-p a) (a-es a) (repeat-v n (raw a))))
                  (ys (if (aval-p b) (a-es b) (repeat-v n (raw b))))
                  (rs (ew2-list name ta ka tb kb xs ys)))
             (if (errp rs) rs (mk-arr ta ka (ones (len sh)) sh rs))))))
(defun fold-max-min (name v vs)      ; MAX, MIN of any number (16.9.135, 16.9.141)
  (declare (xargs :guard t))
  (if (atom vs) v (fold-max-min name (ew2 name v (car vs)) (cdr vs))))

(defun sum-raws (es) (declare (xargs :guard t)) (if (atom es) 0 (+ (ifix (car es)) (sum-raws (cdr es)))))
(defun prod-raws (es) (declare (xargs :guard t)) (if (atom es) 1 (* (ifix (car es)) (prod-raws (cdr es)))))
(defun max-raws (es m) (declare (xargs :guard t)) (if (atom es) m (max-raws (cdr es) (if (and (integerp (car es)) (rationalp m) (< m (car es))) (car es) m))))
(defun min-raws (es m) (declare (xargs :guard t)) (if (atom es) m (min-raws (cdr es) (if (and (integerp (car es)) (rationalp m) (< (car es) m)) (car es) m))))
(defun count-raws (es) (declare (xargs :guard t)) (if (atom es) 0 (+ (if (eq (car es) t) 1 0) (count-raws (cdr es)))))
; SUM and PRODUCT of reals: a processor-dependent approximation
; (16.9.201, 16.9.165); exact, as every processor's is, when the left to
; right fold of finite elements never rounds. MAXVAL, MINVAL of finite
; elements; with a NaN, a signed zero or none at all, the processor's
(defun real-fold (sum k es acc)
  (declare (xargs :guard t))
  (cond ((atom es) acc)
        ((not (and (rationalp (car es)) (rationalp acc))) nil)
        (t (let ((q (if sum (+ acc (car es)) (* acc (car es)))))
             (if (equal (fl-round k q) q) (real-fold sum k (cdr es) q) nil)))))
(defun rat-list-p (es) (declare (xargs :guard t)) (if (atom es) t (and (rationalp (car es)) (rat-list-p (cdr es)))))
(defun rat-max (es m) (declare (xargs :guard t)) (if (atom es) m (rat-max (cdr es) (if (and (rationalp (car es)) (rationalp m) (< m (car es))) (car es) m))))
(defun rat-min (es m) (declare (xargs :guard t)) (if (atom es) m (rat-min (cdr es) (if (and (rationalp (car es)) (rationalp m) (< (car es) m)) (car es) m))))
(defun real-reduce (name k es)
  (declare (xargs :guard t))
  (cond ((member :u es) (err :undefined))
        ((member-equal name '("sum" "product"))
         (let ((r (real-fold (equal name "sum") k es (if (equal name "sum") 0 1))))
           (if (rationalp r) (vr k r) (list :pd :r k))))
        ((and (consp es) (rat-list-p es)) (vr k (if (equal name "maxval") (rat-max (cdr es) (car es)) (rat-min (cdr es) (car es)))))
        (t (list :pd :r k))))
(defun nth1 (i xs) (declare (xargs :guard t)) (nth-safe (+ -1 (nfix i)) xs))

(defun kind-arg (kw)                 ; KIND= : a scalar integer constant, a valid kind
  (declare (xargs :guard t))
  (let ((v (cdr (alk "kind" kw))))
    (cond ((null v) 4) ((and (ival-scalar v) (ikind-p (v-num v))) (v-num v)) (t nil))))

(defun intrinsic (name vs kw)
  (declare (xargs :guard t))
  (let ((a (kar vs)) (n (len vs)))
    (cond
     ((and (equal name "real") (zval-p a) (= n 1) (null kw)) (vr (v-kind a) (z-re a)))   ; 16.9.170: A's kind
     ((equal name "cmplx")                                    ; 16.9.56: default real's kind unless KIND
      (let ((k (if (= n 3) (and (null kw) (ival-scalar (kaddr vs)) (v-num (kaddr vs))) (kind-arg kw))) (y (kadr vs)))
        (cond ((not (and (rkind-p k) (<= 1 n) (<= n 3))) (err :type))
              ((or (pd-p a) (pd-p y)) (list :pd :z k))
              ((zval-p a) (if (= n 1) (to-z k a) (err :type)))
              ((not (and (num-p a) (or (< n 2) (num-p y)))) (err :type))
              (t (vz k (to-fl k a) (if (< n 2) 0 (to-fl k y)))))))
     ((member-equal name '("abs" "aimag" "conjg"))
      (if (and (= n 1) (null kw)) (ew1 name nil a) (err :arity)))
     ((or (member-equal name '("sqrt" "real" "dble" "int" "nint" "floor" "ceiling")) (member-equal name *pd-real-fns*))
      ; KIND positional (REAL (A, KIND)) or by keyword
      (let ((k (if (= n 2) (and (null kw) (ival-scalar (kadr vs)) (v-num (kadr vs))) (kind-arg kw))))
        (cond ((not (or (= n 1) (and (= n 2) (member-equal name '("real" "int" "nint" "floor" "ceiling")))))
               (err :arity))
              ((not k) (err :type))
              (t (ew1 name k a)))))
     ((member-equal name '("mod" "modulo" "sign"))
      (if (and (= n 2) (null kw)) (ew2 name a (kadr vs)) (err :arity)))
     ((member-equal name '("max" "min"))
      (if (and (<= 2 n) (null kw)) (fold-max-min name a (cdr vs)) (err :arity)))
     ((equal name "huge")                                     ; 16.9.96
      (cond ((ival-p a) (vi (v-kind a) (ihuge (v-kind a))))
            ((rval-p a) (vr (v-kind a) (fl-huge (v-kind a))))
            ((and (aval-p a) (eq (a-ty a) :r)) (vr (a-k a) (fl-huge (a-k a))))
            ((aval-p a) (vi (a-k a) (ihuge (a-k a)))) (t (err :type))))
     ((member-equal name '("tiny" "epsilon"))                ; 16.9.210, 16.9.76
      (let ((k (cond ((rval-p a) (v-kind a)) ((and (aval-p a) (eq (a-ty a) :r)) (a-k a)) (t nil))))
        (if (rkind-p k) (vr k (if (equal name "tiny") (fl-tiny k) (fl-epsilon k))) (err :type))))
     ((equal name "allocated")                                ; 16.9.11: an allocatable array's status
      (cond ((not (and (= n 1) (null kw))) (err :arity)) ((aval-p a) (vl 4 t)) ((eq (kar a) :unalloc) (vl 4 nil)) (t (err :type))))
     ((equal name "kind")                                     ; 16.9.118
      (cond ((or (ival-p a) (lval-p a) (rval-p a) (zval-p a)) (vi 4 (v-kind a))) ((cval-p a) (vi 4 1))
            ((aval-p a) (vi 4 (if (eq (a-ty a) :c) 1 (a-k a)))) (t (err :type))))
     ((member-equal name '("len" "len_trim" "trim"))          ; 16.9.120, 16.9.121, 16.9.212, scalars
      (let ((k (kind-arg kw)))
        (cond ((not (and (= n 1) (cval-p a) k (or (null kw) (not (equal name "trim"))))) (err :type))
              ((equal name "len") (mk-int k (v-kind a)))
              ((equal name "len_trim") (mk-int k (len (c-trim (c-chars a)))))
              (t (vc (coerce (c-trim (c-chars a)) 'string))))))
     ((member-equal name '("size" "lbound" "ubound"))         ; 16.9.194, 16.9.119, 16.9.215
      (let ((k (kind-arg kw)) (dim (or (kadr vs) (cdr (alk "dim" kw)))))
        (cond ((not (and k (aval-p a))) (err :type))
              (dim (if (and (ival-scalar dim) (<= 1 (v-num dim)) (<= (v-num dim) (len (a-lbs a))))
                       (let ((e (nth1 (v-num dim) (extents (a-lbs a) (a-ubs a)))))
                         (mk-int k (cond ((equal name "size") e)
                                         ((equal name "lbound") (if (not (posp e)) 1 (nth1 (v-num dim) (a-lbs a))))
                                         (t (if (not (posp e)) 0 (nth1 (v-num dim) (a-ubs a)))))))
                     (err :bounds)))
              ((equal name "size") (mk-int k (prod (extents (a-lbs a) (a-ubs a)))))
              (t (let ((bs (if (equal name "lbound") (a-lbs a) (a-ubs a))))
                   (mk-arr :i k (list 1) (list (len bs)) bs))))))
     ((member-equal name '("sum" "product" "maxval" "minval"))   ; 16.9.201, 16.9.165, 16.9.138, 16.9.144
      (cond ((and (= n 1) (null kw) (aval-p a) (eq (a-ty a) :r)) (real-reduce name (a-k a) (a-es a)))
            ((not (and (= n 1) (null kw) (aval-p a) (eq (a-ty a) :i))) (err :type))
            ((member :u (a-es a)) (err :undefined))
            (t (let ((k (a-k a)) (es (a-es a)))
                 (cond ((equal name "sum") (mk-int k (sum-raws es)))
                       ((equal name "product") (mk-int k (prod-raws es)))
                       ; of no elements: the most negative, the most positive (16.9.138, 16.9.144)
                       ((equal name "maxval") (vi k (max-raws es (- (- (ihuge k)) 1))))
                       (t (vi k (min-raws es (ihuge k)))))))))
     ((member-equal name '("any" "all" "count"))              ; 16.9.15, 16.9.12, 16.9.66
      (cond ((not (and (= n 1) (aval-p a) (eq (a-ty a) :l))) (err :type))
            ((member :u (a-es a)) (err :undefined))
            ((equal name "any") (vl 4 (and (member t (a-es a)) t)))
            ((equal name "all") (vl 4 (not (member nil (a-es a)))))
            (t (let ((k (kind-arg kw))) (if k (mk-int k (count-raws (a-es a))) (err :type))))))
     ((equal name "merge")                                    ; 16.9.139, scalars
      (let ((ts a) (fs (kadr vs)) (m (kaddr vs)))
        (cond ((not (and (= n 3) (lval-p m) (booleanp (v-num m)))) (err :type))
              ((not (equal (list (kar ts) (kadr ts)) (list (kar fs) (kadr fs)))) (err :type))
              (t (if (v-num m) ts fs)))))
     (t (err :undeclared)))))
(in-theory (disable intrinsic))

