; fmean: the meaning of a whole program of the subset (Stage A, item 2):
; an executable ACL2 model over fprog.lisp's parse trees. fortran-run
; reads the text (flex), parses it (fps, fpu), and runs the main program,
; answering what it prints and how it stops.
;
; Values (J3/24-007 clause 7):
;   (:i k n)   integer of kind k (7.4.3.1): k 1 2 4 8, the processor's kinds
;              for gfortran and flang (iso_fortran_env int8 .. int64,
;              16.10.2), n in -2^(8k-1) .. 2^(8k-1)-1; default kind 4
;   (:l k b)   logical of kind k (7.4.5), b t or nil; default kind 4
;   (:c s)     a character constant, printed only
;   (:a ty k lbs ubs es)  an array (8.5.8, 9.5.3): ty :i or :l, kind k, its
;              bounds, its elements in array element order (9.5.3.2), each
;              an integer, t or nil, or :u (undefined)
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

(include-book "fprog")
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

(defun scalar-neg (a)
  (declare (xargs :guard t))
  (cond ((and (ival-p a) (integerp (v-num a))) (mk-int (v-kind a) (- (v-num a))))
        ((rval-p a) (vr (v-kind a) (fl-neg (v-num a))))
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

(defun wrap (ty k e)                 ; an element as a scalar value
  (declare (xargs :guard t))
  (cond ((eq e :u) (list :u ty k)) ((eq e :pd) (list :pd ty k)) ((eq ty :i) (vi k e)) ((eq ty :r) (vr k e)) (t (vl k e))))
(defun raw (v) (declare (xargs :guard t)) (cond ((and (consp v) (eq (car v) :u)) :u) ((pd-p v) :pd) (t (kaddr v))))
(defun scal-ty (v) (declare (xargs :guard t)) (case (kar v) (:i :i) (:l :l) (:r :r) ((:u :pd) (kadr v)) (otherwise nil)))
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

; intrinsic assignment's conversion (10.2.1.3): value v into a variable of
; type ty and kind k; integer to another integer kind keeps the value or
; overflows; logical kinds keep the truth
(defun conv1 (ty k v)
  (declare (xargs :guard t))
  (cond ((and (eq ty :i) (ival-p v)) (mk-int k (v-num v)))
        ((and (eq ty :i) (rval-p v))       ; INT (expr, KIND (variable)), Table 10.8
         (let ((n (fl-to-int :trunc (v-num v)))) (if (integerp n) (mk-int k n) (err :overflow))))
        ((and (eq ty :r) (num-p v)) (vr k (to-fl k v)))   ; REAL (expr, KIND (variable))
        ((and (pd-p v) (member-eq ty '(:i :r)) (member-eq (kadr v) '(:i :r))) (list :pd ty k))
        ((and (pd-p v) (eq ty :l) (eq (kadr v) :l)) (list :pd ty k))
        ((and (eq ty :l) (lval-p v)) (vl k (v-num v)))
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
; first, else nil

(defun write-list (loc ds) (declare (xargs :guard t)) (if (atom ds) nil (cons (list :w loc (car ds)) (write-list loc (cdr ds)))))
(defun read-list (loc ds) (declare (xargs :guard t)) (if (atom ds) nil (cons (list :r loc (car ds)) (read-list loc (cdr ds)))))
(defun st-store (st) (declare (xargs :guard t)) (kar st))
(defun st-next (st) (declare (xargs :guard t)) (nfix (kadr st)))
(defun st-out (st) (declare (xargs :guard t)) (kaddr st))
(defun st-dovars (st) (declare (xargs :guard t)) (kadddr st))
(defun st-saves (st) (declare (xargs :guard t)) (kar (kdr (kdr (kdr (kdr st))))))
(defun st-trace (st) (declare (xargs :guard t)) (kadr (kdr (kdr (kdr (kdr st))))))
(defun mk-st6 (store next out dovars saves trace) (declare (xargs :guard t)) (list store next out dovars saves trace))
(defmacro mk-st (store next out dovars saves) `(mk-st6 ,store ,next ,out ,dovars ,saves (st-trace st)))
(defun st-trace-set (tr st)
  (declare (xargs :guard t))
  (mk-st6 (st-store st) (st-next st) (st-out st) (st-dovars st) (st-saves st) tr))
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
  (case (kar v) (:i (int-str (kaddr v))) (:l (if (kaddr v) "T" "F")) (:c (if (stringp (kadr v)) (kadr v) ""))
    (:r (real-str (kadr v) (kaddr v))) (:pd "~PD")
    (otherwise "?")))
(defun render-raws (ty k es)
  (declare (xargs :guard t))
  (if (atom es) nil (cons (render1 (wrap ty k (car es))) (render-raws ty k (cdr es)))))
(defun render (vs)
  (declare (xargs :guard t))
  (if (atom vs) nil
    (append (if (aval-p (car vs)) (render-raws (a-ty (car vs)) (a-k (car vs)) (a-es (car vs)))
              (list (render1 (car vs))))
            (render (cdr vs)))))

; ---- the intrinsic procedures (16.9) the subset has, on argument values
; vs (positional) and kw (an alist of keyword arguments, "dim" "kind")

(defun ival-scalar (v) (declare (xargs :guard t)) (and (ival-p v) (integerp (v-num v))))

(defun conv-kind-ty (name k ty kk)   ; the result type and kind of an elemental intrinsic
  (declare (xargs :guard t))
  (cond ((member-equal name '("real" "dble")) (mv :r (if (equal name "dble") 8 k)))
        ((member-equal name '("int" "nint" "floor" "ceiling")) (mv :i k))
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
          ((equal name "mod") (vr k (fl-mod k x y)))               ; A - INT (A/P) * P
          ((equal name "modulo")                                   ; A - FLOOR (A/P) * P
           (if (not (and (fl-fin-p x) (fl-fin-p y))) (vr k :nan)
             (let ((r (- (fl-val x) (* (floor (/ (fl-val x) (fl-val y)) 1) (fl-val y)))))
               (vr k (if (= r 0) (fl-signed-zero (fl-neg-p x)) (fl-round k r))))))
          (t (err :type)))))

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
     ((member-equal name '("abs"))
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
     ((equal name "kind")                                     ; 16.9.118
      (cond ((or (ival-p a) (lval-p a) (rval-p a)) (vi 4 (v-kind a))) ((aval-p a) (vi 4 (a-k a))) (t (err :type))))
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

; ---- helpers outside the recursion

(defun str-nat (cs acc)              ; a digit-string's value
  (declare (xargs :guard t))
  (if (atom cs) acc
    (str-nat (cdr cs) (+ (* 10 (nfix acc)) (if (characterp (car cs)) (nfix (- (char-code (car cs)) 48)) 0)))))
(defun digits-val (s) (declare (xargs :guard t)) (if (stringp s) (str-nat (coerce s 'list) 0) 0))

(defun undef-in (v)                  ; a value with an undefined part
  (declare (xargs :guard t))
  (cond ((aval-p v) (and (member :u (a-es v)) t)) ((eq (kar v) :u) t) (t nil)))

(defun fresh (ty k lbs ubs)          ; a variable's undefined value: scalar when no bounds
  (declare (xargs :guard t))
  (if (atom lbs) (list :u ty k) (mk-arr ty k lbs ubs (repeat-v (prod (extents lbs ubs)) :u))))

; the indices a section subscript selects: lo, lo+st, ... while within hi
(defun range-idx (lo hi st n)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (not (posp n)) (not (and (integerp lo) (integerp hi) (integerp st) (not (= st 0))))) nil
    (if (if (< 0 st) (<= lo hi) (>= lo hi)) (cons lo (range-idx (+ lo st) hi st (1- n))) nil)))
(defun range-count (lo hi st)        ; max(0, (hi - lo + st)/st), 9.5.3.3.3
  (declare (xargs :guard t))
  (if (and (integerp lo) (integerp hi) (integerp st) (not (= st 0))) (max 0 (idiv (+ (- hi lo) st) st)) 0))

; tuples of the selected indices, the first subscript varying fastest
(defun tuples-cons1 (is rest)        ; is x rest, rest's tuple outer
  (declare (xargs :guard t))
  (if (atom is) nil (cons (cons (car is) rest) (tuples-cons1 (cdr is) rest))))
(defun tuples-cons (is rests)
  (declare (xargs :guard t))
  (if (atom rests) nil (append (tuples-cons1 is (car rests)) (tuples-cons is (cdr rests)))))

(defun tuples (dims)                 ; dims: per subscript, a list of indices
  (declare (xargs :guard t))
  (if (atom dims) (list nil)
    (tuples-cons (car dims) (tuples (cdr dims)))))
(defun arr-gets (a ts)               ; raw elements at tuples, or an error
  (declare (xargs :guard t))
  (if (atom ts) nil
    (let ((o (arr-offset (car ts) (a-lbs a) (a-ubs a))))
      (if (not (natp o)) (err :bounds)
        (let ((rest (arr-gets a (cdr ts)))) (if (errp rest) rest (cons (nth-safe o (a-es a)) rest)))))))
(defun tuple-offs (a ts)             ; the offsets of tuples, the in-bounds ones
  (declare (xargs :guard t))
  (if (atom ts) nil (let ((o (arr-offset (car ts) (a-lbs a) (a-ubs a)))) (if (natp o) (cons o (tuple-offs a (cdr ts))) (tuple-offs a (cdr ts))))))
(defun arr-sets (a ts es)            ; raw elements es into tuples
  (declare (xargs :guard t :measure (len ts)))
  (if (or (atom ts) (atom es)) a
    (let ((a2 (arr-set a (car ts) (car es)))) (if (errp a2) a2 (arr-sets a2 (cdr ts) (cdr es))))))

; a value assigned into a variable of type ty, kind k and current value
; old (an array, or a scalar): intrinsic assignment (10.2.1.3)
(defun assign-val (old v)
  (declare (xargs :guard t))
  (let ((ty (if (aval-p old) (a-ty old) (scal-ty old))) (k (if (aval-p old) (a-k old) (scal-k old))))
    (cond ((errp v) v)
          ((not (aval-p old))
           (if (aval-p v) (err :shape) (conv1 ty k v)))
          ((aval-p v)
           (if (not (equal (shape-of old) (shape-of v))) (err :shape)
             (let ((rs (conv-raws ty k (a-ty v) (a-k v) (a-es v))))
               (if (errp rs) rs (mk-arr ty k (a-lbs old) (a-ubs old) rs)))))
          (t (let ((c (conv1 ty k v)))      ; a scalar into every element
               (if (errp c) c (mk-arr ty k (a-lbs old) (a-ubs old) (repeat-v (prod (shape-of old)) (raw c)))))))))

(defun strip-cadrs-safe (ds) (declare (xargs :guard t)) (if (atom ds) nil (cons (kadr (car ds)) (strip-cadrs-safe (cdr ds)))))

(defun dummy-names (hd)              ; the dummies' names, in order
  (declare (xargs :guard t))
  (let ((ds (if (eq (kar hd) :function) (kadddr hd) (kar (kdr (kdr (kdr (kdr hd))))))))
    (strip-cadrs-safe ds)))
(defun result-name (hd)              ; a function's result variable (15.6.2.2)
  (declare (xargs :guard t))
  (if (kar (kdr (kdr (kdr (kdr hd))))) (kadr (kar (kdr (kdr (kdr (kdr hd)))))) (kadr (kaddr hd))))

(defun alist-fix (x) (declare (xargs :guard t)) (if (atom x) nil (if (consp (car x)) (cons (car x) (alist-fix (cdr x))) (alist-fix (cdr x)))))

(defun prefix-has (k hd) (declare (xargs :guard t)) (and (member-equal (list :kw k) (true-list-fix (kadr hd))) t))
(defun prefix-ts (hd) (declare (xargs :guard t)) (kar (cdr (assoc-equal :ts (alist-fix (kadr hd))))))
(defun unit-key (u) (declare (xargs :guard t)) (hd-name (kadr u)))
(defun unit-hd (u) (declare (xargs :guard t)) (kadr u))
(defun unit-spec (u) (declare (xargs :guard t)) (kaddr u))
(defun unit-exec (u) (declare (xargs :guard t)) (if (eq (kar u) :module) nil (kadddr u)))
(defun unit-int (u) (declare (xargs :guard t)) (if (eq (kar u) :module) (kadddr u) (kar (kdr (kdr (kdr (kdr u)))))))

; the frame binding a unit's internal (or a module's) procedures
(defun proc-frame (subs host)
  (declare (xargs :guard t))
  (if (atom subs) nil
    (cons (cons (tok-name (hd-name (unit-hd (car subs)))) (list :proc (car subs) host))
          (proc-frame (cdr subs) host))))

; ISO_FORTRAN_ENV's kind constants (16.10.2.17, .18)
(defconst *iso-frame*
  (list (cons "int8" (list :const (vi 4 1))) (cons "int16" (list :const (vi 4 2)))
        (cons "int32" (list :const (vi 4 4))) (cons "int64" (list :const (vi 4 8)))
        (cons "real32" (list :const (vi 4 4))) (cons "real64" (list :const (vi 4 8)))))

(defun only-frame (ns fr)            ; the bindings named in an only-list (14.2.2)
  (declare (xargs :guard t))
  (if (atom ns) nil
    (let ((b (alk (tok-name (car ns)) fr)))
      (if b (cons b (only-frame (cdr ns) fr)) (cons (cons (tok-name (car ns)) (list :missing)) (only-frame (cdr ns) fr))))))

; a use statement's frame, from the modules' frames mods (name -> frame)
(defun use-frame (u mods)
  (declare (xargs :guard t))
  (let* ((m (tok-name (kaddr u)))
         (fr (if (equal m "iso_fortran_env") *iso-frame* (cdr (alk m mods)))))
    (if (kadddr u) (only-frame (kar (kdr (kdr (kdr (kdr u))))) fr) fr)))
(defun use-frames (us mods)
  (declare (xargs :guard t))
  (if (atom us) nil (cons (use-frame (car us) mods) (use-frames (cdr us) mods))))

; an expression tree that is a lone name or a lone name(args), and nothing else
(defun lone-prim (e)                 ; the :prim tree, or nil
  (declare (xargs :guard t))
  (let* ((eq1 (kar e)) (or1 (kar eq1)) (and1 (kar or1)) (l4 (kadr and1)) (l2 (kar l4)) (add (kadr l2))
         (mult (kar add)) (prim (kar mult)))
    (and (null (kadr e)) (null (kadr eq1)) (null (kadr or1)) (null (kar and1))
         (null (kadr l4)) (null (kar l2)) (null (kaddr l2)) (null (kadr add)) (null (kadr mult))
         (member-eq (kar prim) '(:name :ref)) prim)))

; actual arguments matched to the dummies' names (15.5.2.1): positional
; first, then keywords; an alist name -> argument tree, or :arity
(defun match-kw (dns args acc)
  (declare (xargs :guard t :measure (len args)))
  (cond ((atom args) (if (atom dns) acc :arity))
        ((not (eq (kar (car args)) :kw)) :arity)
        (t (let ((n (tok-name (kadr (car args)))))
             (if (and (member-equal n dns) (not (alk n acc)))
                 (match-kw (remove-equal n dns) (cdr args) (cons (cons n (list :sub (kaddr (car args)))) acc))
               :arity)))))

(defun match-pos (dns args acc)
  (declare (xargs :guard t))
  (cond ((or (atom args) (eq (kar (car args)) :kw)) (match-kw dns args acc))
        ((atom dns) :arity)
        (t (match-pos (cdr dns) (cdr args) (cons (cons (car dns) (car args)) acc)))))
(defun drop-copies (dn cs)
  (declare (xargs :guard t))
  (if (atom cs) nil (if (equal (kar (car cs)) dn) (drop-copies dn (cdr cs)) (cons (car cs) (drop-copies dn (cdr cs))))))

(defun decl-dims (attrs)            ; DIMENSION's shapes, or nil
  (declare (xargs :guard t))
  (if (atom attrs) nil (if (eq (kar (car attrs)) :dimension) (kadr (car attrs)) (decl-dims (cdr attrs)))))
(defun decl-intent (attrs)
  (declare (xargs :guard t))
  (if (atom attrs) nil (if (eq (kar (car attrs)) :intent) (kadr (car attrs)) (decl-intent (cdr attrs)))))
(defun decl-has (a attrs) (declare (xargs :guard t)) (and (assoc-equal a (alist-fix attrs)) t))

(defun shapes-lower (ss)            ; assumed-shape lower bounds, nil where defaulted
  (declare (xargs :guard t))
  (if (atom ss) nil (cons (kadr (car ss)) (shapes-lower (cdr ss)))))
(defun all-assumed (ss) (declare (xargs :guard t)) (if (atom ss) t (and (eq (kar (car ss)) :as) (all-assumed (cdr ss)))))

(defun st-dovars-del (loc st) (declare (xargs :guard t)) (st-dovars-set (remove-equal loc (true-list-fix (st-dovars st))) st))

; ---- evaluation and execution, one mutual recursion on fuel
;
; cx = (g purep): g = (mods modenvs gframe), the modules' frames and scopes
; and the external procedures' frame; purep while in a pure procedure.

(defun cx-g (cx) (declare (xargs :guard t)) (kar cx))
(defun cx-pure (cx) (declare (xargs :guard t)) (kadr cx))
(defun g-mods (g) (declare (xargs :guard t)) (kar g))
(defun g-modenvs (g) (declare (xargs :guard t)) (kadr g))
(defun g-gframe (g) (declare (xargs :guard t)) (kaddr g))

(defun acons-raws (vs ty k)         ; an array constructor's elements (7.8): one type and kind
  (declare (xargs :guard t))
  (cond ((atom vs) nil)
        ((aval-p (car vs))
         (if (and (eq (a-ty (car vs)) ty) (equal (a-k (car vs)) k))
             (let ((rest (acons-raws (cdr vs) ty k))) (if (errp rest) rest (append (a-es (car vs)) rest)))
           (err :type)))
        ((and (eq (scal-ty (car vs)) ty) (equal (scal-k (car vs)) k) (not (eq (kar (car vs)) :u)))
         (let ((rest (acons-raws (cdr vs) ty k))) (if (errp rest) rest (cons (raw (car vs)) rest))))
        (t (err :type))))
(defun acons-val (vs)
  (declare (xargs :guard t))
  (let* ((v (kar vs)) (ty (if (aval-p v) (a-ty v) (scal-ty v))) (k (if (aval-p v) (a-k v) (scal-k v)))
         (es (acons-raws vs ty k)))
    (if (or (errp es) (not ty)) (err :type) (mk-arr ty k (list 1) (list (len es)) es))))

(defun section-shape (ds sc)          ; the extents of the triplet subscripts
  (declare (xargs :guard t))
  (if (or (atom ds) (atom sc)) nil
    (if (car sc) (section-shape (cdr ds) (cdr sc)) (cons (len (car ds)) (section-shape (cdr ds) (cdr sc))))))

(defun uppers (los exts)
  (declare (xargs :guard t))
  (if (or (atom los) (atom exts)) nil (cons (+ (ifix (car los)) (ifix (car exts)) -1) (uppers (cdr los) (cdr exts)))))

(defun proc-host (host suf cx)        ; the scope a procedure's body sees beyond its own
  (declare (xargs :guard t))
  (cond ((eq host :host) suf)
        ((eq (kar host) :mod) (cdr (alk (kadr host) (g-modenvs (cx-g cx)))))
        (t (list (g-gframe (cx-g cx))))))

; the temporaries of element, section and rebounded actuals written back
; into the caller's variables, newest first
(defun copy-back (copies fr st)
  (declare (xargs :guard t) (ignorable fr))
  (if (atom copies) st
    (let* ((c (car copies)) (v (st-get (kadr c) st)) (tg (kaddr c)) (loc (kadr tg)) (old (st-get loc st))
           (es (if (aval-p v) (a-es v) (list (raw v))))
           (new (case (kar tg)
                  (:tuples (arr-sets old (kaddr tg) es))
                  (:whole (if (aval-p old) (mk-arr (a-ty old) (a-k old) (a-lbs old) (a-ubs old) es) v))
                  (otherwise (if (aval-p old)
                                 (mk-arr (a-ty old) (a-k old) (a-lbs old) (a-ubs old)
                                         (append es (nthcdr (len es) (true-list-fix (a-es old)))))
                               v)))))
      (if (errp new) new (copy-back (cdr copies) fr (st-put loc new st))))))

; an elemental reference's arguments: the common shape of its arrays (nil
; when all are scalars, :bad when two differ), the scalars at element i
(defun elem-shape (vs)
  (declare (xargs :guard t))
  (if (atom vs) nil
    (let ((s (elem-shape (cdr vs))))
      (cond ((eq s :bad) :bad)
            ((not (aval-p (car vs))) s)
            ((or (null s) (equal s (shape-of (car vs)))) (shape-of (car vs)))
            (t :bad)))))
(defun val-args (vs i)
  (declare (xargs :guard t))
  (if (atom vs) nil
    (cons (list :val (if (aval-p (car vs)) (wrap (a-ty (car vs)) (a-k (car vs)) (nth-safe i (a-es (car vs)))) (car vs)))
          (val-args (cdr vs) i))))
(defun raw-list (rs) (declare (xargs :guard t)) (if (atom rs) nil (cons (raw (car rs)) (raw-list (cdr rs)))))

(defun elem-result (rs sh)
  (declare (xargs :guard t))
  (let ((ty (scal-ty (kar rs))) (k (scal-k (kar rs))))
    (if (aval-p (kar rs)) (err :type)
      (mk-arr (or ty :i) (or k 4) (ones (len sh)) sh (raw-list rs)))))
(defmacro with-v (vs form &rest body)    ; vs (v st): an error in v stops here
  `(mv-let ,vs ,form (if (errp ,(car vs)) (mv ,(car vs) ,(cadr vs)) (progn$ ,@body))))

(defun op-str (tk) (declare (xargs :guard t)) (kadr tk))
(defun ts-ty (name) (declare (xargs :guard t)) (cond ((equal name "integer") :i) ((equal name "real") :r) (t :l)))
(defun cond-err (v) (declare (xargs :guard t)) (if (pd-p v) (err :pd) (err :type)))   ; control on the processor's choice

; a real literal's value (R714): the significand's digits over a power of
; ten, scaled by the exponent, rounded to its kind -- default real, or
; double precision for the letter D (7.4.3.2p7)
(defun drop-dot (cs) (declare (xargs :guard t)) (if (atom cs) nil (if (eql (car cs) #\.) (cdr cs) (drop-dot (cdr cs)))))
(defun real-lit-q (m e)
  (declare (xargs :guard t))
  (let* ((cs (if (stringp m) (coerce m 'list) nil))
         (n (str-nat (remove #\. cs) 0))
         (fr (len (if (member #\. cs) (drop-dot cs) nil)))
         (ecs (if (stringp e) (coerce e 'list) nil))
         (x (cond ((eql (car ecs) #\-) (- (str-nat (cdr ecs) 0))) ((eql (car ecs) #\+) (str-nat (cdr ecs) 0)) (t (str-nat ecs 0)))))
    (* n (expt 10 (- (ifix x) fr)))))

(defun kind-of-param (kp env)       ; a kind-param's value: digits, or a named constant
  (declare (xargs :guard t))
  (cond ((digit-string-p kp) (digits-val kp))
        (t (mv-let (b suf d) (env-lookup kp env) (declare (ignore suf d))
             (if (and (eq (kar b) :const) (ival-scalar (kadr b))) (v-num (kadr b)) nil)))))

(defun lit-val (tk env)              ; R708, R709, R714, R725; a kind name is a named constant
  (declare (xargs :guard t))
  (if (eq (kar tk) :real)
      (let ((k (cond ((kar (cddddr tk)) (kind-of-param (kar (cddddr tk)) env)) ((equal (kaddr tk) "d") 8) (t 4))))
        (if (rkind-p k) (vr k (fl-round k (real-lit-q (kadr tk) (kadddr tk)))) (err :type)))
  (let* ((kp (kaddr tk))
         (k (cond ((null kp) 4)
                  ((digit-string-p kp) (digits-val kp))
                  (t (mv-let (b suf d) (env-lookup kp env) (declare (ignore suf d))
                       (if (and (eq (kar b) :const) (ival-scalar (kadr b))) (v-num (kadr b)) nil))))))
    (cond ((eq (kar tk) :char) (list :c (kadr tk)))
          ((not (ikind-p k)) (err :type))
          ((eq (kar tk) :log) (vl k (kadr tk)))
          (t (mk-int k (digits-val (kadr tk))))))))

; SELECT CASE (11.1.9): a case-value-range is the interval (lo . hi) of
; raw values, nil for an open end (11.1.9.2); an arm's selector is its
; intervals, or :default. A value lo > hi selects nothing. No value may
; lie in two arms' ranges (C1154): checked on every run.
(defun iv-hit (v iv)
  (declare (xargs :guard t))
  (let ((lo (kar iv)) (hi (kdr iv)))
    (if (booleanp v) (equal lo v)
      (and (rationalp v) (or (null lo) (and (rationalp lo) (<= lo v))) (or (null hi) (and (rationalp hi) (<= v hi)))))))
(defun ivs-hit (v ivs) (declare (xargs :guard t)) (if (atom ivs) nil (or (iv-hit v (car ivs)) (ivs-hit v (cdr ivs)))))
(defun iv-meet (a b)                 ; two intervals share a value
  (declare (xargs :guard t))
  (let ((alo (kar a)) (ahi (kdr a)) (blo (kar b)) (bhi (kdr b)))
    (if (or (booleanp alo) (booleanp blo)) (equal alo blo)
      (and (or (null alo) (null bhi) (and (rationalp alo) (rationalp bhi) (<= alo bhi)))
           (or (null blo) (null ahi) (and (rationalp blo) (rationalp ahi) (<= blo ahi)))
           (or (null alo) (null ahi) (and (rationalp alo) (rationalp ahi) (<= alo ahi)))
           (or (null blo) (null bhi) (and (rationalp blo) (rationalp bhi) (<= blo bhi)))))))
(defun iv-meet-any (a bs) (declare (xargs :guard t)) (if (atom bs) nil (or (iv-meet a (car bs)) (iv-meet-any a (cdr bs)))))
(defun ivs-meet (as bs) (declare (xargs :guard t)) (if (atom as) nil (or (iv-meet-any (car as) bs) (ivs-meet (cdr as) bs))))
(defun all-ivs (sels) (declare (xargs :guard t)) (if (atom sels) nil (append (if (eq (car sels) :default) nil (true-list-fix (car sels))) (all-ivs (cdr sels)))))
(defun ivs-disjoint (ivs)            ; no two intervals of the list share a value
  (declare (xargs :guard t))
  (if (atom ivs) t (and (not (iv-meet-any (car ivs) (cdr ivs))) (ivs-disjoint (cdr ivs)))))
(defun sel-pick (v sels i dflt)      ; the arm whose ranges hold v, else the default's, else nil
  (declare (xargs :guard t))
  (cond ((atom sels) dflt)
        ((eq (car sels) :default) (sel-pick v (cdr sels) (+ 1 (nfix i)) (nfix i)))
        ((ivs-hit v (car sels)) (nfix i))
        (t (sel-pick v (cdr sels) (+ 1 (nfix i)) dflt))))
(defun case-raw (ty v)               ; a case value of the case expression's type, as a raw value
  (declare (xargs :guard t))
  (cond ((and (eq ty :i) (ival-scalar v)) (v-num v))
        ((and (eq ty :l) (lval-p v) (booleanp (v-num v))) (v-num v))
        (t :bad)))

; DO CONCURRENT (11.1.7.4.2, 11.1.7.5): the iterations may run in any
; order; the model runs them in array element order of the index tuples
; and checks what makes the order not matter (11.1.7.5p7, unspecified
; locality): a variable referenced in an iteration is defined earlier in
; that iteration, or by no other iteration; one defined by two
; iterations is undefined after the loop. A definition is seen where it
; is an assignment to it, or a change of its value by any other means.
(defun key-meet (a b)                ; two accesses (k loc off) of one variable or element
  (declare (xargs :guard t))
  (and (equal (kadr a) (kadr b)) (or (eq (kaddr a) :all) (eq (kaddr b) :all) (equal (kaddr a) (kaddr b)))))
(defun meets-any (e es) (declare (xargs :guard t)) (if (atom es) nil (or (key-meet e (car es)) (meets-any e (cdr es)))))
(defun any-meet (as bs) (declare (xargs :guard t)) (if (atom as) nil (or (meets-any (car as) bs) (any-meet (cdr as) bs))))
(defun iter-sets (es ws rs)          ; an iteration's accesses, oldest first: (mv defs refs-before-own-def)
  (declare (xargs :guard t))
  (if (atom es) (mv ws rs)
    (let ((e (car es)))
      (if (eq (kar e) :w) (iter-sets (cdr es) (cons e ws) rs)
        (iter-sets (cdr es) ws (if (meets-any e ws) rs (cons e rs)))))))
(defun ws-of (sets) (declare (xargs :guard t)) (if (atom sets) nil (append (true-list-fix (kar (car sets))) (ws-of (cdr sets)))))
(defun conc-bad (pre post)           ; some iteration refers to what another defines
  (declare (xargs :guard t :measure (acl2-count post)))
  (if (atom post) nil
    (or (any-meet (kdr (car post)) (append (ws-of pre) (ws-of (cdr post))))
        (conc-bad (cons (car post) pre) (cdr post)))))
(defun multi-1 (ws others) (declare (xargs :guard t))
  (if (atom ws) nil (if (meets-any (car ws) others) (cons (car ws) (multi-1 (cdr ws) others)) (multi-1 (cdr ws) others))))
(defun conc-multi (pre post)         ; what two iterations define
  (declare (xargs :guard t :measure (acl2-count post)))
  (if (atom post) nil
    (append (multi-1 (true-list-fix (kar (car post))) (append (ws-of pre) (ws-of (cdr post))))
            (conc-multi (cons (car post) pre) (cdr post)))))
(defun undef-val (v off)
  (declare (xargs :guard t))
  (cond ((and (aval-p v) (eq off :all)) (mk-arr (a-ty v) (a-k v) (a-lbs v) (a-ubs v) (repeat-v (len (a-es v)) :u)))
        ((aval-p v) (mk-arr (a-ty v) (a-k v) (a-lbs v) (a-ubs v) (upd-safe off :u (a-es v))))
        (t (list :u (scal-ty v) (scal-k v)))))
(defun undef-all (es st)
  (declare (xargs :guard t))
  (if (atom es) st (undef-all (cdr es) (st-put (kadr (car es)) (undef-val (st-get (kadr (car es)) st) (kaddr (car es))) st))))
(defun drop-locs (es locs)           ; accesses not of the index variables
  (declare (xargs :guard t))
  (if (atom es) nil (if (member-equal (kadr (car es)) locs) (drop-locs (cdr es) locs) (cons (car es) (drop-locs (cdr es) locs)))))
(defun conc-frame (names ks vals st) ; each index a construct entity of its own (11.1.7.5p1): (mv frame locs st)
  (declare (xargs :guard t))
  (if (or (atom names) (atom vals)) (mv nil nil st)
    (mv-let (loc st) (st-new (vi (kar ks) (car vals)) st)
      (mv-let (fr locs st) (conc-frame (cdr names) (kdr ks) (cdr vals) st)
        (mv (cons (cons (car names) (list :var loc :rw)) fr) (cons loc locs) st)))))
(defun strip-cars-safe (ds) (declare (xargs :guard t)) (if (atom ds) nil (cons (kar (car ds)) (strip-cars-safe (cdr ds)))))
(defun strip-caddrs-safe (ds) (declare (xargs :guard t)) (if (atom ds) nil (cons (kaddr (car ds)) (strip-caddrs-safe (cdr ds)))))

(mutual-recursion

 (defun me-ev (nt x env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel) :verify-guards nil))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (case nt
       ((:expr :equiv :or :add)
        (with-v (v st) (me-ev (lev-sub nt) (kar x) env st cx (1- fuel))
          (me-fold nt (kadr x) v env st cx (1- fuel))))
       (:and (with-v (v st) (me-ev :l4 (kadr x) env st cx (1- fuel))
               (mv (if (kar x) (val-op :not v nil) v) st)))
       (:l4 (with-v (a st) (me-ev :l2 (kar x) env st cx (1- fuel))
              (if (kadr x)
                  (with-v (b st) (me-ev :l2 (kaddr x) env st cx (1- fuel))
                    (mv (val-op (op-str (kadr x)) a b) st))
                (mv a st))))
       (:l2 (with-v (a st) (me-ev :add (kadr x) env st cx (1- fuel))
              (let ((a (cond ((equal (kar x) (op "-")) (val-op :neg a nil))
                             ((and (kar x) (not (or (num-p a) (pd-p a) (and (aval-p a) (member-eq (a-ty a) '(:i :r)))))) (err :type))
                             (t a))))
                (if (errp a) (mv a st) (me-fold :l2* (kaddr x) a env st cx (1- fuel))))))
       (:mult (with-v (a st) (me-ev :prim (kar x) env st cx (1- fuel))
                (if (kadr x)
                    (with-v (b st) (me-ev :mult (kadr x) env st cx (1- fuel))
                      (mv (val-op "**" a b) st))
                  (mv a st))))
       (:prim
        (case (kar x)
          (:lit (mv (lit-val (kadr x) env) st))
          (:paren (me-ev :expr (kadr x) env st cx (1- fuel)))
          (:acons (with-v (vs st) (me-list (kadr x) env st cx (1- fuel))
                    (mv (acons-val vs) st)))
          (:name (mv-let (b suf d) (env-lookup (tok-name (kadr x)) env)
                   (declare (ignore suf d))
                   (case (kar b)
                     (:var (let ((v (st-get (kadr b) st)))
                             (if (undef-in v) (mv (err :undefined) st) (mv v (st-log (list (list :r (kadr b) :all)) st)))))
                     (:const (mv (kadr b) st))
                     ((nil) (mv (err :undeclared) st))
                     (otherwise (mv (err :type) st)))))
          (:ref (me-ref (kadr x) (kaddr x) env st cx (1- fuel)))
          (otherwise (mv (err :syntax) st))))
       (otherwise (mv (err :syntax) st)))))

 ; the (op operand) list after a level's first operand, left to right
 (defun me-fold (nt rest v env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((atom rest) (mv v st))
         ; 10.1.7: an operand the value does not need (.and. after false,
         ; .or. after true) need not be evaluated: an error in it is then
         ; the processor's choice, and the value too
         ((let ((op (op-str (kar (car rest)))))
            (and (lval-p v) (booleanp (v-num v))
                 (or (and (equal op ".and.") (not (v-num v))) (and (equal op ".or.") (v-num v)))))
          (mv-let (b st) (me-ev (lev-sub nt) (kadr (car rest)) env st cx (1- fuel))
            (me-fold nt (cdr rest) (if (errp b) (list :pd :l (v-kind v)) v) env st cx (1- fuel))))
         (t (with-v (b st) (me-ev (lev-sub nt) (kadr (car rest)) env st cx (1- fuel))
              (let ((r (val-op (op-str (kar (car rest))) v b)))
                (if (errp r) (mv r st) (me-fold nt (cdr rest) r env st cx (1- fuel))))))))

 (defun me-list (es env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((atom es) (mv nil st))
         (t (with-v (v st) (me-ev :expr (car es) env st cx (1- fuel))
              (with-v (vs st) (me-list (cdr es) env st cx (1- fuel))
                (mv (cons v vs) st))))))

 ; an intrinsic's arguments: values, and keyword values (16.9.1); an
 ; inquiry function's variable argument need not be defined (16.1)
 (defun me-iargs (args inq env st cx fuel)      ; (mv vals-or-err kw st)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) nil st))
         ((atom args) (mv nil nil st))
         ((member-eq (kar (car args)) '(:sub :kw))
          (mv-let (v st) (let* ((e (if (eq (kar (car args)) :sub) (kadr (car args)) (kaddr (car args))))
                                (p (and inq (lone-prim e))))
                           (mv-let (b suf d) (if (eq (kar p) :name) (env-lookup (tok-name (kadr p)) env) (mv nil nil 0))
                             (declare (ignore suf d))
                             (if (eq (kar b) :var) (mv (st-get (kadr b) st) st)
                               (me-ev :expr e env st cx (1- fuel)))))
            (if (errp v) (mv v nil st)
              (mv-let (vs kw st) (me-iargs (cdr args) inq env st cx (1- fuel))
                (cond ((errp vs) (mv vs nil st))
                      ((eq (kar (car args)) :kw) (mv vs (cons (cons (tok-name (kadr (car args))) v) kw) st))
                      (t (mv (cons v vs) kw st)))))))
         (t (mv (err :type) nil st))))

 ; subscripts of array a: per subscript, the list of indices, and whether
 ; it is a scalar subscript (9.5.3.3: a section keeps its triplets' ranks)
 (defun me-subs (args lbs ubs env st cx fuel)  ; (mv dims-or-err scal st)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) nil st))
         ((atom args) (mv (if (atom lbs) nil (err :bounds)) nil st))
         ((atom lbs) (mv (err :bounds) nil st))
         ((eq (kar (car args)) :sub)
          (mv-let (v st) (me-ev :expr (kadr (car args)) env st cx (1- fuel))
            (cond ((errp v) (mv v nil st))
                  ((not (ival-scalar v)) (mv (err :type) nil st))   ; a vector subscript is not in the subset
                  (t (mv-let (ds sc st) (me-subs (cdr args) (cdr lbs) (cdr ubs) env st cx (1- fuel))
                       (if (errp ds) (mv ds nil st) (mv (cons (list (v-num v)) ds) (cons t sc) st)))))))
         ((eq (kar (car args)) :tri)
          (mv-let (lo st) (if (kadr (car args)) (me-ev :expr (kadr (car args)) env st cx (1- fuel)) (mv (vi 8 (kar lbs)) st))
            (mv-let (hi st) (if (kaddr (car args)) (me-ev :expr (kaddr (car args)) env st cx (1- fuel)) (mv (vi 8 (kar ubs)) st))
              (mv-let (sd st) (if (kadddr (car args)) (me-ev :expr (kadddr (car args)) env st cx (1- fuel)) (mv (vi 8 1) st))
                (cond ((errp lo) (mv lo nil st)) ((errp hi) (mv hi nil st)) ((errp sd) (mv sd nil st))
                      ((not (and (ival-scalar lo) (ival-scalar hi) (ival-scalar sd))) (mv (err :type) nil st))
                      ((= (v-num sd) 0) (mv (err :step) nil st))       ; 9.5.3.3.3: the stride shall not be zero
                      (t (let ((is (range-idx (v-num lo) (v-num hi) (v-num sd) (range-count (v-num lo) (v-num hi) (v-num sd)))))
                           (mv-let (ds sc st) (me-subs (cdr args) (cdr lbs) (cdr ubs) env st cx (1- fuel))
                             (if (errp ds) (mv ds nil st) (mv (cons is ds) (cons nil sc) st))))))))))
         (t (mv (err :type) nil st))))

 ; name(args): an array element or section, a function reference, or an intrinsic
 (defun me-ref (tk args env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (mv-let (b suf d) (env-lookup (tok-name tk) env)
       (declare (ignore d))
       (case (kar b)
         ((:var :const)
          (let ((a (if (eq (kar b) :var) (st-get (kadr b) st) (kadr b))))
            (if (not (aval-p a)) (mv (err :type) st)
              (mv-let (ds sc st) (me-subs args (a-lbs a) (a-ubs a) env st cx (1- fuel))
                (if (errp ds) (mv ds st)
                  (let ((es (arr-gets a (tuples ds)))
                        (st (if (eq (kar b) :var) (st-log (read-list (kadr b) (tuple-offs a (tuples ds))) st) st)))
                    (cond ((errp es) (mv es st))
                          ((member :u es) (mv (err :undefined) st))
                          ((not (member nil sc)) (mv (wrap (a-ty a) (a-k a) (car es)) st))
                          (t (let ((sh (section-shape ds sc)))
                               (mv (mk-arr (a-ty a) (a-k a) (ones (len sh)) sh es) st))))))))))
         (:proc (let ((u (kadr b)))
                  (cond ((not (eq (kar (unit-hd u)) :function)) (mv (err :type) st))
                        ; an elemental reference (15.9.2): on arrays, the function
                        ; applied element by element in array element order
                        ((prefix-has "elemental" (unit-hd u))
                         (with-v (vs st) (mv-let (vs kw st) (me-iargs args nil env st cx (1- fuel))
                                           (mv (cond ((errp vs) vs) (kw (err :type)) (t (list :ok vs))) st))
                           (let* ((vs (kadr vs)) (sh (elem-shape vs)))
                             (cond ((eq sh :bad) (mv (err :shape) st))
                                   ((null sh) (me-call u (proc-host (kaddr b) suf cx) (val-args vs 0) env st cx (1- fuel)))
                                   (t (with-v (rs st) (me-elem u (proc-host (kaddr b) suf cx) vs 0 (prod sh) env st cx (1- fuel))
                                        (mv (elem-result rs sh) st)))))))
                        (t (me-call u (proc-host (kaddr b) suf cx) args env st cx (1- fuel))))))
         ((nil) (with-v (vs st) (mv-let (vs kw st) (me-iargs args (member-equal (tok-name tk) '("size" "lbound" "ubound" "kind" "huge")) env st cx (1- fuel))
                                  (mv (if (errp vs) vs (list :ok vs kw)) st))
                  (mv (intrinsic (tok-name tk) (kadr vs) (kaddr vs)) st)))
         (otherwise (mv (err :type) st))))))

 (defun me-elem (u host vs i n env st cx fuel)   ; the results at elements i .. n-1
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((not (and (natp i) (natp n) (< i n))) (mv nil st))
         (t (with-v (r st) (me-call u host (val-args vs i) env st cx (1- fuel))
              (with-v (rs st) (me-elem u host vs (+ 1 i) n env st cx (1- fuel))
                (mv (cons r rs) st))))))

 ; a call: bind the arguments, elaborate the specification, run the body,
 ; copy back; a function answers its result, a subroutine its status
 (defun me-call (u host args env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (let* ((hd (unit-hd u))
            (fn (eq (kar hd) :function))
            (purep (or (prefix-has "pure" hd) (and (prefix-has "elemental" hd) (not (prefix-has "impure" hd)))))
            (m (match-pos (dummy-names hd) args nil)))
       (cond
        ((and (cx-pure cx) (not purep)) (mv (err :pure) st))   ; C1599: a pure procedure calls only pure ones
        ((and (st-trace st) (not purep)) (mv (err :concurrent) st))   ; C1143: no impure reference in DO CONCURRENT
        ((not (alistp m)) (mv (err :arity) st))
        (t
         (mv-let (e fr copies st) (me-bind (dummy-names hd) m env st cx (1- fuel) nil nil)
           (if e (mv e st)
             (mv-let (fr st)                           ; the result variable, typed by the prefix
               (if (and fn (prefix-ts hd))
                   (mv-let (k st) (me-kind (prefix-ts hd) env st cx (1- fuel))
                     (if (errp k) (mv k st)
                       (mv-let (loc st) (st-new (list :u (ts-ty (kar (prefix-ts hd))) k) st)
                         (mv (cons (cons (result-name hd) (list :var loc :rw)) fr) st))))
                 (mv fr st))
               (if (errp fr) (mv fr st)
                 (let* ((spec (unit-spec u))
                        (ufr (use-frames (kar spec) (g-mods (cx-g cx))))
                        (fr (append (proc-frame (kadr (unit-int u)) :host) fr))
                        (cx2 (list (cx-g cx) purep)))
                   (mv-let (e fr copies st) (me-decls (kaddr spec) (append ufr host) st cx2 (1- fuel) fr copies
                                                      (unit-key u) (dummy-names hd))
                     (if e (mv e st)
                       (let ((env2 (cons fr (append ufr host))))
                         (mv-let (s st) (me-blk (unit-exec u) env2 st cx2 (1- fuel))
                           (cond ((errp s) (mv s st))
                                 ((not (member-eq s '(:normal :return))) (mv (err :syntax) st))
                                 (t (let ((st (copy-back copies fr st)))
                                      (if (errp st) (mv st nil)
                                        (if (not fn) (mv :normal st)
                                          (let ((rb (cdr (alk (result-name hd) fr))))
                                            (if (not (eq (kar rb) :var)) (mv (err :undeclared) st)
                                              (let ((v (st-get (kadr rb) st)))
                                                (if (undef-in v) (mv (err :undefined) st) (mv v st))))))))))))))))))))))))

 ; each dummy dn bound to its actual: a whole variable by reference; an
 ; element or section to a temporary copied back; an expression to a
 ; temporary that is not definable (15.5.2.4)
 (defun me-bind (dns m env st cx fuel fr copies)   ; (mv err fr copies st)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) nil nil st))
         ((atom dns) (mv nil fr copies st))
         (t (let* ((dn (car dns)) (a (cdr (alk dn m))))
              (if (eq (kar a) :val)
                  (mv-let (loc st) (st-new (kadr a) st)
                    (me-bind (cdr dns) m env st cx (1- fuel) (cons (cons dn (list :var loc :in)) fr) copies))
              (if (not (eq (kar a) :sub)) (mv (err (if a :type :arity)) nil nil st)
                (let* ((e (kadr a)) (p (lone-prim e)))
                  (mv-let (b suf d) (if p (env-lookup (tok-name (kadr p)) env) (mv nil nil 0))
                    (declare (ignore suf d))
                    (cond
                     ((and p (eq (kar p) :name) (eq (kar b) :var))
                      (me-bind (cdr dns) m env st cx (1- fuel) (cons (cons dn b) fr) copies))
                     ((and p (eq (kar p) :ref) (eq (kar b) :var) (aval-p (st-get (kadr b) st)))
                      (let ((arr (st-get (kadr b) st)))
                        (mv-let (ds sc st) (me-subs (kaddr p) (a-lbs arr) (a-ubs arr) env st cx (1- fuel))
                          (if (errp ds) (mv ds nil nil st)
                            (let* ((ts (tuples ds)) (es (arr-gets arr ts)))
                              (if (errp es) (mv es nil nil st)
                                (let ((v (if (member nil sc)
                                             (let ((sh (section-shape ds sc))) (mk-arr (a-ty arr) (a-k arr) (ones (len sh)) sh es))
                                           (wrap (a-ty arr) (a-k arr) (car es)))))
                                  (mv-let (loc st) (st-new v st)
                                    (me-bind (cdr dns) m env st cx (1- fuel) (cons (cons dn (list :var loc :rw)) fr)
                                             (cons (list dn loc (list :tuples (kadr b) ts)) copies))))))))))
                     (t (mv-let (v st) (me-ev :expr e env st cx (1- fuel))
                          (if (errp v) (mv v nil nil st)
                            (mv-let (loc st) (st-new v st)
                              (me-bind (cdr dns) m env st cx (1- fuel) (cons (cons dn (list :var loc :in)) fr) copies))))))))))))))

 ; a kind selector's value (R706): a scalar integer constant expression
 (defun me-kind (ts env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (if (null (kadr ts)) (mv 4 st)
       (with-v (v st) (me-ev :expr (kadr (kadr ts)) env st cx (1- fuel))
         (if (and (ival-scalar v) (if (equal (kar ts) "real") (rkind-p (v-num v)) (ikind-p (v-num v))))
             (mv (v-num v) st) (mv (err :type) st))))))

 ; explicit bounds (R815): (mv lbs-or-err ubs st)
 (defun me-bounds (ss env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) nil st))
         ((atom ss) (mv nil nil st))
         (t (mv-let (lo st) (if (kadr (car ss)) (me-ev :expr (kadr (car ss)) env st cx (1- fuel)) (mv (vi 4 1) st))
              (mv-let (hi st) (me-ev :expr (kaddr (car ss)) env st cx (1- fuel))
                (cond ((errp lo) (mv lo nil st)) ((errp hi) (mv hi nil st))
                      ((not (and (ival-scalar lo) (ival-scalar hi))) (mv (err :type) nil st))
                      (t (mv-let (ls us st) (me-bounds (cdr ss) env st cx (1- fuel))
                           (if (errp ls) (mv ls nil st) (mv (cons (v-num lo) ls) (cons (v-num hi) us) st))))))))))

 ; the declarations, in order (8.2): each entity's binding in fr
 (defun me-decls (ds env st cx fuel fr copies key dns)   ; (mv err fr copies st)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) nil nil st))
         ((atom ds) (if (subsetp-equal dns (strip-cars (alist-fix fr))) (mv nil fr copies st)
                      (mv (err :undeclared) nil nil st)))      ; the subset has no implicit typing
         (t (let* ((d (car ds)) (ts (kadr d)) (attrs (kaddr d)))
              (mv-let (k st) (me-kind ts (cons fr env) st cx (1- fuel))
                (if (errp k) (mv k nil nil st)
                  (mv-let (e fr copies st) (me-ents (kar (kdr (kdr (kdr (kdr d))))) (ts-ty (kar ts)) k attrs
                                                    env st cx (1- fuel) fr copies key dns)
                    (if e (mv e nil nil st) (me-decls (cdr ds) env st cx (1- fuel) fr copies key dns)))))))))

 (defun me-ents (ents ty k attrs env st cx fuel fr copies key dns)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) nil nil st))
         ((atom ents) (mv nil fr copies st))
         (t (let* ((ent (car ents)) (n (tok-name (kar ent)))
                   (ss (or (kadr ent) (decl-dims attrs))) (init (kaddr ent)) (envf (cons fr env)))
              (mv-let (e fr copies st)
                (cond
                 ((decl-has :parameter attrs)                    ; 8.5.13: a named constant
                  (if (null init) (mv (err :syntax) nil nil st)
                    (mv-let (v st) (me-ev :expr init envf st cx (1- fuel))
                      (let ((c (if (errp v) v (if (and ss (aval-p v)) (assign-val (fresh ty k (a-lbs v) (a-ubs v)) v) (conv1 ty k v)))))
                        (if (errp c) (mv c nil nil st) (mv nil (cons (cons n (list :const c)) fr) copies st))))))
                 ((member-equal n dns)                           ; a dummy: its actual's binding
                  (me-dummy n ty k ss attrs envf st cx (1- fuel) fr copies))
                 (t
                  (mv-let (ls us st) (if (and ss (not (all-assumed ss))) (me-bounds ss envf st cx (1- fuel)) (mv nil nil st))
                    (cond
                     ((errp ls) (mv ls nil nil st))
                     ((and ss (all-assumed ss)) (mv (err :syntax) nil nil st))   ; assumed shape only for a dummy (C836)
                     ((and init (assoc-equal (list key n) (st-saves st)))       ; saved: its location already
                      (mv nil (cons (cons n (list :var (cdr (assoc-equal (list key n) (st-saves st))) :rw)) fr) copies st))
                     (init
                      (mv-let (v st) (me-ev :expr init envf st cx (1- fuel))
                        (let ((c (if (errp v) v (assign-val (fresh ty k ls us) v))))
                          (if (errp c) (mv c nil nil st)
                            (mv-let (loc st) (st-new c st)
                              (mv nil (cons (cons n (list :var loc :rw)) fr) copies (st-save (list key n) loc st)))))))
                     (t (mv-let (loc st) (st-new (fresh ty k ls us) st)
                          (mv nil (cons (cons n (list :var loc :rw)) fr) copies st)))))))
                (if e (mv e nil nil st) (me-ents (cdr ents) ty k attrs env st cx (1- fuel) fr copies key dns)))))))

 ; a dummy's declaration against its actual (15.5.2.4): type and kind agree;
 ; VALUE takes a copy; INTENT(IN) is not definable; INTENT(OUT) becomes
 ; undefined (15.5.2.5) and needs a definable actual; an assumed-shape
 ; dummy takes the actual's shape with its own lower bounds (8.5.8.3); an
 ; explicit-shape one the actual's leading elements (15.5.2.12)
 (defun me-dummy (n ty k ss attrs env st cx fuel fr copies)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) nil nil st)
     (let* ((b (cdr (alk n fr))) (loc (kadr b)) (v (st-get loc st)) (int (decl-intent attrs)))
       (cond
        ((not (equal (list (if (aval-p v) (a-ty v) (scal-ty v)) (if (aval-p v) (a-k v) (scal-k v))) (list ty k)))
         (mv (err :type) nil nil st))
        ((if ss (not (aval-p v)) (aval-p v)) (mv (err :type) nil nil st))
        ((and (member-equal int '(("out") ("inout") ("in" "out"))) (eq (kaddr b) :in)) (mv (err :intent) nil nil st))
        (t
         (mv-let (ls us st)
           (cond ((not ss) (mv nil nil st))
                 ((all-assumed ss)
                  (mv-let (los st) (me-lowers (shapes-lower ss) env st cx (1- fuel))
                    (mv los (if (errp los) nil (uppers los (extents (a-lbs v) (a-ubs v)))) st)))
                 (t (me-bounds ss env st cx (1- fuel))))
           (cond
            ((errp ls) (mv ls nil nil st))
            ((and ss (not (equal (len ls) (len (a-lbs v)))) (all-assumed ss)) (mv (err :shape) nil nil st))
            ((and ss (not (all-assumed ss)) (< (prod (extents (a-lbs v) (a-ubs v))) (prod (extents ls us))))
             (mv (err :shape) nil nil st))
            (t
             (let* ((rebound (and ss (not (equal (list ls us) (list (a-lbs v) (a-ubs v))))))
                    (v2 (if rebound (mk-arr ty k ls us (take (prod (extents ls us)) (a-es v))) v))
                    (v3 (if (equal int '("out")) (if ss (fresh ty k ls us) (list :u ty k)) v2)))
               (cond
                ((decl-has :value attrs)
                 (mv-let (l2 st) (st-new v3 st)
                   (mv nil (cons (cons n (list :var l2 :rw)) fr) (drop-copies n copies) st)))
                (rebound
                 (mv-let (l2 st) (st-new v3 st)
                   (mv nil (cons (cons n (list :var l2 (if (equal int '("in")) :in (kaddr b)))) fr)
                       (if (equal int '("in")) (drop-copies n copies)
                         (cons (list n l2 (if (all-assumed ss) (list :whole loc) (list :prefix loc))) copies))
                       st)))
                ((equal int '("in"))
                 (mv nil (cons (cons n (list :var loc :in)) fr) (drop-copies n copies) st))
                ((equal int '("out")) (mv nil fr copies (st-put loc v3 st)))
                (t (mv nil fr copies st))))))))))))

 (defun me-lowers (los env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((atom los) (mv nil st))
         (t (mv-let (v st) (if (car los) (me-ev :expr (car los) env st cx (1- fuel)) (mv (vi 4 1) st))
              (cond ((errp v) (mv v st))
                    ((not (ival-scalar v)) (mv (err :type) st))
                    (t (with-v (vs st) (me-lowers (cdr los) env st cx (1- fuel)) (mv (cons (v-num v) vs) st))))))))

 ; ---- statements

 (defun me-blk (cs env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((atom cs) (mv :normal st))
         (t (mv-let (s st) (me-c (car cs) env st cx (1- fuel))
              (if (eq s :normal) (me-blk (cdr cs) env st cx (1- fuel)) (mv s st))))))

 (defun me-c (c env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (case (kar c)
       (:act (me-act (kadr c) env st cx (1- fuel)))
       (:ifc (with-v (v st) (me-ev :expr (kadr c) env st cx (1- fuel))
               (cond ((not (and (lval-p v) (booleanp (v-num v)))) (mv (cond-err v) st))
                     ((v-num v) (me-blk (kaddr c) env st cx (1- fuel)))
                     (t (me-eifs (kadddr c) (kar (kdr (kdr (kdr (kdr c))))) env st cx (1- fuel))))))
       (:doc (me-do (kadr c) (kaddr c) env st cx (1- fuel)))
       (:casec (with-v (v st) (me-ev :expr (kadr c) env st cx (1- fuel))
                 (let ((ty (cond ((ival-scalar v) :i) ((and (lval-p v) (booleanp (v-num v))) :l) (t nil))))
                   (if (not ty) (mv (cond-err v) st)            ; C1150: integer, logical (or character)
                     (mv-let (sels st) (me-sels (kaddr c) ty env st cx (1- fuel))
                       (cond ((errp sels) (mv sels st))
                             ((not (ivs-disjoint (all-ivs sels))) (mv (err :case) st))
                             (t (let ((i (sel-pick (v-num v) sels 0 nil)))
                                  (if (natp i) (me-blk (kadr (nth i (true-list-fix (kaddr c)))) env st cx (1- fuel))
                                    (mv :normal st))))))))))
       (otherwise (mv (err :syntax) st)))))

 ; each arm's selector: its ranges' intervals, or :default
 (defun me-sels (arms ty env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((atom arms) (mv nil st))
         (t (mv-let (ivs st) (if (equal (kar (car arms)) '(:case-default)) (mv :default st)
                               (me-ranges (kadr (kar (car arms))) ty env st cx (1- fuel)))
              (if (errp ivs) (mv ivs st)
                (mv-let (rest st) (me-sels (cdr arms) ty env st cx (1- fuel))
                  (if (errp rest) (mv rest st) (mv (cons ivs rest) st))))))))

 (defun me-ranges (rs ty env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((atom rs) (mv nil st))
         (t (let* ((r (car rs)) (open (member-eq (kar r) '(:from :to :rng))))
              (mv-let (a st) (me-ev :expr (kadr r) env st cx (1- fuel))
                (mv-let (b st) (if (eq (kar r) :rng) (me-ev :expr (kaddr r) env st cx (1- fuel)) (mv a st))
                  (let ((x (case-raw ty a)) (y (case-raw ty b)))
                    (cond ((errp a) (mv a st)) ((errp b) (mv b st))
                          ((or (eq x :bad) (eq y :bad)) (mv (err :type) st))   ; C1152: the case expression's type
                          ((and open (eq ty :l)) (mv (err :type) st))         ; C1153: no logical ranges
                          (t (mv-let (rest st) (me-ranges (cdr rs) ty env st cx (1- fuel))
                               (if (errp rest) (mv rest st)
                                 (mv (cons (case (kar r) (:from (cons x nil)) (:to (cons nil x)) (otherwise (cons x y))) rest)
                                     st))))))))))))

 (defun me-eifs (eifs els env st cx fuel)    ; 11.1.8.2: the first true condition's block
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((atom eifs) (if (consp els) (me-blk (car els) env st cx (1- fuel)) (mv :normal st)))
         (t (with-v (v st) (me-ev :expr (kar (car eifs)) env st cx (1- fuel))
              (cond ((not (and (lval-p v) (booleanp (v-num v)))) (mv (cond-err v) st))
                    ((v-num v) (me-blk (kadr (car eifs)) env st cx (1- fuel)))
                    (t (me-eifs (cdr eifs) els env st cx (1- fuel))))))))

 ; 11.1.7.4.1: the parameters evaluated and converted to the DO variable's
 ; kind, the iteration count max((m2-m1+m3)/m3, 0), the variable set to m1
 (defun me-do (ctl blk env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (case (kar ctl)
       (:range
        (mv-let (b suf d) (env-lookup (tok-name (kaddr ctl)) env)
          (declare (ignore suf))
          (let ((loc (kadr b)))
            (cond ((not (and (eq (kar b) :var) (eq (scal-ty (st-get loc st)) :i))) (mv (err :type) st))
                  ((eq (kaddr b) :in) (mv (err :intent) st))
                  ((and (cx-pure cx) (not (equal d 0))) (mv (err :pure) st))
                  (t (let ((k (scal-k (st-get loc st))))
                       (with-v (m1 st) (me-ev :expr (kadddr ctl) env st cx (1- fuel))
                         (with-v (m2 st) (me-ev :expr (kar (kdr (kdr (kdr (kdr ctl))))) env st cx (1- fuel))
                           (with-v (m3 st) (if (kadr (kdr (kdr (kdr (kdr ctl)))))
                                               (me-ev :expr (kadr (kdr (kdr (kdr (kdr ctl))))) env st cx (1- fuel))
                                             (mv (vi k 1) st))
                             (let ((m1 (conv1 :i k m1)) (m2 (conv1 :i k m2)) (m3 (conv1 :i k m3)))
                               (cond ((errp m1) (mv m1 st)) ((errp m2) (mv m2 st)) ((errp m3) (mv m3 st))
                                     ((= (v-num m3) 0) (mv (err :step) st))
                                     ((member loc (st-dovars st)) (mv (err :do-var) st))
                                     (t (let ((st (st-dovars-set (cons loc (true-list-fix (st-dovars st))) (st-put loc m1 st))))
                                          (mv-let (s st) (me-iter loc (v-num m3) (max 0 (idiv (+ (- (v-num m2) (v-num m1)) (v-num m3)) (v-num m3)))
                                                                  blk env st cx (1- fuel))
                                            (mv s (st-dovars-del loc st))))))))))))))))
       (:while (me-while (kaddr ctl) blk env st cx (1- fuel)))
       (:conc (me-conc ctl blk env st cx (1- fuel)))
       (otherwise (me-forever blk env st cx (1- fuel))))))

 (defun me-conc (ctl blk env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (mv-let (k st) (if (kaddr ctl) (me-kind (kaddr ctl) env st cx (1- fuel)) (mv nil st))
       (if (errp k) (mv k st)
         (mv-let (dims st) (me-conc-lims (kadddr ctl) k env st cx (1- fuel))
           (if (errp dims) (mv dims st)
             (let ((tr0 (st-trace st)))
               (mv-let (s st sets) (me-conc-iters (tuples (strip-caddrs-safe dims)) (strip-cars-safe dims) (strip-cadrs-safe dims)
                                                  blk env st cx (1- fuel) nil)
                 (if (errp s) (mv s st)
                   (let ((st (st-trace-set (if tr0 (cons :on (append (ws-of sets) (true-list-fix (cdr tr0)))) nil) st)))
                     (if (conc-bad nil sets) (mv (err :concurrent) st)
                       (mv :normal (undef-all (conc-multi nil sets) st)))))))))))))

 ; the indices' values (11.1.7.4.2: the limits and steps evaluated first),
 ; each (name k values); an index's kind its type-spec's, else that of
 ; the variable of its name outside (R1125)
 (defun me-conc-lims (ixs k env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((atom ixs) (mv nil st))
         (t (let* ((ix (car ixs)) (n (tok-name (kar ix))))
              (mv-let (b suf d) (env-lookup n env)
                (declare (ignore suf d))
                (let ((kk (or k (and (eq (kar b) :var) (eq (scal-ty (st-get (kadr b) st)) :i) (scal-k (st-get (kadr b) st))))))
                  (if (not kk) (mv (err :undeclared) st)
                    (with-v (lo st) (me-ev :expr (kadr ix) env st cx (1- fuel))
                      (with-v (hi st) (me-ev :expr (kaddr ix) env st cx (1- fuel))
                        (with-v (sd st) (if (kadddr ix) (me-ev :expr (kadddr ix) env st cx (1- fuel)) (mv (vi kk 1) st))
                          (let ((lo (conv1 :i kk lo)) (hi (conv1 :i kk hi)) (sd (conv1 :i kk sd)))
                            (cond ((errp lo) (mv lo st)) ((errp hi) (mv hi st)) ((errp sd) (mv sd st))
                                  ((= (v-num sd) 0) (mv (err :step) st))
                                  (t (mv-let (rest st) (me-conc-lims (cdr ixs) k env st cx (1- fuel))
                                       (if (errp rest) (mv rest st)
                                         (mv (cons (list n kk (range-idx (v-num lo) (v-num hi) (v-num sd)
                                                                         (range-count (v-num lo) (v-num hi) (v-num sd))))
                                                   rest)
                                             st))))))))))))))))

 ; the iterations, each with its own indices and its accesses traced
 (defun me-conc-iters (tups names ks blk env st cx fuel sets)   ; (mv status st sets)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st nil))
         ((atom tups) (mv :normal st sets))
         (t (mv-let (fr locs st) (conc-frame names ks (car tups) st)
              (let ((st (st-dovars-set (append locs (true-list-fix (st-dovars st))) (st-trace-set (list :on) st))))
                (mv-let (s st) (me-blk blk (cons fr env) st cx (1- fuel))
                  (cond ((errp s) (mv s st nil))
                        ((member-eq s '(:exit :return)) (mv (err :concurrent) st nil))   ; C1172, C1140
                        (t (mv-let (ws rs) (iter-sets (reverse (drop-locs (true-list-fix (cdr (st-trace st))) locs)) nil nil)
                             (me-conc-iters (cdr tups) names ks blk env
                                            (st-dovars-set (set-difference-equal (true-list-fix (st-dovars st)) locs) st)
                                            cx (1- fuel) (cons (cons ws rs) sets)))))))))))

 ; 11.1.7.4.3: while the count is positive, the block, then the variable
 ; incremented by m3 and the count decremented; EXIT ends the loop, CYCLE
 ; the pass
 (defun me-iter (loc m3 count blk env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (err :fuel) st))
         ((not (and (integerp count) (< 0 count))) (mv :normal st))
         (t (mv-let (s st) (me-blk blk env st cx (1- fuel))
              (cond ((eq s :exit) (mv :normal st))
                    ((member-eq s '(:normal :cycle))
                     (let* ((v (st-get loc st)) (n (mk-int (v-kind v) (+ (ifix (v-num v)) (ifix m3)))))
                       (if (errp n) (mv n st)
                         (me-iter loc m3 (+ -1 count) blk env (st-put loc n st) cx (1- fuel)))))
                    (t (mv s st)))))))

 (defun me-while (e blk env st cx fuel)       ; 11.1.7.4.3: DO WHILE
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (with-v (v st) (me-ev :expr e env st cx (1- fuel))
       (cond ((not (and (lval-p v) (booleanp (v-num v)))) (mv (cond-err v) st))
             ((not (v-num v)) (mv :normal st))
             (t (mv-let (s st) (me-blk blk env st cx (1- fuel))
                  (cond ((eq s :exit) (mv :normal st))
                        ((member-eq s '(:normal :cycle)) (me-while e blk env st cx (1- fuel)))
                        (t (mv s st)))))))))

 (defun me-forever (blk env st cx fuel)        ; DO without loop-control
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (mv-let (s st) (me-blk blk env st cx (1- fuel))
       (cond ((eq s :exit) (mv :normal st))
             ((member-eq s '(:normal :cycle)) (me-forever blk env st cx (1- fuel)))
             (t (mv s st))))))

 (defun me-act (s env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (case (kar s)
       (:assign (me-assign s env st cx (1- fuel)))
       (:simple (let ((k (kadr s)))
                  (cond ((equal k "cycle") (mv :cycle st)) ((equal k "exit") (mv :exit st))
                        ((equal k "return") (mv :return st)) ((equal k "continue") (mv :normal st))
                        (t (mv (err :stop) st)))))
       (:call (mv-let (b suf d) (env-lookup (tok-name (kadr s)) env)
                (declare (ignore d))
                (if (and (eq (kar b) :proc) (eq (kar (unit-hd (kadr b))) :subroutine))
                    (me-call (kadr b) (proc-host (kaddr b) suf cx) (kadddr s) env st cx (1- fuel))
                  (mv (err (if b :type :undeclared)) st))))
       (:print (if (cx-pure cx) (mv (err :pure) st)          ; C1599: no I/O in a pure procedure
               (if (st-trace st) (mv (err :pd) st)     ; output in an order the processor picks (11.1.7.4.2)
                 (with-v (vs st) (me-list (kadr s) env st cx (1- fuel))
                   (mv :normal (st-print (render vs) st))))))
       (:if (with-v (v st) (me-ev :expr (kadr s) env st cx (1- fuel))
              (cond ((not (and (lval-p v) (booleanp (v-num v)))) (mv (cond-err v) st))
                    ((v-num v) (me-act (kaddr s) env st cx (1- fuel)))
                    (t (mv :normal st)))))
       (otherwise (mv (err :syntax) st)))))

 ; R1033: the expression, then the variable (10.2.1.3)
 (defun me-assign (s env st cx fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (err :fuel) st)
     (with-v (v st) (me-ev :expr (kar (kdr (kdr (kdr (kdr s))))) env st cx (1- fuel))
       (mv-let (b suf d) (env-lookup (tok-name (kadr s)) env)
         (declare (ignore suf))
         (let ((loc (kadr b)))
           (cond ((not (eq (kar b) :var)) (mv (err (if b :type :undeclared)) st))
                 ((eq (kaddr b) :in) (mv (err :intent) st))
                 ((member loc (st-dovars st)) (mv (err :do-var) st))
                 ((and (cx-pure cx) (not (equal d 0))) (mv (err :pure) st))   ; C1594: no host or use variable
                 ((not (kaddr s))
                  (let ((n (assign-val (st-get loc st) v)))
                    (if (errp n) (mv n st) (mv :normal (st-put loc n (st-log (list (list :w loc :all)) st))))))
                 (t (let ((a (st-get loc st)))
                      (if (not (aval-p a)) (mv (err :type) st)
                        (mv-let (ds sc st) (me-subs (kadddr s) (a-lbs a) (a-ubs a) env st cx (1- fuel))
                          (if (errp ds) (mv ds st)
                            (let* ((ts (tuples ds))
                                   (sh (section-shape ds sc))
                                   (tgt (fresh (a-ty a) (a-k a) (ones (len sh)) sh))
                                   (c (if (member nil sc) (assign-val tgt v) (conv1 (a-ty a) (a-k a) v))))
                              (if (errp c) (mv c st)
                                (let ((n (arr-sets (st-get loc st) ts (if (aval-p c) (a-es c) (list (raw c))))))
                                  (if (errp n) (mv n st) (mv :normal (st-put loc n (st-log (write-list loc (tuple-offs a ts)) st))))))))))))))))))
)

; ---- a program: the modules elaborated in order, then the main program

(defun ext-frame (units)             ; the external procedures (R503)
  (declare (xargs :guard t))
  (if (atom units) nil
    (if (eq (kar (car units)) :proc)
        (cons (cons (tok-name (hd-name (unit-hd (car units)))) (list :proc (car units) :ext)) (ext-frame (cdr units)))
      (ext-frame (cdr units)))))

(defun me-modules (units mods modenvs gframe st fuel)   ; (mv err mods modenvs st)
  (declare (xargs :guard t :measure (len units) :verify-guards nil))
  (cond ((atom units) (mv nil mods modenvs st))
        ((not (eq (kar (car units)) :module)) (me-modules (cdr units) mods modenvs gframe st fuel))
        (t (let* ((u (car units)) (m (tok-name (hd-name (unit-hd u)))) (spec (unit-spec u))
                  (ufr (use-frames (kar spec) mods)) (env0 (append ufr (list gframe)))
                  (pfr (proc-frame (kadr (unit-int u)) (list :mod m))))
             (mv-let (e fr copies st) (me-decls (kaddr spec) env0 st (list (list mods modenvs gframe) nil) fuel pfr nil m nil)
               (declare (ignore copies))
               (if e (mv e nil nil st)
                 (me-modules (cdr units) (cons (cons m fr) mods) (cons (cons m (cons fr env0)) modenvs) gframe st fuel)))))))

(defun find-main (units)
  (declare (xargs :guard t))
  (if (atom units) nil (if (eq (kar (car units)) :main) (car units) (find-main (cdr units)))))

(defun me-program (units fuel)       ; (mv status lines)
  (declare (xargs :guard t :verify-guards nil))
  (let ((gframe (ext-frame units)) (st (mk-st6 nil 0 nil nil nil nil)) (main (find-main units)))
    (mv-let (e mods modenvs st) (me-modules units nil nil gframe st fuel)
      (cond (e (mv e (reverse (true-list-fix (st-out st)))))
            ((not main) (mv (err :syntax) nil))
            (t (let* ((g (list mods modenvs gframe)) (cx (list g nil)) (spec (unit-spec main))
                      (ufr (use-frames (kar spec) mods)) (env0 (append ufr (list gframe)))
                      (pfr (proc-frame (kadr (unit-int main)) :host)))
                 (mv-let (e fr copies st) (me-decls (kaddr spec) env0 st cx fuel pfr nil (unit-key main) nil)
                   (declare (ignore copies))
                   (if e (mv e (reverse (true-list-fix (st-out st))))
                     (mv-let (s st) (me-blk (unit-exec main) (cons fr env0) st cx fuel)
                       (mv (cond ((equal s (err :stop)) :stop) ((eq s :normal) :normal)
                                 ((errp s) s) (t (err :syntax)))
                           (reverse (true-list-fix (st-out st)))))))))))))

; ---- the text to its answer

(defun parse-stmts (ss)              ; each statement parsed whole, or nil
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ss) (mv t nil)
    (mv-let (ok s r) (fps :stmt (car ss))
      (if (not (and ok (null r))) (mv nil (car ss))
        (mv-let (ok2 rest) (parse-stmts (cdr ss)) (if ok2 (mv t (cons s rest)) (mv nil rest)))))))

(defun fortran-parse (text)          ; (mv ok units-or-the-bad-statement)
  (declare (xargs :guard (stringp text) :verify-guards nil))
  (mv-let (ok ss) (parse-stmts (flex text))
    (if (not ok) (mv nil ss)
      (mv-let (ok2 us r) (fpu :program ss)
        (if (and ok2 (null r)) (mv t us) (mv nil (kar r)))))))

(defun fortran-run (text fuel)       ; (list status lines), or (list (:error :parse) stmt)
  (declare (xargs :guard (stringp text) :verify-guards nil))
  (mv-let (ok us) (fortran-parse text)
    (if (not ok) (list (err :parse) us)
      (mv-let (s lines) (me-program us fuel) (list s lines)))))

; what fortran-parse accepts is a program of the grammar: each statement
; one fps read whole (fps-sound), the units fpu read from them (fpu-sound)
(defthm parse-stmts-sound
  (implies (mv-nth 0 (parse-stmts ss)) (stmts-p (mv-nth 1 (parse-stmts ss))))
  :hints (("Goal" :induct (parse-stmts ss))
          ("Subgoal *1/2" :use ((:instance fps-sound (nt :stmt) (toks (car ss)))) :in-theory (disable fps-sound))))

(defthm fortran-parse-sound
  (implies (mv-nth 0 (fortran-parse text)) (fgu :program (mv-nth 1 (fortran-parse text))))
  :hints (("Goal" :use ((:instance fpu-sound (nt :program) (toks (mv-nth 1 (parse-stmts (flex text))))))
           :in-theory (disable fpu-sound))))

; ---- cost: the runtime's data operations
;
; Evaluation's depth is bounded by fuel (each me-* call passes 1- fuel,
; the mutual recursion's measure). Under it, the operations a run repeats
; are linear: a variable's lookup in the store, an array element's offset
; in array element order (9.5.3.2) and its fetch or update. (A processor
; does these in constant time; the model keeps lists.)

(defun alk-steps (k al)
  (declare (xargs :guard t))
  (cond ((atom al) 1) ((and (consp (car al)) (equal (caar al) k)) 1) (t (+ 1 (alk-steps k (cdr al))))))
(defthm alk-cost (<= (alk-steps k al) (+ 1 (len al))) :rule-classes :linear)

(defun aput-steps (k al)
  (declare (xargs :guard t))
  (cond ((atom al) 1) ((and (consp (car al)) (equal (caar al) k)) 1) (t (+ 1 (aput-steps k (cdr al))))))
(defthm aput-cost (<= (aput-steps k al) (+ 1 (len al))) :rule-classes :linear)

(defun arr-offset-steps (idx lbs ubs)
  (declare (xargs :guard t))
  (cond ((and (atom idx) (atom lbs)) 1)
        ((or (atom idx) (atom lbs) (atom ubs)) 1)
        ((not (and (integerp (car idx)) (integerp (car lbs)) (integerp (car ubs))
                   (<= (car lbs) (car idx)) (<= (car idx) (car ubs)))) 1)
        (t (+ 1 (arr-offset-steps (cdr idx) (cdr lbs) (cdr ubs))))))
(defthm arr-offset-cost (<= (arr-offset-steps idx lbs ubs) (+ 1 (len idx))) :rule-classes :linear)

(defun nth-safe-steps (n xs)
  (declare (xargs :guard t))
  (if (atom xs) 1 (if (not (posp n)) 1 (+ 1 (nth-safe-steps (1- n) (cdr xs))))))
(defthm nth-safe-cost (<= (nth-safe-steps n xs) (+ 1 (len xs))) :rule-classes :linear)

(defun upd-safe-steps (n xs)
  (declare (xargs :guard t))
  (if (atom xs) 1 (if (not (posp n)) 1 (+ 1 (upd-safe-steps (1- n) (cdr xs))))))
(defthm upd-safe-cost (<= (upd-safe-steps n xs) (+ 1 (len xs))) :rule-classes :linear)

; an element's fetch or update: linear in the rank and the element count
(defun arr-get-steps (a idx)
  (declare (xargs :guard t))
  (+ (arr-offset-steps idx (a-lbs a) (a-ubs a)) (nth-safe-steps (arr-offset idx (a-lbs a) (a-ubs a)) (a-es a))))
(defthm arr-get-cost (<= (arr-get-steps a idx) (+ 2 (len idx) (len (a-es a)))) :rule-classes :linear)
(defun arr-set-steps (a idx)
  (declare (xargs :guard t))
  (+ (arr-offset-steps idx (a-lbs a) (a-ubs a)) (upd-safe-steps (arr-offset idx (a-lbs a) (a-ubs a)) (a-es a))))
(defthm arr-set-cost (<= (arr-set-steps a idx) (+ 2 (len idx) (len (a-es a)))) :rule-classes :linear)

; ---- tests: DO CONCURRENT's rules (11.1.7.5), each broken once

(defun lines-text (ls)              ; a program's text, one string per line
  (declare (xargs :guard t))
  (if (atom ls) "" (concatenate 'string (if (stringp (car ls)) (car ls) "") (string #\Newline) (lines-text (cdr ls)))))
(defmacro prog-lines (&rest ls) `(lines-text (list ,@ls)))
(defun run-status (text) (declare (xargs :mode :program)) (car (fortran-run text 1000000)))

; s referred to in every iteration and defined in the others: a reduction
; without REDUCE locality
(assert-event (equal (run-status (prog-lines "program p" "implicit none" "integer :: i, s" "s = 0"
                                             "do concurrent (i = 1:3)" "s = s + i" "end do" "print *, s" "end program p"))
                     '(:error :concurrent)))
; a(i) referred to in iteration i and defined in iteration i - 1
(assert-event (equal (run-status (prog-lines "program p" "implicit none" "integer :: i, a(4)" "a = 1"
                                             "do concurrent (i = 1:3)" "a(i + 1) = a(i)" "end do" "print *, a" "end program p"))
                     '(:error :concurrent)))
; EXIT out of the construct (C1172)
(assert-event (equal (run-status (prog-lines "program p" "implicit none" "integer :: i" 
                                             "do concurrent (i = 1:3)" "exit" "end do" "end program p"))
                     '(:error :concurrent)))
; each element its own iteration's: conforming
(assert-event (equal (fortran-run (prog-lines "program p" "implicit none" "integer :: i, a(3)" "a = 1"
                                              "do concurrent (i = 1:3)" "a(i) = a(i) + i" "end do" "print *, a" "end program p")
                                  1000000)
                     '(:normal (("2" "3" "4")))))
; an operand the value does not need, and its error (10.1.7)
(assert-event (equal (fortran-run (prog-lines "program p" "implicit none" "logical :: l" "integer :: z" "z = 0"
                                              "l = (z > 1) .and. (1 / z > 0)" "print *, l" "end program p")
                                  1000000)
                     '(:normal (("~PD")))))
