; fhelp: what fmean.lisp's evaluation calls outside its mutual
; recursion -- procedures' frames and arguments, literals (R708 .. ), SELECT
; CASE's ranges, labels for GO TO (11.2.2); formatted I/O is fio.lisp's.

(in-package "ACL2")

(include-book "fval")

(set-verify-guards-eagerness 0)

; ---- helpers outside the recursion

(defun str-nat (cs acc)              ; a digit-string's value
  (declare (xargs :guard t))
  (if (atom cs) acc
    (str-nat (cdr cs) (+ (* 10 (nfix acc)) (if (characterp (car cs)) (nfix (- (char-code (car cs)) 48)) 0)))))
(defun digits-val (s) (declare (xargs :guard t)) (if (stringp s) (str-nat (coerce s 'list) 0) 0))

; A character variable defined in part, by a substring (9.4.1), holds
; the code 0 at each undefined character: the subset's programs write no
; such character (no CHAR, ACHAR, nor a literal with one).
(defun nul-in (s) (declare (xargs :guard t)) (and (stringp s) (member (code-char 0) (coerce s 'list)) t))
(defun undef-es (es) (declare (xargs :guard t)) (if (atom es) nil (or (eq (car es) :u) (nul-in (car es)) (undef-es (cdr es)))))
(defun undef-in (v)                  ; a value with an undefined part
  (declare (xargs :guard t))
  (cond ((aval-p v) (undef-es (a-es v))) ((eq (kar v) :u) t) ((cval-p v) (nul-in (kaddr v))) (t nil)))

; ---- substrings (9.4.1): a parent's characters lo .. hi
(defun substr-arg-p (args)           ; name ( [lo] : [hi] ), a character scalar's substring
  (declare (xargs :guard t))
  (and (consp args) (null (cdr args)) (eq (kar (car args)) :tri) (null (kadddr (car args)))))
(defun c-len (v) (declare (xargs :guard t)) (case (kar v) (:c (nfix (kadr v))) (:u (nfix (kaddr v))) (otherwise 0)))
(defun c-str (v)                     ; the characters, an undefined value's each code 0
  (if (cval-p v) (coerce (kaddr v) 'list) (make-list (c-len v) :initial-element (code-char 0))))
(defun substr-of (v lo hi)
  (cond ((not (eq (scal-ty v) :c)) (err :type))
        ((not (and (integerp lo) (integerp hi))) (err :type))
        ((< hi lo) (vc ""))                                      ; zero length
        ((or (< lo 1) (< (c-len v) hi)) (err :bounds))          ; 9.4.1p2
        (t (let ((cs (take (+ 1 (- hi lo)) (nthcdr (- lo 1) (c-str v)))))
             (if (member (code-char 0) cs) (err :undefined) (list :c (len cs) (coerce cs 'string)))))))
(defun substr-put (v lo hi x)        ; v with its characters lo .. hi x's, fit to them (10.2.1.3p10)
  (cond ((not (eq (scal-ty v) :c)) (err :type))
        ((not (cval-p x)) (if (eq (kar x) :u) (err :undefined) (err :type)))
        ((not (and (integerp lo) (integerp hi))) (err :type))
        ((< hi lo) v)
        ((or (< lo 1) (< (c-len v) hi)) (err :bounds))
        (t (let ((cs (c-str v)))
             (list :c (c-len v) (coerce (append (take (- lo 1) cs) (c-chars (c-fit (+ 1 (- hi lo)) x)) (nthcdr hi cs)) 'string))))))

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
                  ; a character dummy shorter than its actual: the actual's leftmost characters
                  (:cprefix (list :c (c-len old) (coerce (append (c-str v) (nthcdr (c-len v) (c-str old))) 'string)))
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
(defun ts-ty (name) (declare (xargs :guard t))
  (cond ((equal name "integer") :i) ((member-equal name '("real" "double")) :r) ((equal name "character") :c) (t :l)))
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
    (cond ((eq (kar tk) :char) (vc (kadr tk)))
          ((not (ikind-p k)) (err :type))
          ((eq (kar tk) :log) (vl k (kadr tk)))
          (t (mk-int k (digits-val (kadr tk))))))))
(in-theory (disable lit-val))

; SELECT CASE (11.1.9): a case-value-range is the interval (lo . hi) of
; raw values, nil for an open end (11.1.9.2); an arm's selector is its
; intervals, or :default. A value lo > hi selects nothing. No value may
; lie in two arms' ranges (C1154): checked on every run.
(defun cv-le (a b)                   ; integers, or characters (10.1.5.5.1)
  (declare (xargs :guard t))
  (cond ((and (rationalp a) (rationalp b)) (<= a b))
        ((and (stringp a) (stringp b)) (<= (cs-cmp (coerce a 'list) (coerce b 'list)) 0))
        (t nil)))
(defun iv-hit (v iv)
  (declare (xargs :guard t))
  (let ((lo (kar iv)) (hi (kdr iv)))
    (if (booleanp v) (equal lo v)
      (and (or (rationalp v) (stringp v)) (or (null lo) (cv-le lo v)) (or (null hi) (cv-le v hi))))))
(defun ivs-hit (v ivs) (declare (xargs :guard t)) (if (atom ivs) nil (or (iv-hit v (car ivs)) (ivs-hit v (cdr ivs)))))
(defun iv-meet (a b)                 ; two intervals share a value
  (declare (xargs :guard t))
  (let ((alo (kar a)) (ahi (kdr a)) (blo (kar b)) (bhi (kdr b)))
    (if (or (booleanp alo) (booleanp blo)) (equal alo blo)
      (and (or (null alo) (null bhi) (cv-le alo bhi))
           (or (null blo) (null ahi) (cv-le blo ahi))
           (or (null alo) (null ahi) (cv-le alo ahi))
           (or (null blo) (null bhi) (cv-le blo bhi))))))
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
        ((and (eq ty :c) (cval-p v)) (v-num v))
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

; ---- labels (R611): GO TO (11.2.2) finds its target in the statement
; list it is in or in one around it, never inside another construct
; (C1169: a branch target is in the scoping unit and no branch goes into
; a construct); a FORMAT statement is found by its label from WRITE
(defun goto-p (s) (declare (xargs :guard t)) (and (consp s) (eq (car s) :goto)))
(defun find-label (l cs)             ; the statements from the one labelled l on
  (declare (xargs :guard t))
  (cond ((atom cs) nil)
        ((equal (car cs) (list :act (list :label l))) cs)
        (t (find-label l (cdr cs)))))
(defun fmt-scan (xs)                 ; label -> format text, from (:act (:label l)) (:act (:format s)) pairs
  (declare (xargs :guard t))
  (if (or (atom xs) (atom (cdr xs))) nil
    (if (and (equal (kar (car xs)) :act) (equal (kar (kadr (car xs))) :label)
             (equal (kar (cadr xs)) :act) (equal (kar (kadr (cadr xs))) :format))
        (cons (cons (kadr (kadr (car xs))) (kadr (kadr (cadr xs)))) (fmt-scan (cdr xs)))
      (fmt-scan (cdr xs)))))
(defun unit-formats (x)              ; every such pair in a unit's tree
  (declare (xargs :guard t))
  (if (atom x) nil (append (fmt-scan x) (unit-formats (car x)) (unit-formats (cdr x)))))

; label DO (R1121): rewritten as a nonlabel DO whose END DO follows the
; statement labelled with its label (11.1.7.2), before the units are read
(defun count-top (l stack) (declare (xargs :guard t)) (if (and (consp stack) (equal (car stack) l)) (+ 1 (count-top l (cdr stack))) 0))
(defun drop-top (l stack) (declare (xargs :guard t)) (if (and (consp stack) (equal (car stack) l)) (drop-top l (cdr stack)) stack))
(defun end-dos (n) (declare (xargs :guard t)) (if (zp n) nil (cons (list :end "do" nil) (end-dos (1- n)))))
(defun ldo-sugar (ss stack term)
  (declare (xargs :guard t))
  (cond ((atom ss) nil)
        (term (append (list (car ss)) (end-dos (count-top term stack)) (ldo-sugar (cdr ss) (drop-top term stack) nil)))
        ((equal (kar (car ss)) :ldo) (cons (list :do (kaddr (car ss))) (ldo-sugar (cdr ss) (cons (kadr (car ss)) stack) nil)))
        ((and (equal (kar (car ss)) :label) (member-equal (kadr (car ss)) stack))
         (cons (car ss) (ldo-sugar (cdr ss) stack (kadr (car ss)))))
        (t (cons (car ss) (ldo-sugar (cdr ss) stack nil)))))

; implicit typing (8.7): in a scoping unit without IMPLICIT NONE a name
; used as a variable and not declared is integer when it begins with I
; to N, real otherwise, default kinds
(defun used-names (x)
  (declare (xargs :guard t))
  (if (atom x) nil
    (append (cond ((and (eq (car x) :name) (consp (cdr x)) (consp (cadr x)) (eq (car (cadr x)) :name)) (list (kadr (cadr x))))
                  ((and (eq (car x) :assign) (consp (cdr x)) (consp (cddr x)) (null (caddr x))) (list (kadr (cadr x))))
                  ((and (eq (car x) :range) (consp (cdr x)) (consp (cddr x))) (list (kadr (caddr x))))
                  (t nil))
            (used-names (car x)) (used-names (cdr x)))))
(defun implicit-ty (n)
  (declare (xargs :guard t))
  (if (and (stringp n) (consp (coerce n 'list)) (member (car (coerce n 'list)) '(#\i #\j #\k #\l #\m #\n))) :i :r))
(defun implicit-vars (ns fr env st)  ; (mv fr st): the undeclared names given variables
  (declare (xargs :guard t))
  (cond ((atom ns) (mv fr st))
        ((or (not (stringp (car ns))) (alk (car ns) fr) (mv-let (b suf d) (env-lookup (car ns) env) (declare (ignore suf d)) b))
         (implicit-vars (cdr ns) fr env st))
        (t (mv-let (loc st) (st-new (list :u (implicit-ty (car ns)) 4) st)
             (implicit-vars (cdr ns) (cons (cons (car ns) (list :var loc :rw)) fr) env st)))))
