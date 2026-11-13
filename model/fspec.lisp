; Lemmis: the specific names of intrinsic functions (16.8, Tables 16.2, 16.3),
; FORTRAN 77's, and DPROD (16.9.71).
;
; A specific name is the generic intrinsic of its row on arguments of the
; one type and kind the row gives (default integer :i 4, default real :r 4,
; double precision :r 8, default complex :z 4); a reference with others
; does not conform (16.8), an error :type here. AMAX0 and AMIN0 are REAL of
; the generic's result, MAX1 and MIN1 INT of it. A name that is both specific
; and generic (ABS, MOD, SQRT, INT, REAL, ...) referenced as a function is
; the generic, fval's intrinsic. Not in the subset: a specific name as an
; actual argument (15.5.2.9), INDEX, LEN as specifics, CHAR, ICHAR, LGE..LLT.

(in-package "ACL2")
(include-book "fval")
(set-verify-guards-eagerness 0)

(defconst *specifics*   ; name generic argument-type argument-kind [conversion]
  '(("iabs" "abs" :i 4) ("dabs" "abs" :r 8) ("cabs" "abs" :z 4)
    ("alog" "log" :r 4) ("dlog" "log" :r 8) ("clog" "log" :z 4)
    ("alog10" "log10" :r 4) ("dlog10" "log10" :r 8)
    ("dexp" "exp" :r 8) ("cexp" "exp" :z 4) ("dsqrt" "sqrt" :r 8) ("csqrt" "sqrt" :z 4)
    ("dsin" "sin" :r 8) ("csin" "sin" :z 4) ("dcos" "cos" :r 8) ("ccos" "cos" :z 4) ("dtan" "tan" :r 8)
    ("dasin" "asin" :r 8) ("dacos" "acos" :r 8) ("datan" "atan" :r 8) ("datan2" "atan2" :r 8)
    ("dsinh" "sinh" :r 8) ("dcosh" "cosh" :r 8) ("dtanh" "tanh" :r 8)
    ("dint" "aint" :r 8) ("dnint" "anint" :r 8) ("idnint" "nint" :r 8)
    ("amod" "mod" :r 4) ("dmod" "mod" :r 8) ("isign" "sign" :i 4) ("dsign" "sign" :r 8)
    ("idim" "dim" :i 4) ("ddim" "dim" :r 8)
    ("max0" "max" :i 4) ("amax1" "max" :r 4) ("dmax1" "max" :r 8)
    ("amax0" "max" :i 4 "real") ("max1" "max" :r 4 "int")
    ("min0" "min" :i 4) ("amin1" "min" :r 4) ("dmin1" "min" :r 8)
    ("amin0" "min" :i 4 "real") ("min1" "min" :r 4 "int")
    ("float" "real" :i 4) ("ifix" "int" :r 4) ("idint" "int" :r 8) ("sngl" "real" :r 8)))

(defun spec-args-ok (ty k vs)        ; every argument of type ty, kind k
  (declare (xargs :guard t))
  (or (atom vs)
      (and (let ((v (car vs)))
             (if (aval-p v) (and (eq (a-ty v) ty) (equal (a-k v) k))
               (and (eq (scal-ty v) ty) (equal (scal-k v) k))))
           (spec-args-ok ty k (cdr vs)))))

(defun intrinsic-spec (name vs kw)
  (declare (xargs :guard t))
  (let ((s (cdr (assoc-equal name *specifics*))) (x (kar vs)) (y (kadr vs)))
    (cond ((equal name "dprod")      ; 16.9.71: X * Y of default reals, as double precision
           (cond ((not (and (= (len vs) 2) (null kw) (spec-args-ok :r 4 vs) (not (aval-p x)) (not (aval-p y)))) (err :type))
                 ((or (eq (kar x) :u) (eq (kar y) :u)) (err :undefined))
                 ((or (pd-p x) (pd-p y)) (list :pd :r 8))
                 (t (vr 8 (fl-mul 8 (v-num x) (v-num y))))))   ; exact: 24 + 24 bits fit in 53
          ((not (consp s)) (intrinsic name vs kw))
          ((not (and (null kw) (spec-args-ok (cadr s) (caddr s) vs))) (err :type))
          (t (let ((r (intrinsic (car s) vs nil)))
               (if (and (cadddr s) (not (errp r))) (intrinsic (cadddr s) (list r) nil) r))))))
(in-theory (disable intrinsic-spec))
