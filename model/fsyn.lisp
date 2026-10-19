; fsyn: the abstract syntax of the Fortran subset clotran's ACL2-to-Fortran
; generator (clotran's scripts/acl2-fortran) emits -- exactly that subset,
; inventoried in SUBSET.md, each form citing its rule in J3/24-007
; (Fortran 2023). Recognizers only; fsem.lisp gives the meaning.
;
; Names are strings (R603, C601). The forms, keyword-headed lists:
;
;  type     :int64 | :logical                       R704/R705 (kind int64), R704 LOGICAL
;  expr     (:int n)            n_int64, a literal; negative n is the
;                               generator's -n_int64, a leading add-op
;                               (R1007) on the literal (R708)
;           (:true) (:false)    R725
;           (:var x)            a variable (R901/R903)
;           (:comp o c)         o%c, a structure component (R911/R913)
;           (:elem o c e)       o%c(e), an array element (R917, R919)
;           (:add a b) (:sub a b) (:mul a b) (:neg a)    R1006/R1007
;           (:eq a b) (:lt a b) (:le a b) (:ge a b)      R1013/R1014
;           (:not a)                                     R1015/R1019
;           (:max a b)          max(a, b)        16.9.135
;           (:size o c)         size(o%c, kind=int64)   16.9.194
;           (:huge)             huge(0_int64)    16.9.96
;           (:fcall f args)     a function reference (R1520)
;  stmt     (:assign d e)       d = e (R1033), d a :var, :comp or :elem
;           (:if c then else)   IF (c) THEN / ELSE / END IF (R1136-R1140);
;                               the generator always writes the ELSE
;           (:select e arms default)  SELECT CASE (R1142-R1149); arms
;                               ((k stmts) ...), k distinct (C1154)
;           (:do body)          DO / END DO, no loop-control (R1119-R1134)
;           (:cycle) (:exit) (:return)   R1135, R1158, R1545
;           (:call s args)      CALL s(args) (R1521)
;  dummy    (x :value :int64)   integer(int64), value :: x  (R801, R864)
;           (x :in ty) (x :inout ty)   type(ty), intent(in|inout) :: x (R828)
;           (x :out :int64)     integer(int64), intent(out) :: x
;  local    (x type)            a type declaration (R801)
;  proc     (:function f pure recursive dummies rtype locals body)
;                               [recursive] [pure] function f(..) result(r)
;                               (R1529, R1533, R1535); the result is r
;           (:subroutine s recursive dummies locals body)   R1538
;  module   (:module m procs)   R1404-R1408, its use and implicit none fixed

(in-package "ACL2")

(defconst *int64-max* 9223372036854775807)
(defconst *int64-min* -9223372036854775808)

; ---- names (R603: a letter, then letters, digits, underscores; C601: 63 at most)

(defun alnum-chars-p (cs)
  (declare (xargs :guard t))
  (if (atom cs) (null cs)
    (and (characterp (car cs))
         (or (alpha-char-p (car cs)) (digit-char-p (car cs)) (eql (car cs) #\_))
         (alnum-chars-p (cdr cs)))))

(defun fname-p (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (let ((cs (coerce x 'list)))
         (and (consp cs) (<= (len cs) 63)
              (characterp (car cs)) (alpha-char-p (car cs))
              (alnum-chars-p cs)))))

(defun ftype-p (x) (declare (xargs :guard t)) (or (eq x :int64) (eq x :logical)))

; ---- expressions

(defun int-lit-p (n)
  (declare (xargs :guard t))
  ; -2^63 has no literal: its magnitude is past HUGE; the generator writes
  ; (-huge(0_int64) - 1_int64) for it
  (and (integerp n) (<= (- *int64-max*) n) (<= n *int64-max*)))

; a literal written with a sign: -n_int64. An add-operand or mult-operand
; cannot begin with a sign (R1006, R1007), so it is no right operand of
; +, - or *, and no operand of a unary minus: (x + -1_int64) is not
; Fortran (gfortran -std=f2018 refuses it; flang takes it). The
; generator writes (-1_int64 + x), never the other order (SUBSET.md).
(defun neg-lit-p (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :int) (consp (cdr x)) (integerp (cadr x)) (< (cadr x) 0)))

(mutual-recursion
 (defun fexpr-p (x)
   (declare (xargs :guard t :measure (acl2-count x)))
   (and (consp x) (true-listp x)
        (case (car x)
          (:int (and (= (len x) 2) (int-lit-p (cadr x))))
          ((:true :false :huge) (= (len x) 1))
          (:var (and (= (len x) 2) (fname-p (cadr x))))
          ((:comp :size) (and (= (len x) 3) (fname-p (cadr x)) (fname-p (caddr x))))
          (:elem (and (= (len x) 4) (fname-p (cadr x)) (fname-p (caddr x)) (fexpr-p (cadddr x))))
          (:neg (and (= (len x) 2) (fexpr-p (cadr x)) (not (neg-lit-p (cadr x)))))
          (:not (and (= (len x) 2) (fexpr-p (cadr x))))
          ((:add :sub :mul)
           (and (= (len x) 3) (fexpr-p (cadr x)) (fexpr-p (caddr x)) (not (neg-lit-p (caddr x)))))
          ((:eq :lt :le :ge :max)
           (and (= (len x) 3) (fexpr-p (cadr x)) (fexpr-p (caddr x))))
          (:fcall (and (= (len x) 3) (fname-p (cadr x)) (fexpr-list-p (caddr x))))
          (otherwise nil))))
 (defun fexpr-list-p (xs)
   (declare (xargs :guard t :measure (acl2-count xs)))
   (if (atom xs) (null xs)
     (and (fexpr-p (car xs)) (fexpr-list-p (cdr xs))))))

(defun fdesig-p (x)
  (declare (xargs :guard t))
  (and (fexpr-p x) (member-eq (car x) '(:var :comp :elem)) t))

; ---- statements

(defun case-keys (arms)
  (declare (xargs :guard t))
  (if (atom arms) nil
    (cons (if (consp (car arms)) (caar arms) nil) (case-keys (cdr arms)))))

(mutual-recursion
 (defun fstmt-p (x)
   (declare (xargs :guard t :measure (acl2-count x)))
   (and (consp x) (true-listp x)
        (case (car x)
          (:assign (and (= (len x) 3) (fdesig-p (cadr x)) (fexpr-p (caddr x))))
          (:if (and (= (len x) 4) (fexpr-p (cadr x)) (fstmt-list-p (caddr x)) (fstmt-list-p (cadddr x))))
          (:select (and (= (len x) 4) (fexpr-p (cadr x))
                        (farms-p (caddr x)) (no-duplicatesp-equal (case-keys (caddr x)))
                        (fstmt-list-p (cadddr x))))
          (:do (and (= (len x) 2) (fstmt-list-p (cadr x))))
          ((:cycle :exit :return) (= (len x) 1))
          (:call (and (= (len x) 3) (fname-p (cadr x)) (fexpr-list-p (caddr x))))
          (otherwise nil))))
 (defun farms-p (arms)
   (declare (xargs :guard t :measure (acl2-count arms)))
   (if (atom arms) (null arms)
     (and (consp (car arms)) (true-listp (car arms)) (= (len (car arms)) 2)
          (int-lit-p (caar arms)) (fstmt-list-p (cadar arms))
          (farms-p (cdr arms)))))
 (defun fstmt-list-p (xs)
   (declare (xargs :guard t :measure (acl2-count xs)))
   (if (atom xs) (null xs)
     (and (fstmt-p (car xs)) (fstmt-list-p (cdr xs))))))

; ---- procedures and the module

(defun fdummy-p (d)
  (declare (xargs :guard t))
  (and (true-listp d) (= (len d) 3) (fname-p (car d))
       (case (cadr d)
         ((:value :out) (eq (caddr d) :int64))
         ((:in :inout) (fname-p (caddr d)))
         (otherwise nil))))

(defun fdummies-p (ds)
  (declare (xargs :guard t))
  (if (atom ds) (null ds) (and (fdummy-p (car ds)) (fdummies-p (cdr ds)))))

(defun flocals-p (ls)
  (declare (xargs :guard t))
  (if (atom ls) (null ls)
    (and (true-listp (car ls)) (= (len (car ls)) 2) (fname-p (caar ls)) (ftype-p (cadar ls))
         (flocals-p (cdr ls)))))

(defun strip-names (xs)
  (declare (xargs :guard t))
  (if (atom xs) nil (cons (if (consp (car xs)) (caar xs) nil) (strip-names (cdr xs)))))

(defun fproc-p (p)
  (declare (xargs :guard t))
  (and (true-listp p)
       (case (car p)
         (:function (and (= (len p) 8) (fname-p (nth 1 p)) (booleanp (nth 2 p)) (booleanp (nth 3 p))
                         (fdummies-p (nth 4 p)) (ftype-p (nth 5 p)) (flocals-p (nth 6 p))
                         (fstmt-list-p (nth 7 p))
                         ; the dummies, the locals and the result r are distinct names
                         (no-duplicatesp-equal (cons "r" (append (strip-names (nth 4 p)) (strip-names (nth 6 p)))))))
         (:subroutine (and (= (len p) 6) (fname-p (nth 1 p)) (booleanp (nth 2 p))
                           (fdummies-p (nth 3 p)) (flocals-p (nth 4 p)) (fstmt-list-p (nth 5 p))
                           (no-duplicatesp-equal (append (strip-names (nth 3 p)) (strip-names (nth 4 p))))))
         (otherwise nil))))

(defun fprocs-p (ps)
  (declare (xargs :guard t))
  (if (atom ps) (null ps) (and (fproc-p (car ps)) (fprocs-p (cdr ps)))))

(defun proc-names (ps)
  (declare (xargs :guard t))
  (if (atom ps) nil (cons (if (true-listp (car ps)) (nth 1 (car ps)) nil) (proc-names (cdr ps)))))

(defun fmodule-p (m)
  (declare (xargs :guard t))
  (and (true-listp m) (= (len m) 3) (eq (car m) :module) (fname-p (cadr m))
       (fprocs-p (caddr m)) (no-duplicatesp-equal (proc-names (caddr m)))))

; ---- tests: the generator's own lines, in this syntax

; r = (.not. (1099511627776_int64 < x_))
(assert-event (fstmt-p '(:assign (:var "r") (:not (:lt (:int 1099511627776) (:var "x_"))))))
; st%ca(i_4) = v_5
(assert-event (fstmt-p '(:assign (:elem "st" "ca" (:var "i_4")) (:var "v_5"))))
; t_5 = (var_4 < size(st%stk, kind=int64))
(assert-event (fstmt-p '(:assign (:var "t_5") (:lt (:var "var_4") (:size "st" "stk")))))
; if ((.not. (x_ < (-huge(0_int64) - 1_int64)))) then ...
(assert-event (fexpr-p '(:not (:lt (:var "x_") (:sub (:neg (:huge)) (:int 1))))))
; select case (n_) / case (1_int64) ... / case default ... / end select
(assert-event (fstmt-p '(:select (:var "n_") ((1 ((:assign (:var "r") (:int 0)))) (2 ((:return))))
                                 ((:assign (:var "r") (:max (:int 0) (:var "ci_")))))))
; duplicate case values are refused (C1154)
(assert-event (not (fstmt-p '(:select (:var "n_") ((1 nil) (1 nil)) nil))))
; a signed literal leads a sum, never follows an operator (R1007)
(assert-event (and (fexpr-p '(:add (:int -1) (:var "k_"))) (not (fexpr-p '(:add (:var "k_") (:int -1))))
                   (fexpr-p '(:lt (:var "x_") (:int -1))) (not (fexpr-p '(:neg (:int -1))))))
; -2^63 has no literal
(assert-event (not (fexpr-p '(:int -9223372036854775808))))
; a name: a letter first (R603), 63 characters at most (C601)
(assert-event (and (fname-p "vmg_step") (not (fname-p "_x")) (not (fname-p "1x"))))
(assert-event (fproc-p '(:function "bnd40p" t nil (("x_" :value :int64)) :logical nil
                         ((:if (:not (:lt (:var "x_") (:int 0)))
                               ((:assign (:var "r") (:not (:lt (:int 1099511627776) (:var "x_")))) (:return))
                               ((:assign (:var "r") (:false)) (:return)))))))
