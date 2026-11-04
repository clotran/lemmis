; fstmt: the subset's statements (Stage A, item 1, continued): grammar
; (fgs, fys) and parser (fps) over one statement's tokens, the
; expressions read by fparse.lisp's fp. As there: fps-sound and
; fps-complete prove that fps accepts exactly the statements fgs allows,
; and answers the one tree that spells them (fstmt-sound.lisp,
; fstmt-complete.lisp).
; fps-cost bounds its work: a successful parse makes at most 64 calls
; (fp's among them) per token it consumes, plus fps-d nt (fstmt-cost.lisp).
;
; A statement's kind is known from its first token (the subset's names
; are never *fkeywords*), or after its type-spec: "integer function f"
; begins a function, "integer :: n" a declaration.
;
;  :stmt  (:program n)              R1402 program-stmt: PROGRAM program-name
;         (:module n)               R1405 module-stmt: MODULE module-name
;         (:end k n)                END [k [n]]: R1403 end-program-stmt,
;                                   R1406 end-module-stmt, R1536
;                                   end-function-stmt, R1540
;                                   end-subroutine-stmt (k one of those,
;                                   n its name or nil); R1134 end-do-stmt,
;                                   R1140 end-if-stmt (k do or if, no
;                                   construct name in the subset)
;         (:contains)               R1546 contains-stmt
;         (:use nat n onlyp ns)     R1409 use-stmt: USE [[, module-nature]
;                                   ::] module-name [, ONLY : [only-list]];
;                                   R1410 module-nature (nat nil, :dc for a
;                                   bare ::, or "intrinsic" "non_intrinsic");
;                                   R1412/R1413 only: only-use-name (names)
;         (:implicit-none)          R866 implicit-stmt: IMPLICIT NONE
;         (:decl ts attrs dc ents)  R801 type-declaration-stmt:
;                                   declaration-type-spec [[, attr-spec]...
;                                   ::] entity-decl-list; dc whether "::"
;                                   is written: required with an attr-spec
;                                   (R801) or an initialization (C806)
;         (:assign n refp args e)   R1033 assignment-stmt: variable = expr;
;                                   R902 variable, R901 designator: a name
;                                   or a part-ref with its subscripts (R912)
;         (:if-then e)              R1137 if-then-stmt: IF ( expr ) THEN
;         (:else-if e)              R1138 else-if-stmt: ELSE IF ( expr ) THEN
;         (:else)                   R1139 else-stmt: ELSE
;         (:if e s)                 R1141 if-stmt: IF ( expr ) action-stmt,
;                                   s an action-stmt (R515) other than an
;                                   if-stmt (C1143)
;         (:do ctl)                 R1122 nonlabel-do-stmt: DO [loop-control]
;         (:simple k)               R1135 cycle-stmt, R1158 exit-stmt, R1545
;                                   return-stmt, R1161 continue-stmt, R1162
;                                   stop-stmt (no construct name, return
;                                   value or stop-code in the subset)
;         (:call n parens args)     R1521 call-stmt: CALL procedure-designator
;                                   [( [actual-arg-spec-list] )], R1522
;         (:print f items)          R1212 print-stmt: PRINT format [,
;                                   output-item-list]; R1215 format: *
;                                   (f :star), a label (f its digits) or a
;                                   char-literal-constant (f its token: a
;                                   default-char-expr, a literal in the
;                                   subset); R1217 output-item: expr
;         (:function pre n ds res)  R1533 function-stmt: [prefix] FUNCTION
;                                   function-name ( [dummy-arg-name-list] )
;                                   [suffix]; R1534; R1535 suffix: RESULT (
;                                   result-name ) (res nil when absent)
;         (:subroutine pre n p ds)  R1538 subroutine-stmt: [prefix]
;                                   SUBROUTINE subroutine-name [( [dummy-arg-list] )],
;                                   R1539 dummy-arg: dummy-arg-name
;         (:select e)               R1143 select-case-stmt: SELECT CASE ( case-expr ),
;                                   R1146 case-expr: scalar-expr
;         (:case rs)                R1144 case-stmt: CASE case-selector, R1147
;                                   case-selector: ( case-value-range-list )
;         (:case-default)           CASE DEFAULT
;                                   (END SELECT, R1145 end-select-stmt, is (:end "select" nil))
;  :ranges (r ...) nonempty, ")" included: the case-value-range-list
;  :range (:val e) (:from e) (:to e) (:rng a b)   R1148 case-value-range:
;                                   case-value | case-value : | : case-value
;                                   | case-value : case-value; R1149 case-value
;         (:label l)                R611 label, written before a statement
;                                   (6.2.5): its own statement here, the
;                                   token (:lab l) the lexers make
;         (:goto l)                 R1157 goto-stmt: GO TO label
;         (:aif e l1 l2 l3)         arithmetic IF, a deleted feature (B.1;
;                                   Fortran 2008 R853): IF ( expr ) l1, l2, l3
;         (:ldo l ctl)              R1121 label-do-stmt: DO label [loop-control]
;         (:format s)               R1301 format-stmt: FORMAT format-specification,
;                                   the token (:fmt s) its text from "(" to ")"
;         (:write ios items)        R1211 write-stmt: WRITE ( io-control-spec-list )
;                                   [output-item-list]
;         (:read ios items)         R1210 read-stmt: READ ( io-control-spec-list )
;                                   [input-item-list], R1216 input-item:
;                                   variable, a designator (lone-prim)
;         (:readf f items)          R1210 READ format [, input-item-list]
;  :ios  (io ...) ")" included      R1213 io-control-spec-list: io-unit first
;                                   when UNIT= is omitted (C1211), format
;                                   second when FMT= is (C1218), each at
;                                   most once (C1210), an ADVANCE= only with
;                                   a format other than * (C1223); exactly
;                                   one format in the subset (formatted I/O)
;  :kios (io ...) ")" included      the specs written with their keyword, each ", io"
;  :io   (:unit kwp u)              [UNIT =] io-unit: R1201 io-unit * (u
;                                   :star) or R1202 file-unit-number, an expr
;        (:fmt kwp f)               [FMT =] format (as PRINT's f); kwp nil
;                                   only as the list's second item
;        (:adv tk)                  ADVANCE = scalar-default-char-expr, a
;                                   char-literal-constant in the subset
;  :oitems (e ...)                  R1216 output-item-list, e {, e}, to the end
;  :ts    (k ks)                    R703/R704 declaration-type-spec,
;                                   intrinsic-type-spec: R705 INTEGER
;                                   [kind-selector] or LOGICAL
;                                   [kind-selector]; R706 kind-selector:
;                                   ( [KIND =] scalar-int-constant-expr ),
;                                   ks nil or (kwp e)
;  :attrs (attr ...)                each written ", attr-spec" (R802):
;                                   (:parameter) PARAMETER, (:value) VALUE,
;                                   (:intent i) INTENT ( intent-spec ) R828
;                                   (i "in" "out" "inout" or "in out",
;                                   Table 6.2), (:dimension shapes)
;                                   DIMENSION ( array-spec )
;  :shapes (s ...) nonempty, ")" included: R814 array-spec, an
;                                   explicit-shape-spec-list or an
;                                   assumed-shape-spec-list, not mixed
;  :shape (:ex lo hi)               R815 explicit-shape-spec: [lower-bound :]
;                                   upper-bound (R816, R817)
;         (:as lo)                  R820 assumed-shape-spec: [lower-bound] :
;  :ents  (ent ...) nonempty        entity-decl-list
;  :ent   (n shapes init)           R803 entity-decl: object-name (R804)
;                                   [( array-spec )] [initialization]; R805
;                                   initialization: = constant-expr
;  :names (n ...), ")" included     ( [dummy-arg-name-list] )
;  :onames (n ...)                  only-list, to the statement's end
;  :items (e ...)                   each written ", expr"
;  :ctl   nil                       DO alone
;         (:range c v e1 e2 e3)     R1123 loop-control: [,] do-variable =
;                                   expr , expr [, expr]; R1124 (c whether
;                                   the "," is written, e3 nil when absent)
;         (:while c e)              R1123 [,] WHILE ( expr )
;         (:conc c ts ixs)          R1123 [,] CONCURRENT concurrent-header;
;                                   R1125 concurrent-header: ( [integer-type-spec
;                                   ::] concurrent-control-list ) -- no
;                                   scalar-mask-expr and no concurrent-locality
;                                   (R1129) in the subset; ts nil or a :ts
;  :ixs  (ix ...) nonempty, ")" included: the concurrent-control-list
;  :ix   (n lo hi st)              R1126 concurrent-control: index-name =
;                                   concurrent-limit : concurrent-limit [:
;                                   concurrent-step] (R1127, R1128; st nil)
;  :prefix (spec ...)               R1529 prefix, R1530 prefix-spec:
;                                   (:ts ts) a declaration-type-spec, or
;                                   (:kw k) ELEMENTAL IMPURE NON_RECURSIVE
;                                   PURE RECURSIVE

(in-package "ACL2")

(include-book "fstmt-base")

(defun kw-list (ss)
  (declare (xargs :guard t))
  (if (atom ss) nil (cons (kw (car ss)) (kw-list (cdr ss)))))

; a statement's parts, as nonterminals of their own:
;  :decl-rest (attrs dc ents)    after a declaration's type-spec
;  :fn-rest   (n ds res)         FUNCTION n ( names ) [RESULT ( r )]
;  :sub-rest  (n p ds)           SUBROUTINE n [( names )]
;  :attr      one attr-spec, its "," before it written by :attrs
;  :init      nil or e           [= expr]
(defun fgs-measure (nt x)
  (declare (xargs :guard t))
  (+ (* 2 (acl2-count x)) (if (eq nt :shapes) 1 0)))

(defun fgs (nt x)
  (declare (xargs :guard t :measure (fgs-measure nt x)))
  (case nt
    (:stmt
     (and (true-listp x)
          (case (car x)
            ((:program :module) (and (= (len x) 2) (name-tok-p (cadr x))))
            (:end (and (= (len x) 3)
                       (if (cadr x)
                           (and (member-equal (cadr x) *end-kinds*)
                                (or (null (caddr x))
                                    (and (member-equal (cadr x) *unit-ends*) (name-tok-p (caddr x)))))
                         (null (caddr x)))))
            ((:contains :implicit-none :else) (= (len x) 1))
            (:use (and (= (len x) 5)
                       (member-equal (cadr x) '(nil :dc "intrinsic" "non_intrinsic"))
                       (name-tok-p (caddr x)) (booleanp (cadddr x))
                       (names-p (car (cddddr x)))
                       (or (cadddr x) (null (car (cddddr x))))))
            (:decl (and (= (len x) 5) (fgs :ts (cadr x)) (fgs :decl-rest (cddr x))))
            (:assign (and (= (len x) 5) (name-tok-p (cadr x)) (booleanp (caddr x))
                          (if (caddr x) (and (fg :args (cadddr x)) (no-kw-args (cadddr x))) (null (cadddr x)))
                          (fg :expr (car (cddddr x)))))
            ((:if-then :else-if) (and (= (len x) 2) (fg :expr (cadr x))))
            (:if (and (= (len x) 3) (fg :expr (cadr x)) (consp (caddr x))
                      (action-kind-p (car (caddr x))) (fgs :stmt (caddr x))))
            (:do (and (= (len x) 2) (fgs :ctl (cadr x))))
            (:simple (and (= (len x) 2) (member-equal (cadr x) *simple-kinds*) t))
            (:call (and (= (len x) 4) (name-tok-p (cadr x)) (booleanp (caddr x))
                        (if (caddr x) (fg :args (cadddr x)) (null (cadddr x)))))
            (:print (and (= (len x) 3) (fmt-spec-p (cadr x)) (fgs :items (caddr x))))
            (:readf (and (= (len x) 3) (fmt-spec-p (cadr x)) (fgs :items (caddr x)) (all-lone (caddr x))))
            (:select (and (= (len x) 2) (fg :expr (cadr x))))
            (:case (and (= (len x) 2) (fgs :ranges (cadr x))))
            (:case-default (= (len x) 1))
            ((:label :goto) (and (= (len x) 2) (label-digits-p (cadr x))))
            (:aif (and (= (len x) 5) (fg :expr (cadr x)) (label-digits-p (caddr x)) (label-digits-p (cadddr x))
                       (label-digits-p (car (cddddr x)))))
            (:ldo (and (= (len x) 3) (label-digits-p (cadr x)) (fgs :ctl (caddr x))))
            (:format (and (= (len x) 2) (stringp (cadr x))))
            (:write (and (= (len x) 3) (fgs :ios (cadr x)) (fgs :oitems (caddr x))))
            (:read (and (= (len x) 3) (fgs :ios (cadr x)) (fgs :oitems (caddr x)) (all-lone (caddr x))))
            (:function (and (= (len x) 5) (fgs :prefix (cadr x)) (fgs :fn-rest (cddr x))))
            (:subroutine (and (= (len x) 5) (fgs :prefix (cadr x)) (not (assoc-eq :ts (cadr x)))
                              (fgs :sub-rest (cddr x))))
            (otherwise nil))))
    (:decl-rest (and (true-listp x) (= (len x) 3) (fgs :attrs (car x)) (booleanp (cadr x))
                     (consp (caddr x)) (fgs :ents (caddr x))
                     (implies (or (consp (car x)) (ents-init-p (caddr x))) (cadr x))))
    (:fn-rest (and (true-listp x) (= (len x) 3) (name-tok-p (car x)) (names-p (cadr x))
                   (or (null (caddr x)) (name-tok-p (caddr x)))))
    (:sub-rest (and (true-listp x) (= (len x) 3) (name-tok-p (car x)) (booleanp (cadr x))
                    (names-p (caddr x)) (or (cadr x) (null (caddr x)))))
    (:ts (and (true-listp x) (= (len x) 2) (member-equal (car x) *type-kws*)
              (or (null (cadr x))
                  (and (true-listp (cadr x)) (= (len (cadr x)) 2) (booleanp (car (cadr x)))
                       (fg :expr (cadr (cadr x)))))))
    (:attrs (if (atom x) (null x) (and (fgs :attr (car x)) (fgs :attrs (cdr x)))))
    (:attr (and (true-listp x)
                (case (car x)
                  ((:parameter :value) (= (len x) 1))
                  (:intent (and (= (len x) 2) (member-equal (cadr x) *intents*) t))
                  (:dimension (and (= (len x) 2) (fgs :shapes (cadr x))))
                  (otherwise nil))))
    (:shapes (and (consp x) (shapes-same x (shape-kind (car x))) (fgs :shapes* x)))
    (:shapes* (and (consp x) (fgs :shape (car x)) (or (null (cdr x)) (fgs :shapes* (cdr x)))))
    (:shape (and (true-listp x)
                 (case (car x)
                   (:ex (and (= (len x) 3) (or (null (cadr x)) (fg :expr (cadr x))) (fg :expr (caddr x))))
                   (:as (and (= (len x) 2) (or (null (cadr x)) (fg :expr (cadr x)))))
                   (otherwise nil))))
    (:ranges (and (consp x) (fgs :range (car x)) (or (null (cdr x)) (fgs :ranges (cdr x)))))
    (:ixs (and (consp x) (fgs :ix (car x)) (or (null (cdr x)) (fgs :ixs (cdr x)))))
    (:ix (and (true-listp x) (= (len x) 4) (name-tok-p (car x)) (fg :expr (cadr x)) (fg :expr (caddr x))
              (or (null (cadddr x)) (fg :expr (cadddr x)))))
    (:range (and (true-listp x)
                 (case (car x)
                   ((:val :from :to) (and (= (len x) 2) (fg :expr (cadr x))))
                   (:rng (and (= (len x) 3) (fg :expr (cadr x)) (fg :expr (caddr x))))
                   (otherwise nil))))
    (:ents (and (consp x) (fgs :ent (car x)) (or (null (cdr x)) (fgs :ents (cdr x)))))
    (:ent (and (true-listp x) (= (len x) 3) (name-tok-p (car x))
               (or (null (cadr x)) (fgs :shapes (cadr x)))
               (fgs :init (caddr x))))
    (:init (or (null x) (fg :expr x)))
    (:items (if (atom x) (null x) (and (fg :expr (car x)) (fgs :items (cdr x)))))
    (:oitems (if (atom x) (null x) (and (fg :expr (car x)) (fgs :oitems (cdr x)))))
    (:ios (and (consp x) (fgs :io (car x)) (ios-ok x)
               (if (and (unit-pos-p (car x)) (consp (cdr x)) (fmt-pos-p (cadr x))) (fgs :kios (cddr x)) (fgs :kios (cdr x)))))
    (:kios (if (atom x) (null x) (and (fgs :io (car x)) (not (unit-pos-p (car x))) (fgs :kios (cdr x)))))
    (:io (and (true-listp x)
              (case (car x)
                (:unit (and (= (len x) 3) (booleanp (cadr x)) (or (eq (caddr x) :star) (fg :expr (caddr x)))))
                (:fmt (and (= (len x) 3) (eq (cadr x) t) (fmt-spec-p (caddr x))))
                (:adv (and (= (len x) 2) (char-tok-p (cadr x))))
                (otherwise nil))))
    (:ctl (or (null x)
              (and (true-listp x)
                   (case (car x)
                     (:range (and (= (len x) 6) (booleanp (cadr x)) (name-tok-p (caddr x))
                                  (fg :expr (cadddr x)) (fg :expr (car (cddddr x)))
                                  (or (null (cadr (cddddr x))) (fg :expr (cadr (cddddr x))))))
                     (:while (and (= (len x) 3) (booleanp (cadr x)) (fg :expr (caddr x))))
                     (:conc (and (= (len x) 4) (booleanp (cadr x))
                                 (or (null (caddr x)) (and (fgs :ts (caddr x)) (equal (car (caddr x)) "integer")))
                                 (fgs :ixs (cadddr x))))
                     (otherwise nil)))))
    ((:names :onames) (names-p x))
    (:names1 (and (consp x) (names-p x)))
    (:prefix (if (atom x) (null x)
               (and (true-listp (car x)) (= (len (car x)) 2)
                    (case (caar x)
                      (:ts (fgs :ts (cadar x)))
                      (:kw (and (member-equal (cadar x) *prefix-kws*) t))
                      (otherwise nil))
                    (fgs :prefix (cdr x)))))
    (otherwise nil)))

(defun names-y (ns)                ; n {, n} )
  (declare (xargs :guard t))
  (if (atom ns) (list (op ")"))
    (cons (car ns) (if (consp (cdr ns)) (cons (op ",") (names-y (cdr ns))) (list (op ")"))))))
(defun onames-y (ns)               ; n {, n}
  (declare (xargs :guard t))
  (if (atom ns) nil
    (cons (car ns) (if (consp (cdr ns)) (cons (op ",") (onames-y (cdr ns))) nil))))

(defun dcolon () (declare (xargs :guard t)) (list (op ":") (op ":")))   ; "::", two ":" tokens (flex)

(defun fys (nt x)
  (declare (xargs :guard t :measure (fgs-measure nt x)))
  (if (atom x)
      (case nt ((:shapes :shapes* :names :names1 :ranges :ixs :kios) (list (op ")"))) (otherwise nil))
    (case nt
      (:stmt
       (case (car x)
         (:program (list (kw "program") (kadr x)))
         (:module (list (kw "module") (kadr x)))
         (:end (cons (kw "end") (if (kadr x) (cons (kw (kadr x)) (if (kaddr x) (list (kaddr x)) nil)) nil)))
         (:contains (list (kw "contains")))
         (:implicit-none (list (kw "implicit") (kw "none")))
         (:else (list (kw "else")))
         (:use (append (list (kw "use"))
                       (cond ((null (kadr x)) nil) ((eq (kadr x) :dc) (dcolon))
                             (t (list* (op ",") (kw (kadr x)) (dcolon))))
                       (list (kaddr x))
                       (if (kadddr x) (list* (op ",") (kw "only") (op ":") (onames-y (kar (kdr (kdr (kdr (kdr x))))))) nil)))
         (:decl (append (fys :ts (kadr x)) (fys :decl-rest (kdr (kdr x)))))
         (:assign (append (list (kadr x)) (if (kaddr x) (cons (op "(") (fy :args (kadddr x))) nil)
                          (cons (op "=") (fy :expr (kar (kdr (kdr (kdr (kdr x)))))))))
         (:if-then (list* (kw "if") (op "(") (append (fy :expr (kadr x)) (list (op ")") (kw "then")))))
         (:else-if (list* (kw "else") (kw "if") (op "(") (append (fy :expr (kadr x)) (list (op ")") (kw "then")))))
         (:if (list* (kw "if") (op "(") (append (fy :expr (kadr x)) (cons (op ")") (fys :stmt (kaddr x))))))
         (:do (cons (kw "do") (fys :ctl (kadr x))))
         (:simple (list (kw (kadr x))))
         (:call (list* (kw "call") (kadr x) (if (kaddr x) (cons (op "(") (fy :args (kadddr x))) nil)))
         (:print (list* (kw "print") (fmt-tok (kadr x)) (fys :items (kaddr x))))
         (:readf (list* (kw "read") (fmt-tok (kadr x)) (fys :items (kaddr x))))
         (:select (list* (kw "select") (kw "case") (op "(") (append (fy :expr (kadr x)) (list (op ")")))))
         (:case (list* (kw "case") (op "(") (fys :ranges (kadr x))))
         (:case-default (list (kw "case") (kw "default")))
         (:label (list (list :lab (kadr x))))
         (:goto (list (kw "go") (kw "to") (lab-int (kadr x))))
         (:aif (list* (kw "if") (op "(") (append (fy :expr (kadr x))
                                                (list (op ")") (lab-int (kaddr x)) (op ",") (lab-int (kadddr x)) (op ",")
                                                      (lab-int (kar (kdr (kdr (kdr (kdr x))))))))))
         (:ldo (list* (kw "do") (lab-int (kadr x)) (fys :ctl (kaddr x))))
         (:format (list (kw "format") (list :fmt (kadr x))))
         (:write (list* (kw "write") (op "(") (append (fys :ios (kadr x)) (fys :oitems (kaddr x)))))
         (:read (list* (kw "read") (op "(") (append (fys :ios (kadr x)) (fys :oitems (kaddr x)))))
         (:function (append (fys :prefix (kadr x)) (fys :fn-rest (kdr (kdr x)))))
         (:subroutine (append (fys :prefix (kadr x)) (fys :sub-rest (kdr (kdr x)))))
         (otherwise nil)))
      (:decl-rest (append (fys :attrs (car x)) (if (kadr x) (dcolon) nil) (fys :ents (kaddr x))))
      (:fn-rest (append (list (kw "function") (car x) (op "(")) (names-y (kadr x))
                        (if (kaddr x) (list (kw "result") (op "(") (kaddr x) (op ")")) nil)))
      (:sub-rest (append (list (kw "subroutine") (car x)) (if (kadr x) (cons (op "(") (names-y (kaddr x))) nil)))
      (:ts (cons (kw (car x))
                 (if (kadr x)
                     (cons (op "(") (append (if (kar (kadr x)) (list (kw "kind") (op "=")) nil)
                                            (fy :expr (kadr (kadr x))) (list (op ")"))))
                   nil)))
      (:attrs (cons (op ",") (append (fys :attr (car x)) (fys :attrs (cdr x)))))
      (:attr (case (car x)
               (:parameter (list (kw "parameter")))
               (:value (list (kw "value")))
               (:intent (append (list (kw "intent") (op "(")) (kw-list (kadr x)) (list (op ")"))))
               (otherwise (list* (kw "dimension") (op "(") (fys :shapes (kadr x))))))
      (:shapes (fys :shapes* x))
      (:shapes* (append (fys :shape (car x)) (if (consp (cdr x)) (cons (op ",") (fys :shapes* (cdr x))) (list (op ")")))))
      (:shape (if (eq (car x) :ex)
                  (append (if (kadr x) (append (fy :expr (kadr x)) (list (op ":"))) nil) (fy :expr (kaddr x)))
                (append (if (kadr x) (fy :expr (kadr x)) nil) (list (op ":")))))
      (:ranges (append (fys :range (car x)) (if (consp (cdr x)) (cons (op ",") (fys :ranges (cdr x))) (list (op ")")))))
      (:ixs (append (fys :ix (car x)) (if (consp (cdr x)) (cons (op ",") (fys :ixs (cdr x))) (list (op ")")))))
      (:ix (append (list (car x) (op "=")) (fy :expr (kadr x)) (cons (op ":") (fy :expr (kaddr x)))
                   (if (kadddr x) (cons (op ":") (fy :expr (kadddr x))) nil)))
      (:range (case (car x)
                (:val (fy :expr (kadr x)))
                (:from (append (fy :expr (kadr x)) (list (op ":"))))
                (:to (cons (op ":") (fy :expr (kadr x))))
                (otherwise (append (fy :expr (kadr x)) (cons (op ":") (fy :expr (kaddr x)))))))
      (:ents (append (fys :ent (car x)) (if (consp (cdr x)) (cons (op ",") (fys :ents (cdr x))) nil)))
      (:ent (append (list (car x)) (if (kadr x) (cons (op "(") (fys :shapes (kadr x))) nil) (fys :init (kaddr x))))
      (:init (cons (op "=") (fy :expr x)))
      (:items (cons (op ",") (append (fy :expr (car x)) (fys :items (cdr x)))))
      (:oitems (append (fy :expr (car x)) (if (consp (cdr x)) (cons (op ",") (fys :oitems (cdr x))) nil)))
      (:ios (append (fys :io (car x))
                    (if (and (unit-pos-p (car x)) (consp (cdr x)) (fmt-pos-p (cadr x)))
                        (list* (op ",") (fmt-tok (kaddr (cadr x))) (fys :kios (cddr x)))
                      (fys :kios (cdr x)))))
      (:kios (cons (op ",") (append (fys :io (car x)) (fys :kios (cdr x)))))
      (:io (case (car x)
             (:unit (append (if (kadr x) (list (kw "unit") (op "=")) nil) (if (eq (kaddr x) :star) (list (op "*")) (fy :expr (kaddr x)))))
             (:fmt (list (kw "fmt") (op "=") (fmt-tok (kaddr x))))
             (otherwise (list (kw "advance") (op "=") (kadr x)))))
      (:ctl (case (car x)
              (:range (append (if (kadr x) (list (op ",")) nil) (list (kaddr x) (op "="))
                              (fy :expr (kadddr x)) (cons (op ",") (fy :expr (kar (kdr (kdr (kdr (kdr x)))))))
                              (if (kadr (kdr (kdr (kdr (kdr x)))))
                                  (cons (op ",") (fy :expr (kadr (kdr (kdr (kdr (kdr x))))))) nil)))
              (:while (append (if (kadr x) (list (op ",")) nil) (list (kw "while") (op "("))
                              (fy :expr (kaddr x)) (list (op ")"))))
              (:conc (append (if (kadr x) (list (op ",")) nil) (list (kw "concurrent") (op "("))
                             (if (kaddr x) (append (fys :ts (kaddr x)) (dcolon)) nil) (fys :ixs (kadddr x))))
              (otherwise nil)))
      ((:names :names1) (names-y x))
      (:onames (onames-y x))
      (:prefix (append (if (eq (kar (car x)) :ts) (fys :ts (kadr (car x))) (list (kw (kadr (car x)))))
                       (fys :prefix (cdr x))))
      (otherwise nil))))

; ---- the parser

(defthm len-kdr
  (and (<= (len (kdr x)) (len x)) (implies (consp x) (< (len (kdr x)) (len x))))
  :rule-classes :linear)

(defun fps-rank (nt)
  (declare (xargs :guard t))
  (case nt (:stmt 12) (:s-unit 11) (:prefix 10) (:decl-rest 9) (:attrs 8) (:ents 7) (:ent 6) (:shapes 6)
    (:shapes* 5) (:shape 4) (:ranges 5) (:range 4) (:ixs 5) (:ix 4) (:names 3) (:names1 2) (:ios 2) (otherwise 1)))

(defun tok-in (tk ss)               ; tk is the keyword name of one of ss
  (declare (xargs :guard (true-listp ss)))
  (and (consp tk) (eq (car tk) :name) (consp (cdr tk)) (null (cddr tk)) (member-equal (cadr tk) ss) t))

; the statement kinds' own nonterminals, :s-*, answer :stmt trees
(defun stmt-nt (tk)
  (declare (xargs :guard t))
  (cond ((or (equal tk (kw "program")) (equal tk (kw "module"))) :s-head)
        ((equal tk (kw "end")) :s-end)
        ((equal tk (kw "use")) :s-use)
        ((equal tk (kw "else")) :s-else)
        ((equal tk (kw "if")) :s-if)
        ((equal tk (kw "do")) :s-do)
        ((equal tk (kw "call")) :s-call)
        ((equal tk (kw "print")) :s-print)
        ((or (tok-in tk '("function" "subroutine")) (tok-in tk *prefix-kws*) (tok-in tk *type-kws*)) :s-unit)
        ((eq (kar tk) :lab) :s-label)
        ((equal tk (kw "go")) :s-goto)
        ((equal tk (kw "write")) :s-write)
        ((equal tk (kw "read")) :s-read)
        ((equal tk (kw "format")) :s-format)
        ((equal tk (kw "select")) :s-select)
        ((equal tk (kw "case")) :s-case)
        ((name-tok-p tk) :s-assign)
        (t :s-other)))

(defun fps (nt toks)
  (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fps-rank nt)) :verify-guards nil))
  (let ((tk (kar toks)))
    (if (atom toks)                      ; what may be empty
        (if (member-eq nt '(:attrs :onames :items :ctl :prefix :init :oitems)) (mv t nil toks) (fail))
    (case nt
      (:stmt (fps (stmt-nt tk) toks))
      (:s-head (if (and (or (equal tk (kw "program")) (equal tk (kw "module"))) (name-tok-p (kadr toks)))
                   (mv t (list (if (equal tk (kw "program")) :program :module) (kadr toks)) (kdr (kdr toks)))
                 (fail)))
      (:s-end (if (not (equal tk (kw "end"))) (fail)
              (if (tok-in (kadr toks) *end-kinds*)
                  (if (and (tok-in (kadr toks) *unit-ends*) (name-tok-p (kaddr toks)))
                      (mv t (list :end (kadr (kadr toks)) (kaddr toks)) (kdr (kdr (kdr toks))))
                    (mv t (list :end (kadr (kadr toks)) nil) (kdr (kdr toks))))
                (mv t (list :end nil nil) (kdr toks)))))
      (:s-other (cond ((equal tk (kw "contains")) (mv t (list :contains) (kdr toks)))
                      ((and (equal tk (kw "implicit")) (equal (kadr toks) (kw "none")))
                       (mv t (list :implicit-none) (kdr (kdr toks))))
                      ((tok-in tk *simple-kinds*) (mv t (list :simple (kadr tk)) (kdr toks)))
                      (t (fail))))
      (:s-use
       (if (not (equal tk (kw "use"))) (fail)
       (let* ((t1 (kdr toks))
              (nat (cond ((and (equal (kar t1) (op ":")) (equal (kadr t1) (op ":"))) :dc)
                         ((and (equal (kar t1) (op ",")) (tok-in (kadr t1) '("intrinsic" "non_intrinsic"))
                               (equal (kaddr t1) (op ":")) (equal (kadddr t1) (op ":")))
                          (kadr (kadr t1)))
                         (t nil)))
              (t2 (cond ((eq nat :dc) (kdr (kdr t1))) (nat (kdr (kdr (kdr (kdr t1))))) (t t1))))
         (cond ((not (name-tok-p (kar t2))) (fail))
               ((and (equal (kadr t2) (op ",")) (equal (kaddr t2) (kw "only")) (equal (kadddr t2) (op ":")))
                (mv-let (ok ns r) (fps :onames (kdr (kdr (kdr (kdr t2)))))
                  (if ok (mv t (list :use nat (kar t2) t ns) r) (fail))))
               (t (mv t (list :use nat (kar t2) nil nil) (kdr t2)))))))
      (:s-else (if (not (equal tk (kw "else"))) (fail)
               (if (and (equal (kadr toks) (kw "if")) (equal (kaddr toks) (op "(")))
                   (mv-let (ok e r) (fp :expr (kdr (kdr (kdr toks))))
                     (if (and ok (equal (kar r) (op ")")) (equal (kadr r) (kw "then")))
                         (mv t (list :else-if e) (kdr (kdr r)))
                       (fail)))
                 (mv t (list :else) (kdr toks)))))
      (:s-if (if (and (equal tk (kw "if")) (equal (kadr toks) (op "(")))
                 (mv-let (ok e r) (fp :expr (kdr (kdr toks)))
                   (cond ((not (and ok (equal (kar r) (op ")")))) (fail))
                         ((aif-labs-p (kdr r))
                          (mv t (list :aif e (kadr (kadr r)) (kadr (kadddr r)) (kadr (kar (cdr (cddddr r))))) (kdr (cdr (cddddr r)))))
                         ((and (equal (kadr r) (kw "then")) (atom (kdr (kdr r))))
                          (mv t (list :if-then e) (kdr (kdr r))))
                         ((not (< (len (kdr r)) (len toks))) (fail))
                         (t (mv-let (ok2 s r2) (fps :stmt (kdr r))
                              (if (and ok2 (action-kind-p (kar s))) (mv t (list :if e s) r2) (fail))))))
               (fail)))
      (:s-do (cond ((not (equal tk (kw "do"))) (fail))
                   ((label-int-p (kadr toks))
                    (mv-let (ok c r) (fps :ctl (kdr (kdr toks))) (if ok (mv t (list :ldo (kadr (kadr toks)) c) r) (fail))))
                   (t (mv-let (ok c r) (fps :ctl (kdr toks)) (if ok (mv t (list :do c) r) (fail))))))
      (:s-label (if (label-tok-p tk) (mv t (list :label (kadr tk)) (kdr toks)) (fail)))
      (:s-goto (if (and (equal tk (kw "go")) (equal (kadr toks) (kw "to")) (label-int-p (kaddr toks)))
                   (mv t (list :goto (kadr (kaddr toks))) (kdr (kdr (kdr toks))))
                 (fail)))
      (:s-format (if (and (equal tk (kw "format")) (fmt-tok-p (kadr toks)))
                     (mv t (list :format (kadr (kadr toks))) (kdr (kdr toks)))
                   (fail)))
      (:s-write
       (if (not (and (equal tk (kw "write")) (equal (kadr toks) (op "(")))) (fail)
         (mv-let (ok cs r) (fps :ios (kdr (kdr toks)))
           (if (not (and ok (< (len r) (len toks)))) (fail)
             (mv-let (ok2 is r2) (fps :oitems r) (if ok2 (mv t (list :write cs is) r2) (fail)))))))
      (:s-read
       (cond ((not (equal tk (kw "read"))) (fail))
             ((equal (kadr toks) (op "("))
              (mv-let (ok cs r) (fps :ios (kdr (kdr toks)))
                (if (not (and ok (< (len r) (len toks)))) (fail)
                  (mv-let (ok2 is r2) (fps :oitems r) (if (and ok2 (all-lone is)) (mv t (list :read cs is) r2) (fail))))))
             ((fmt-head-p (kadr toks))
              (mv-let (ok is r) (fps :items (kdr (kdr toks)))
                (if (and ok (all-lone is)) (mv t (list :readf (fmt-of (kadr toks)) is) r) (fail))))
             (t (fail))))
      (:ios (mv-let (ok c r) (fps :io toks)
              (cond ((not (and ok (< (len r) (len toks)))) (fail))
                    ((and (unit-pos-p c) (equal (kar r) (op ",")) (fmt-head-p (kadr r)))
                     (mv-let (ok2 cs r2) (fps :kios (kdr (kdr r)))
                       (let ((x (list* c (list :fmt nil (fmt-of (kadr r))) cs))) (if (and ok2 (ios-ok x)) (mv t x r2) (fail)))))
                    (t (mv-let (ok2 cs r2) (fps :kios r)
                         (let ((x (cons c cs))) (if (and ok2 (ios-ok x)) (mv t x r2) (fail))))))))
      (:kios (cond ((equal tk (op ")")) (mv t nil (kdr toks)))
                   ((equal tk (op ","))
                    (mv-let (ok c r) (fps :io (kdr toks))
                      (if (not (and ok (not (unit-pos-p c)) (< (len r) (len toks)))) (fail)
                        (mv-let (ok2 cs r2) (fps :kios r) (if ok2 (mv t (cons c cs) r2) (fail))))))
                   (t (fail))))
      (:io (cond ((and (equal tk (kw "unit")) (equal (kadr toks) (op "=")))
                  (if (equal (kaddr toks) (op "*")) (mv t (list :unit t :star) (kdr (kdr (kdr toks))))
                    (mv-let (ok e r) (fp :expr (kdr (kdr toks))) (if ok (mv t (list :unit t e) r) (fail)))))
                 ((and (equal tk (kw "fmt")) (equal (kadr toks) (op "=")))
                  (if (fmt-head-p (kaddr toks)) (mv t (list :fmt t (fmt-of (kaddr toks))) (kdr (kdr (kdr toks)))) (fail)))
                 ((and (equal tk (kw "advance")) (equal (kadr toks) (op "=")))
                  (if (char-tok-p (kaddr toks)) (mv t (list :adv (kaddr toks)) (kdr (kdr (kdr toks)))) (fail)))
                 ((equal tk (op "*")) (mv t (list :unit nil :star) (kdr toks)))
                 (t (mv-let (ok e r) (fp :expr toks) (if ok (mv t (list :unit nil e) r) (fail))))))
      (:oitems (if (atom toks) (mv t nil toks)
                 (mv-let (ok e r) (fp :expr toks)
                   (cond ((not (and ok (< (len r) (len toks)))) (fail))
                         ((atom r) (mv t (list e) r))
                         ((equal (kar r) (op ","))
                          (mv-let (ok2 es r2) (fps :oitems (kdr r)) (if (and ok2 (consp es)) (mv t (cons e es) r2) (fail))))
                         (t (fail))))))
      (:s-call (cond ((not (and (equal tk (kw "call")) (name-tok-p (kadr toks)))) (fail))
                     ((equal (kaddr toks) (op "("))
                      (mv-let (ok as r) (fp :args (kdr (kdr (kdr toks))))
                        (if ok (mv t (list :call (kadr toks) t as) r) (fail))))
                     (t (mv t (list :call (kadr toks) nil nil) (kdr (kdr toks))))))
      (:s-print (if (and (equal tk (kw "print")) (fmt-head-p (kadr toks)))
                    (mv-let (ok is r) (fps :items (kdr (kdr toks))) (if ok (mv t (list :print (fmt-of (kadr toks)) is) r) (fail)))
                  (fail)))
      (:s-assign (if (not (name-tok-p tk)) (fail)
                 (if (equal (kadr toks) (op "("))
                     (mv-let (ok as r) (fp :args (kdr (kdr toks)))
                       (if (and ok (no-kw-args as) (equal (kar r) (op "=")))
                           (mv-let (ok2 e r2) (fp :expr (kdr r))
                             (if ok2 (mv t (list :assign tk t as e) r2) (fail)))
                         (fail)))
                   (if (equal (kadr toks) (op "="))
                       (mv-let (ok e r) (fp :expr (kdr (kdr toks)))
                         (if ok (mv t (list :assign tk nil nil e) r) (fail)))
                     (fail)))))
      (:s-select (if (and (equal tk (kw "select")) (equal (kadr toks) (kw "case")) (equal (kaddr toks) (op "(")))
                     (mv-let (ok e r) (fp :expr (kdr (kdr (kdr toks))))
                       (if (and ok (equal (kar r) (op ")"))) (mv t (list :select e) (kdr r)) (fail)))
                   (fail)))
      (:s-case (cond ((not (equal tk (kw "case"))) (fail))
                     ((equal (kadr toks) (kw "default")) (mv t (list :case-default) (kdr (kdr toks))))
                     ((equal (kadr toks) (op "("))
                      (mv-let (ok rs r) (fps :ranges (kdr (kdr toks))) (if ok (mv t (list :case rs) r) (fail))))
                     (t (fail))))
      (:ranges (mv-let (ok s r) (fps :range toks)
                 (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                       ((equal (kar r) (op ")")) (mv t (list s) (kdr r)))
                       ((equal (kar r) (op ","))
                        (mv-let (ok2 ss r2) (fps :ranges (kdr r)) (if ok2 (mv t (cons s ss) r2) (fail))))
                       (t (fail)))))
      (:ixs (mv-let (ok s r) (fps :ix toks)
              (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                    ((equal (kar r) (op ")")) (mv t (list s) (kdr r)))
                    ((equal (kar r) (op ","))
                     (mv-let (ok2 ss r2) (fps :ixs (kdr r)) (if ok2 (mv t (cons s ss) r2) (fail))))
                    (t (fail)))))
      (:ix (if (and (name-tok-p tk) (equal (kadr toks) (op "=")))
               (mv-let (ok lo r) (fp :expr (kdr (kdr toks)))
                 (if (not (and ok (equal (kar r) (op ":")))) (fail)
                   (mv-let (ok2 hi r2) (fp :expr (kdr r))
                     (cond ((not ok2) (fail))
                           ((equal (kar r2) (op ":"))
                            (mv-let (ok3 st r3) (fp :expr (kdr r2)) (if ok3 (mv t (list tk lo hi st) r3) (fail))))
                           (t (mv t (list tk lo hi nil) r2))))))
             (fail)))
      (:range (if (equal tk (op ":"))
                  (mv-let (ok e r) (fp :expr (kdr toks)) (if ok (mv t (list :to e) r) (fail)))
                (mv-let (ok e r) (fp :expr toks)
                  (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                        ((not (equal (kar r) (op ":"))) (mv t (list :val e) r))
                        ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (mv t (list :from e) (kdr r)))
                        (t (mv-let (ok2 b r2) (fp :expr (kdr r)) (if ok2 (mv t (list :rng e b) r2) (fail))))))))
      (:s-unit
       (mv-let (ok pre r) (fps :prefix toks)
         (cond
          ((not (and ok (<= (len r) (len toks)))) (fail))
          ((equal (kar r) (kw "function"))
           (mv-let (ok2 fr r2) (fps :fn-rest r) (if ok2 (mv t (list* :function pre fr) r2) (fail))))
          ((equal (kar r) (kw "subroutine"))
           (if (assoc-eq :ts pre) (fail)
             (mv-let (ok2 sr r2) (fps :sub-rest r) (if ok2 (mv t (list* :subroutine pre sr) r2) (fail)))))
          ((and (consp pre) (null (cdr pre)) (eq (kar (car pre)) :ts))
           (mv-let (ok2 dr r2) (fps :decl-rest r) (if ok2 (mv t (list* :decl (kadr (car pre)) dr) r2) (fail))))
          (t (fail)))))
      (:fn-rest (if (and (equal tk (kw "function")) (name-tok-p (kadr toks)) (equal (kaddr toks) (op "(")))
                    (mv-let (ok ds r) (fps :names (kdr (kdr (kdr toks))))
                      (cond ((not ok) (fail))
                            ((and (equal (kar r) (kw "result")) (equal (kadr r) (op "("))
                                  (name-tok-p (kaddr r)) (equal (kadddr r) (op ")")))
                             (mv t (list (kadr toks) ds (kaddr r)) (kdr (kdr (kdr (kdr r))))))
                            (t (mv t (list (kadr toks) ds nil) r))))
                  (fail)))
      (:sub-rest (cond ((not (and (equal tk (kw "subroutine")) (name-tok-p (kadr toks)))) (fail))
                       ((equal (kaddr toks) (op "("))
                        (mv-let (ok ds r) (fps :names (kdr (kdr (kdr toks))))
                          (if ok (mv t (list (kadr toks) t ds) r) (fail))))
                       (t (mv t (list (kadr toks) nil nil) (kdr (kdr toks))))))
      (:decl-rest
       (mv-let (ok as r) (fps :attrs toks)
         (if (not (and ok (<= (len r) (len toks)))) (fail)
           (let* ((dc (and (equal (kar r) (op ":")) (equal (kadr r) (op ":")))) (r1 (if dc (kdr (kdr r)) r)))
             (mv-let (ok2 es r2) (fps :ents r1)
               (if (and ok2 (consp es) (implies (or (consp as) (ents-init-p es)) dc))
                   (mv t (list as dc es) r2)
                 (fail)))))))
      (:ts (cond ((not (tok-in tk *type-kws*)) (fail))
                 ((equal (kadr toks) (op "("))
                  (let* ((kwp (and (equal (kaddr toks) (kw "kind")) (kw-head-p (kdr (kdr toks)))))
                         (t1 (if kwp (kdr (kdr (kdr (kdr toks)))) (kdr (kdr toks)))))
                    (mv-let (ok e r) (fp :expr t1)
                      (if (and ok (equal (kar r) (op ")")))
                          (mv t (list (kadr tk) (list kwp e)) (kdr r))
                        (fail)))))
                 (t (mv t (list (kadr tk) nil) (kdr toks)))))
      (:attrs (if (equal tk (op ","))
                  (mv-let (ok a r) (fps :attr (kdr toks))
                    (if (not (and ok (<= (len r) (len (kdr toks))))) (fail)
                      (mv-let (ok2 as r2) (fps :attrs r) (if ok2 (mv t (cons a as) r2) (fail)))))
                (mv t nil toks)))
      (:attr (cond ((equal tk (kw "parameter")) (mv t (list :parameter) (kdr toks)))
                   ((equal tk (kw "value")) (mv t (list :value) (kdr toks)))
                   ((and (equal tk (kw "intent")) (equal (kadr toks) (op "(")))
                    (cond ((and (equal (kaddr toks) (kw "in")) (equal (kadddr toks) (kw "out"))
                                (equal (kar (kdr (kdr (kdr (kdr toks))))) (op ")")))
                           (mv t (list :intent (list "in" "out")) (kdr (kdr (kdr (kdr (kdr toks)))))))
                          ((and (tok-in (kaddr toks) '("in" "out" "inout")) (equal (kadddr toks) (op ")")))
                           (mv t (list :intent (list (kadr (kaddr toks)))) (kdr (kdr (kdr (kdr toks))))))
                          (t (fail))))
                   ((and (equal tk (kw "dimension")) (equal (kadr toks) (op "(")))
                    (mv-let (ok ss r) (fps :shapes (kdr (kdr toks))) (if ok (mv t (list :dimension ss) r) (fail))))
                   (t (fail))))
      (:shapes (mv-let (ok ss r) (fps :shapes* toks)
                 (if (and ok (consp ss) (shapes-same ss (shape-kind (car ss)))) (mv t ss r) (fail))))
      (:shapes* (mv-let (ok s r) (fps :shape toks)
                  (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                        ((equal (kar r) (op ")")) (mv t (list s) (kdr r)))
                        ((equal (kar r) (op ","))
                         (mv-let (ok2 ss r2) (fps :shapes* (kdr r)) (if ok2 (mv t (cons s ss) r2) (fail))))
                        (t (fail)))))
      (:shape (if (equal tk (op ":")) (mv t (list :as nil) (kdr toks))
                (mv-let (ok e r) (fp :expr toks)
                  (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                        ((not (equal (kar r) (op ":"))) (mv t (list :ex nil e) r))
                        ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (mv t (list :as e) (kdr r)))
                        (t (mv-let (ok2 hi r2) (fp :expr (kdr r)) (if ok2 (mv t (list :ex e hi) r2) (fail))))))))
      (:ents (mv-let (ok e r) (fps :ent toks)
               (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                     ((equal (kar r) (op ","))
                      (mv-let (ok2 es r2) (fps :ents (kdr r)) (if ok2 (mv t (cons e es) r2) (fail))))
                     (t (mv t (list e) r)))))
      (:ent (cond ((not (name-tok-p tk)) (fail))
                  ((equal (kadr toks) (op "("))
                   (mv-let (ok ss r) (fps :shapes (kdr (kdr toks)))
                     (if (not (and ok (<= (len r) (len toks)))) (fail)
                       (mv-let (ok2 i r2) (fps :init r) (if ok2 (mv t (list tk ss i) r2) (fail))))))
                  (t (mv-let (ok2 i r2) (fps :init (kdr toks)) (if ok2 (mv t (list tk nil i) r2) (fail))))))
      (:init (if (equal tk (op "="))
                 (mv-let (ok e r) (fp :expr (kdr toks)) (if ok (mv t e r) (fail)))
               (mv t nil toks)))
      (:names (if (equal tk (op ")")) (mv t nil (kdr toks)) (fps :names1 toks)))
      (:names1 (cond ((not (name-tok-p tk)) (fail))
                     ((equal (kadr toks) (op ")")) (mv t (list tk) (kdr (kdr toks))))
                     ((equal (kadr toks) (op ","))
                      (mv-let (ok ns r) (fps :names1 (kdr (kdr toks))) (if ok (mv t (cons tk ns) r) (fail))))
                     (t (fail))))
      (:onames (cond ((not (name-tok-p tk)) (mv t nil toks))
                     ((equal (kadr toks) (op ","))
                      (mv-let (ok ns r) (fps :onames (kdr (kdr toks)))
                        (if (and ok (consp ns)) (mv t (cons tk ns) r) (fail))))
                     (t (mv t (list tk) (kdr toks)))))
      (:items (if (equal tk (op ","))
                  (mv-let (ok e r) (fp :expr (kdr toks))
                    (if (not (and ok (< (len r) (len toks)))) (fail)
                      (mv-let (ok2 es r2) (fps :items r) (if ok2 (mv t (cons e es) r2) (fail)))))
                (mv t nil toks)))
      (:ctl (if (atom toks) (mv t nil toks)
              (let* ((c (equal tk (op ","))) (t1 (if c (kdr toks) toks)))
                (cond ((and (equal (kar t1) (kw "while")) (equal (kadr t1) (op "(")))
                       (mv-let (ok e r) (fp :expr (kdr (kdr t1)))
                         (if (and ok (equal (kar r) (op ")"))) (mv t (list :while c e) (kdr r)) (fail))))
                      ((and (equal (kar t1) (kw "concurrent")) (equal (kadr t1) (op "(")))
                       (let ((t2 (kdr (kdr t1))))
                         (mv-let (ok ts r)
                           (if (tok-in (kar t2) *type-kws*) (fps :ts t2) (mv t nil t2))
                           (cond ((not (and ok (<= (len r) (len t2)))) (fail))
                                 ((and ts (not (and (equal (kar ts) "integer") (equal (kar r) (op ":")) (equal (kadr r) (op ":"))))) (fail))
                                 (t (mv-let (ok2 ixs r2) (fps :ixs (if ts (kdr (kdr r)) r))
                                      (if ok2 (mv t (list :conc c ts ixs) r2) (fail))))))))
                      ((and (name-tok-p (kar t1)) (equal (kadr t1) (op "=")))
                       (mv-let (ok e1 r) (fp :expr (kdr (kdr t1)))
                         (if (not (and ok (equal (kar r) (op ",")))) (fail)
                           (mv-let (ok2 e2 r2) (fp :expr (kdr r))
                             (cond ((not ok2) (fail))
                                   ((equal (kar r2) (op ","))
                                    (mv-let (ok3 e3 r3) (fp :expr (kdr r2))
                                      (if ok3 (mv t (list :range c (kar t1) e1 e2 e3) r3) (fail))))
                                   (t (mv t (list :range c (kar t1) e1 e2 nil) r2)))))))
                      (t (fail))))))
      (:prefix (cond ((tok-in tk *prefix-kws*)
                      (mv-let (ok ps r) (fps :prefix (kdr toks))
                        (if ok (mv t (cons (list :kw (kadr tk)) ps) r) (fail))))
                     ((tok-in tk *type-kws*)
                      (mv-let (ok ts r) (fps :ts toks)
                        (if (not (and ok (< (len r) (len toks)))) (fail)
                          (mv-let (ok2 ps r2) (fps :prefix r)
                            (if ok2 (mv t (cons (list :ts ts) ps) r2) (fail))))))
                     (t (mv t nil toks))))
      (otherwise (fail))))))

