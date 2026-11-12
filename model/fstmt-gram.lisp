; fstmt-gram: the grammar half of fstmt.lisp: fgs, which recognizes one
; statement's trees, and fys, the tokens a tree spells.
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
;                                   (R801) or an initialization (C806);
;                                   ts ("character" (:len tk :comma)) for
;                                   R722's * char-length "," (C724, C725:
;                                   no attrs, no "::"; the first entity's
;                                   name not an attr-spec keyword)
;         (:assign n refp args e)   R1033 assignment-stmt: variable = expr;
;                                   R902 variable, R901 designator: a name
;                                   or a part-ref with its subscripts (R912);
;                                   refp t, or the R910 substring-range
;                                   (:tri lo hi nil) of R908's substring
;                                   name ( args ) ( range )
;         (:cassign n refp args ps e) R1033 with R911's data-ref for the
;                                   variable: n [( args )] then the :parts ps
;                                   (% part-ref ...), a structure component
;         (:type dc n)              R727 derived-type-stmt: TYPE [::]
;                                   type-name (no type-attr-spec in the
;                                   subset); END TYPE [n] is (:end "type" n)
;         (:tdecl n attrs dc ents)  R801 with R703's TYPE ( derived-type-spec ),
;                                   R754 derived-type-spec a type-name (no
;                                   type-param-spec); also R737
;                                   data-component-def-stmt in a type
;         (:if-then e)              R1137 if-then-stmt: IF ( expr ) THEN
;         (:else-if e)              R1138 else-if-stmt: ELSE IF ( expr ) THEN
;         (:else)                   R1139 else-stmt: ELSE
;         (:if e s)                 R1141 if-stmt: IF ( expr ) action-stmt,
;                                   s an action-stmt (R515) other than an
;                                   if-stmt (C1143)
;         (:do ctl)                 R1122 nonlabel-do-stmt: DO [loop-control]
;         (:simple k)               R1135 cycle-stmt, R1158 exit-stmt, R1545
;                                   return-stmt, R1161 continue-stmt, R1162
;                                   stop-stmt without a stop-code (no
;                                   construct name or return value in the
;                                   subset)
;         (:save dc ns)             R856 save-stmt: SAVE [[::] ns], ns saved
;                                   entity names (not a common block's)
;         (:stop e)                 R1162 stop-stmt: STOP stop-code (R1163,
;                                   e an expr; its type is the meaning's)
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
;                                   [kind-selector], REAL [kind-selector],
;                                   LOGICAL [kind-selector]; R706 kind-selector:
;                                   ( [KIND =] scalar-int-constant-expr ),
;                                   ks nil or (kwp e); DOUBLE PRECISION (k
;                                   "double", ks nil); CHARACTER [char-selector]
;                                   (R721, R722 length-selector, no KIND=): ks
;                                   nil, (kwp e) for ( [LEN =] type-param-value )
;                                   (R701: e an expr, or :star for *), or
;                                   (:len tk) for * char-length (R723, an
;                                   int-literal-constant tk), (:plen e) for
;                                   * ( type-param-value ), e an expr or :star
;  :attrs (attr ...)                each written ", attr-spec" (R802):
;                                   (:parameter) PARAMETER, (:value) VALUE,
;                                   (:save) SAVE,
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
            (:decl (and (= (len x) 5)
                        (or (fgs :ts (cadr x))
                            (and (ts-comma-p (cadr x)) (null (caddr x)) (null (cadddr x))
                                 (not (attr-kw-tok-p (kar (kar (car (cddddr x))))))))
                        (fgs :decl-rest (cddr x))))
            (:assign (and (= (len x) 5) (name-tok-p (cadr x)) (or (booleanp (caddr x)) (substr-rng-p (caddr x)))
                          (if (caddr x) (and (fg :args (cadddr x)) (no-kw-args (cadddr x))) (null (cadddr x)))
                          (fg :expr (car (cddddr x)))))
            (:cassign (and (= (len x) 6) (name-tok-p (cadr x)) (booleanp (caddr x))
                           (if (caddr x) (and (fg :args (cadddr x)) (no-kw-args (cadddr x))) (null (cadddr x)))
                           (consp (car (cddddr x))) (fg :parts (car (cddddr x)))
                           (fg :expr (cadr (cddddr x)))))
            (:type (and (= (len x) 3) (booleanp (cadr x)) (name-tok-p (caddr x))))
            (:tdecl (and (= (len x) 5) (name-tok-p (cadr x)) (fgs :decl-rest (cddr x))))
            ((:if-then :else-if) (and (= (len x) 2) (fg :expr (cadr x))))
            (:if (and (= (len x) 3) (fg :expr (cadr x)) (consp (caddr x))
                      (action-kind-p (car (caddr x))) (fgs :stmt (caddr x))))
            (:do (and (= (len x) 2) (fgs :ctl (cadr x))))
            (:simple (and (= (len x) 2) (member-equal (cadr x) *simple-kinds*) t))
            (:stop (and (= (len x) 2) (fg :expr (cadr x))))
            (:save (and (= (len x) 3) (booleanp (cadr x)) (names-p (caddr x)) (or (null (cadr x)) (consp (caddr x)))))
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
                  (and (not (equal (car x) "double"))
                       (true-listp (cadr x)) (= (len (cadr x)) 2)
                       (case (car (cadr x))
                         (:len (and (equal (car x) "character") (len-tok-p (cadr (cadr x)))))
                         (:plen (and (equal (car x) "character")
                                     (or (eq (cadr (cadr x)) :star) (fg :expr (cadr (cadr x))))))
                         (otherwise
                          (and (booleanp (car (cadr x)))
                              (if (eq (cadr (cadr x)) :star) (equal (car x) "character")
                                (fg :expr (cadr (cadr x)))))))))))
    (:attrs (if (atom x) (null x) (and (fgs :attr (car x)) (fgs :attrs (cdr x)))))
    (:attr (and (true-listp x)
                (case (car x)
                  ((:parameter :value :save) (= (len x) 1))
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
         (:decl (append (fys :ts (kadr x)) (if (ts-comma-p (kadr x)) (list (op ",")) nil) (fys :decl-rest (kdr (kdr x)))))
         (:assign (append (list (kadr x)) (if (kaddr x) (cons (op "(") (fy :args (kadddr x))) nil)
                          (if (consp (kaddr x)) (cons (op "(") (append (fy :arg (kaddr x)) (list (op ")")))) nil)
                          (cons (op "=") (fy :expr (kar (kdr (kdr (kdr (kdr x)))))))))
         (:cassign (append (list (kadr x)) (if (kaddr x) (cons (op "(") (fy :args (kadddr x))) nil)
                           (fy :parts (kar (kdr (kdr (kdr (kdr x))))))
                           (cons (op "=") (fy :expr (kadr (kdr (kdr (kdr (kdr x)))))))))
         (:type (cons (kw "type") (append (if (kadr x) (dcolon) nil) (list (kaddr x)))))
         (:tdecl (list* (kw "type") (op "(") (kadr x) (op ")") (fys :decl-rest (kdr (kdr x)))))
         (:if-then (list* (kw "if") (op "(") (append (fy :expr (kadr x)) (list (op ")") (kw "then")))))
         (:else-if (list* (kw "else") (kw "if") (op "(") (append (fy :expr (kadr x)) (list (op ")") (kw "then")))))
         (:if (list* (kw "if") (op "(") (append (fy :expr (kadr x)) (cons (op ")") (fys :stmt (kaddr x))))))
         (:do (cons (kw "do") (fys :ctl (kadr x))))
         (:simple (list (kw (kadr x))))
         (:stop (cons (kw "stop") (fy :expr (kadr x))))
         (:save (cons (kw "save") (append (if (kadr x) (dcolon) nil) (onames-y (kaddr x)))))
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
                 (cond ((equal (car x) "double") (list (kw "precision")))
                       ((not (kadr x)) nil)
                       ((eq (kar (kadr x)) :len) (list (op "*") (kadr (kadr x))))
                       ((eq (kar (kadr x)) :plen)
                        (list* (op "*") (op "(") (append (if (eq (kadr (kadr x)) :star) (list (op "*")) (fy :expr (kadr (kadr x))))
                                                         (list (op ")")))))
                       (t (cons (op "(") (append (if (kar (kadr x)) (list (kw (if (equal (car x) "character") "len" "kind")) (op "=")) nil)
                                                 (if (eq (kadr (kadr x)) :star) (list (op "*")) (fy :expr (kadr (kadr x))))
                                                 (list (op ")"))))))))
      (:attrs (cons (op ",") (append (fys :attr (car x)) (fys :attrs (cdr x)))))
      (:attr (case (car x)
               (:parameter (list (kw "parameter")))
               (:value (list (kw "value")))
               (:save (list (kw "save")))
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

