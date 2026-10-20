; fstmt: the subset's statements (Stage A, item 1, continued): grammar
; (fgs, fys) and parser (fps) over one statement's tokens, the
; expressions read by fparse.lisp's fp. As there: fps-sound and
; fps-complete prove that fps accepts exactly the statements fgs allows,
; and answers the one tree that spells them.
; fps-cost bounds its work: a successful parse makes at most 64 calls
; (fp's among them) per token it consumes, plus fps-d nt.
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
;         (:print items)            R1212 print-stmt: PRINT format [,
;                                   output-item-list]; R1215 format *;
;                                   R1217 output-item: expr
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
;  :prefix (spec ...)               R1529 prefix, R1530 prefix-spec:
;                                   (:ts ts) a declaration-type-spec, or
;                                   (:kw k) ELEMENTAL IMPURE NON_RECURSIVE
;                                   PURE RECURSIVE

(in-package "ACL2")

(include-book "fparse")

(defun kw (s) (declare (xargs :guard t)) (list :name s))

(defconst *end-kinds* '("program" "module" "function" "subroutine" "do" "if" "select"))
(defconst *unit-ends* '("program" "module" "function" "subroutine"))
(defconst *simple-kinds* '("cycle" "exit" "return" "continue" "stop"))
(defconst *prefix-kws* '("pure" "elemental" "impure" "recursive" "non_recursive"))
(defconst *type-kws* '("integer" "logical" "real"))
(defconst *intents* '(("in") ("out") ("inout") ("in" "out")))

(defun fg-expr (e) (declare (xargs :guard t)) (fg :expr e))

(defun names-p (ns)
  (declare (xargs :guard t))
  (if (atom ns) (null ns) (and (name-tok-p (car ns)) (names-p (cdr ns)))))

(defun shape-kind (s) (declare (xargs :guard t)) (kar s))
(defun shapes-same (ss k)
  (declare (xargs :guard t))
  (if (atom ss) t (and (equal (shape-kind (car ss)) k) (shapes-same (cdr ss) k))))

(defun no-kw-args (as)            ; a designator's subscripts: no keyword (R912)
  (declare (xargs :guard t))
  (if (atom as) t (and (not (eq (kar (car as)) :kw)) (no-kw-args (cdr as)))))

(defun action-kind-p (k)          ; R515, C1143
  (declare (xargs :guard t))
  (and (member-eq k '(:assign :simple :call :print)) t))

(defun ents-init-p (ents)
  (declare (xargs :guard t))
  (if (atom ents) nil (or (and (consp (car ents)) (kaddr (car ents)) t) (ents-init-p (cdr ents)))))


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
            (:print (and (= (len x) 2) (fgs :items (cadr x))))
            (:select (and (= (len x) 2) (fg :expr (cadr x))))
            (:case (and (= (len x) 2) (fgs :ranges (cadr x))))
            (:case-default (= (len x) 1))
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
    (:ctl (or (null x)
              (and (true-listp x)
                   (case (car x)
                     (:range (and (= (len x) 6) (booleanp (cadr x)) (name-tok-p (caddr x))
                                  (fg :expr (cadddr x)) (fg :expr (car (cddddr x)))
                                  (or (null (cadr (cddddr x))) (fg :expr (cadr (cddddr x))))))
                     (:while (and (= (len x) 3) (booleanp (cadr x)) (fg :expr (caddr x))))
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
      (case nt ((:shapes :shapes* :names :names1 :ranges) (list (op ")"))) (otherwise nil))
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
         (:print (list* (kw "print") (op "*") (fys :items (kadr x))))
         (:select (list* (kw "select") (kw "case") (op "(") (append (fy :expr (kadr x)) (list (op ")")))))
         (:case (list* (kw "case") (op "(") (fys :ranges (kadr x))))
         (:case-default (list (kw "case") (kw "default")))
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
      (:range (case (car x)
                (:val (fy :expr (kadr x)))
                (:from (append (fy :expr (kadr x)) (list (op ":"))))
                (:to (cons (op ":") (fy :expr (kadr x))))
                (otherwise (append (fy :expr (kadr x)) (cons (op ":") (fy :expr (kaddr x)))))))
      (:ents (append (fys :ent (car x)) (if (consp (cdr x)) (cons (op ",") (fys :ents (cdr x))) nil)))
      (:ent (append (list (car x)) (if (kadr x) (cons (op "(") (fys :shapes (kadr x))) nil) (fys :init (kaddr x))))
      (:init (cons (op "=") (fy :expr x)))
      (:items (cons (op ",") (append (fy :expr (car x)) (fys :items (cdr x)))))
      (:ctl (case (car x)
              (:range (append (if (kadr x) (list (op ",")) nil) (list (kaddr x) (op "="))
                              (fy :expr (kadddr x)) (cons (op ",") (fy :expr (kar (kdr (kdr (kdr (kdr x)))))))
                              (if (kadr (kdr (kdr (kdr (kdr x)))))
                                  (cons (op ",") (fy :expr (kadr (kdr (kdr (kdr (kdr x))))))) nil)))
              (:while (append (if (kadr x) (list (op ",")) nil) (list (kw "while") (op "("))
                              (fy :expr (kaddr x)) (list (op ")"))))
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
    (:shapes* 5) (:shape 4) (:ranges 5) (:range 4) (:names 3) (:names1 2) (otherwise 1)))

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
        ((equal tk (kw "select")) :s-select)
        ((equal tk (kw "case")) :s-case)
        ((name-tok-p tk) :s-assign)
        (t :s-other)))

(defun fps (nt toks)
  (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fps-rank nt)) :verify-guards nil))
  (let ((tk (kar toks)))
    (if (atom toks)                      ; what may be empty
        (if (member-eq nt '(:attrs :onames :items :ctl :prefix :init)) (mv t nil toks) (fail))
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
                         ((and (equal (kadr r) (kw "then")) (atom (kdr (kdr r))))
                          (mv t (list :if-then e) (kdr (kdr r))))
                         ((not (< (len (kdr r)) (len toks))) (fail))
                         (t (mv-let (ok2 s r2) (fps :stmt (kdr r))
                              (if (and ok2 (action-kind-p (kar s))) (mv t (list :if e s) r2) (fail))))))
               (fail)))
      (:s-do (if (not (equal tk (kw "do"))) (fail)
               (mv-let (ok c r) (fps :ctl (kdr toks)) (if ok (mv t (list :do c) r) (fail)))))
      (:s-call (cond ((not (and (equal tk (kw "call")) (name-tok-p (kadr toks)))) (fail))
                     ((equal (kaddr toks) (op "("))
                      (mv-let (ok as r) (fp :args (kdr (kdr (kdr toks))))
                        (if ok (mv t (list :call (kadr toks) t as) r) (fail))))
                     (t (mv t (list :call (kadr toks) nil nil) (kdr (kdr toks))))))
      (:s-print (if (and (equal tk (kw "print")) (equal (kadr toks) (op "*")))
                    (mv-let (ok is r) (fps :items (kdr (kdr toks))) (if ok (mv t (list :print is) r) (fail)))
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

(defthm fg-expr-consp (implies (fg :expr x) (consp x)) :hints (("Goal" :expand ((fg :expr x)))))
(defthm fg-args-true-listp (implies (fg :args x) (true-listp x)) :hints (("Goal" :expand ((fg :args x)))))

; an expression fp reads is a tree, never nil
(defthm fp-expr-tree
  (implies (mv-nth 0 (fp :expr toks)) (mv-nth 1 (fp :expr toks)))
  :hints (("Goal" :use ((:instance fp-sound (nt :expr))) :in-theory (disable fp-sound))))

; fps opens only where a proof says so
(in-theory (disable fps))

; the tree nt answers: an :s-* answers a statement
(defun gnt (nt) (declare (xargs :guard t)) (if (member-eq nt '(:s-head :s-end :s-other :s-use :s-else :s-if :s-do :s-call :s-print :s-assign :s-unit :s-select :s-case)) :stmt nt))

; the parts' shapes, and fgs and fys opened only on a tree being built
; (a cons): a subtree a hypothesis speaks of stays closed
(defthm parts-shape
  (and (implies (fgs :decl-rest x) (and (true-listp x) (equal (len x) 3)))
       (implies (fgs :fn-rest x) (and (true-listp x) (equal (len x) 3)))
       (implies (fgs :sub-rest x) (and (true-listp x) (equal (len x) 3)))
       (implies (fgs :ts x) (and (true-listp x) (equal (len x) 2))))
  :hints (("Goal" :expand ((fgs :decl-rest x) (fgs :fn-rest x) (fgs :sub-rest x) (fgs :ts x)))))

(set-ignore-ok t)
(defmacro def-cons-opener (name call)
  `(make-event
    (let ((fn (car ',call)))
      `(defthm ,',name
         (implies (syntaxp (and (quotep nt) (consp x) (member-eq (car x) '(cons quote))))
                  (equal ,',call ,(body fn nil (w state))))
         :hints (("Goal" :expand (,',call)))))))
(def-cons-opener fgs-cons-open (fgs nt x))
(def-cons-opener fys-cons-open (fys nt x))
(in-theory (disable fgs fys shape-kind))

; the nonterminals that only rename a recognizer or a spelling
(defthm fgs-fys-aliases
  (and (equal (fgs :names x) (names-p x)) (equal (fgs :onames x) (names-p x))
       (equal (fgs :names1 x) (and (consp x) (names-p x)))
       (equal (fys :names x) (names-y x)) (equal (fys :names1 x) (names-y x))
       (equal (fys :onames x) (onames-y x))
       (equal (fgs :shapes x) (and (consp x) (shapes-same x (shape-kind (car x))) (fgs :shapes* x)))
       (equal (fys :shapes x) (fys :shapes* x)))
  :hints (("Goal" :in-theory (enable fgs fys))))

; a prefix that is one type-spec: the declaration's
(defthm prefix-just-ts
  (implies (and (fgs :prefix p) (consp p) (null (cdr p)) (equal (car (car p)) :ts))
           (and (consp (cdr (car p))) (fgs :ts (cadr (car p))) (equal (fys :prefix p) (fys :ts (cadr (car p))))))
  :rule-classes nil
  :hints (("Goal" :expand ((fgs :prefix p) (fys :prefix p) (fgs :prefix (cdr p)) (fys :prefix (cdr p))))))

; the lists that are never empty
(defthm nonempty-parts
  (and (implies (fgs :shapes* x) (consp x)) (implies (fgs :ents x) (consp x)) (implies (fgs :ranges x) (consp x)))
  :hints (("Goal" :expand ((fgs :shapes* x) (fgs :ents x) (fgs :ranges x)))))

; fps-sound, bottom up: one lemma per nonterminal, in an order where
; each one's calls are already answered, by an induction on that
; nonterminal's own calls (its nt a constant)
; the conclusion about a tree x of nt and the rest r, in the canonical
; forms fgs-fys-aliases rewrites to
(defun sound-concl (nt x r toks)
  (declare (xargs :mode :program))
  (let ((g (gnt nt)))
   (append
    ; the trees never nil
    (if (member-eq g '(:stmt :shapes :shapes* :ents :ent :names1 :ts :attr :shape :decl-rest :fn-rest :sub-rest :ranges :range))
        `(and ,x) '(and))
    (list
    (case g
      ((:names :onames) `(and (names-p ,x) (equal (append ,(if (eq g :onames) `(onames-y ,x) `(names-y ,x)) ,r) ,toks)))
      (:names1 `(and (consp ,x) (names-p ,x) (equal (append (names-y ,x) ,r) ,toks)))
      (:shapes `(and (consp ,x) (shapes-same ,x (shape-kind (car ,x))) (fgs :shapes* ,x)
                     (equal (append (fys :shapes* ,x) ,r) ,toks)))
      (otherwise `(and (fgs ,g ,x) (equal (append (fys ,g ,x) ,r) ,toks))))))))

; a list nonterminal's own recursion, for its inductions: each call on the
; tokens after an item, as fps makes it
(defun list-ind (nt toks)
  (declare (xargs :measure (len toks)))
  (if (atom toks) nil
    (mv-let (go r)
      (case nt
        (:shapes* (mv-let (ok s r) (fps :shape toks) (declare (ignore s))
                    (if (and ok (equal (kar r) (op ","))) (mv t (kdr r)) (mv nil nil))))
        (:ranges (mv-let (ok s r) (fps :range toks) (declare (ignore s))
                   (if (and ok (equal (kar r) (op ","))) (mv t (kdr r)) (mv nil nil))))
        (:names1 (if (equal (kadr toks) (op ",")) (mv t (kdr (kdr toks))) (mv nil nil)))
        (:onames (if (and (name-tok-p (kar toks)) (equal (kadr toks) (op ","))) (mv t (kdr (kdr toks))) (mv nil nil)))
        (:attrs (if (equal (kar toks) (op ","))
                    (mv-let (ok a r) (fps :attr (kdr toks)) (declare (ignore a)) (if ok (mv t r) (mv nil nil)))
                  (mv nil nil)))
        (:ents (mv-let (ok e r) (fps :ent toks) (declare (ignore e))
                 (if (and ok (equal (kar r) (op ","))) (mv t (kdr r)) (mv nil nil))))
        (:items (if (equal (kar toks) (op ","))
                    (mv-let (ok e r) (fp :expr (kdr toks)) (declare (ignore e)) (if ok (mv t r) (mv nil nil)))
                  (mv nil nil)))
        (otherwise (cond ((tok-in (kar toks) *prefix-kws*) (mv t (kdr toks)))
                         ((tok-in (kar toks) *type-kws*)
                          (mv-let (ok ts r) (fps :ts toks) (declare (ignore ts)) (if ok (mv t r) (mv nil nil))))
                         (t (mv nil nil)))))
      (if (and go (< (len r) (len toks))) (list-ind nt r) nil))))

(defmacro fps-sound-at (nt)          ; a list nt inducts on list-ind
  (if (member-eq nt '(:shapes* :names1 :onames :attrs :ents :items :prefix :ranges))
      `(defthm ,(packn (list 'fps-sound- nt))
         (implies (mv-nth 0 (fps ,nt toks))
                  ,(sound-concl nt `(mv-nth 1 (fps ,nt toks)) `(mv-nth 2 (fps ,nt toks)) 'toks))
         :hints (("Goal" :induct (list-ind ,nt toks) :expand ((fps ,nt toks)) :in-theory (enable member-equal))))
    `(defthm ,(packn (list 'fps-sound- nt))
       (implies (mv-nth 0 (fps ,nt toks))
                ,(sound-concl nt `(mv-nth 1 (fps ,nt toks)) `(mv-nth 2 (fps ,nt toks)) 'toks))
       :hints (("Goal" :expand ((fps ,nt toks))
                :in-theory ,(if (eq nt :init) '(enable member-equal fgs fys) '(enable member-equal)))))))

(fps-sound-at :init)
(fps-sound-at :ts)
(fps-sound-at :shape)
(fps-sound-at :range)
(fps-sound-at :items)
(fps-sound-at :ctl)
(fps-sound-at :onames)
(fps-sound-at :names1)
(fps-sound-at :names)
(fps-sound-at :shapes*)
(fps-sound-at :ranges)
(fps-sound-at :shapes)
(fps-sound-at :attr)
(fps-sound-at :attrs)
(fps-sound-at :ent)
(fps-sound-at :ents)
(fps-sound-at :decl-rest)
(fps-sound-at :prefix)
(fps-sound-at :fn-rest)
(fps-sound-at :sub-rest)
(fps-sound-at :s-head)
(fps-sound-at :s-end)
(fps-sound-at :s-other)
(fps-sound-at :s-use)
(fps-sound-at :s-else)
(fps-sound-at :s-do)
(fps-sound-at :s-call)
(fps-sound-at :s-print)
(fps-sound-at :s-assign)
(fps-sound-at :s-select)
(fps-sound-at :s-case)
; a declaration's type-spec, read as a prefix of one type-spec
(defthm fps-prefix-just-ts
  (let ((p (mv-nth 1 (fps :prefix toks))))
    (implies (and (mv-nth 0 (fps :prefix toks)) (consp p) (null (cdr p)) (equal (car (car p)) :ts))
             (and (consp (cdr (car p))) (fgs :ts (cadr (car p)))
                  (equal (append (fys :ts (cadr (car p))) (mv-nth 2 (fps :prefix toks))) toks))))
  :hints (("Goal" :use ((:instance prefix-just-ts (p (mv-nth 1 (fps :prefix toks))))) :in-theory (disable fps-sound-prefix))
          ("Goal'" :use fps-sound-prefix)))

(fps-sound-at :s-unit)

; the statements other than IF, as one
(defthm fps-sound-flat
  (implies (and (member-eq nt '(:s-head :s-end :s-other :s-use :s-else :s-do :s-call :s-print :s-assign :s-unit :s-select :s-case))
                (mv-nth 0 (fps nt toks)))
           (and (fgs :stmt (mv-nth 1 (fps nt toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps nt toks))) (mv-nth 2 (fps nt toks))) toks)))
  :hints (("Goal" :in-theory (enable member-equal))))

; IF's recursion, for the induction: the action statement after IF ( e )
(defun stmt-ind (nt toks)          ; the statement inside is a :stmt, whatever nt was
  (declare (xargs :measure (len toks)) (ignorable nt))
  (if (and (consp toks) (equal (kar toks) (kw "if")) (equal (kadr toks) (op "(")))
      (mv-let (ok e r) (fp :expr (kdr (kdr toks)))
        (declare (ignore e))
        (if (and ok (equal (kar r) (op ")")) (< (len (kdr r)) (len toks))) (stmt-ind :stmt (kdr r)) nil))
    nil))

; a statement, and an IF statement around one
(defthm fps-sound-stmt
  (implies (and (member-eq nt '(:stmt :s-if)) (mv-nth 0 (fps nt toks)))
           (and (fgs :stmt (mv-nth 1 (fps nt toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps nt toks))) (mv-nth 2 (fps nt toks))) toks)))
  :hints (("Goal" :induct (stmt-ind nt toks) :in-theory (enable member-equal)
           :expand ((fps :stmt toks) (fps :s-if toks)))))

(defconst *fps-nts*
  '(:stmt :s-head :s-end :s-other :s-use :s-else :s-if :s-do :s-call :s-print :s-assign :s-unit :s-select :s-case
    :fn-rest :sub-rest :decl-rest :ts :attrs :attr :shapes :shapes* :shape :ranges :range :ents :ent :init
    :names :names1 :onames :items :ctl :prefix))

(defthm fps-other
  (implies (not (member-equal nt *fps-nts*)) (not (mv-nth 0 (fps nt toks))))
  :hints (("Goal" :expand ((fps nt toks)) :in-theory (enable member-equal))))

(defun nt-cases (nts) (declare (xargs :mode :program))
  (if (endp nts) nil (cons `(equal nt ,(car nts)) (nt-cases (cdr nts)))))

; fps-sound: what fps answers is a tree of its nonterminal (an :s-* answers
; a statement), and spells the tokens it read
(make-event
 `(defthm fps-sound
    (implies (mv-nth 0 (fps nt toks))
             (and (fgs (gnt nt) (mv-nth 1 (fps nt toks)))
                  (equal (append (fys (gnt nt) (mv-nth 1 (fps nt toks))) (mv-nth 2 (fps nt toks))) toks)))
    :hints (("Goal" :cases ,(nt-cases *fps-nts*) :in-theory (enable member-equal)))))

; what fps consumed is a spelling: the rest is no longer than its tokens
(defthm fps-len
  (implies (mv-nth 0 (fps nt toks))
           (<= (len (mv-nth 2 (fps nt toks))) (len toks)))
  :rule-classes :linear
  :hints (("Goal" :use fps-sound :in-theory (disable fps-sound))))

; ---- fps-complete: every statement is read back as its own tree
;
; As fparse.lisp's fp-complete, bottom up: for each nonterminal, the
; spelling of any of its trees, followed by anything that does not
; continue it (sfollow-ok), is read back as that tree.

(defun scont-tok-p (nt tk)
  (declare (xargs :guard t))
  (case nt
    (:ts (equal tk (op "(")))
    (:attrs (equal tk (op ",")))
    ((:shape :range) (not (member-equal tk (list (op ",") (op ")")))))   ; a shape or a range is ended by "," or ")" only
    (:init (cont-tok-p :expr tk))
    (:ent (or (cont-tok-p :expr tk) (equal tk (op "(")) (equal tk (op "="))))
    ((:ents :decl-rest) (or (cont-tok-p :expr tk) (equal tk (op "(")) (equal tk (op "=")) (equal tk (op ","))))
    (:prefix (or (tok-in tk *prefix-kws*) (tok-in tk *type-kws*) (equal tk (op "("))))
    (:fn-rest (equal tk (kw "result")))
    (:sub-rest (equal tk (op "(")))
    ((:shapes :shapes* :names :names1 :ranges) nil)
    (otherwise t)))                       ; a statement is whole; DO's control ends it

(defun sfollow-ok (nt r)
  (declare (xargs :guard t))
  (if (atom r) (not (member-eq nt '(:shape :range))) (not (scont-tok-p nt (car r)))))

(defthm sfollow-facts
  (and (implies (and (atom r) (not (member-eq nt '(:shape :range)))) (sfollow-ok nt r))
       (equal (sfollow-ok nt (cons a b)) (not (scont-tok-p nt a)))
       (equal (sfollow-ok nt (append a b)) (if (consp a) (not (scont-tok-p nt (car a))) (sfollow-ok nt b)))
       (implies (member-eq nt '(:shapes :shapes* :names :names1 :ranges)) (sfollow-ok nt r))
       ; what follows an initialization or a shape follows its expression
       (implies (sfollow-ok :init r) (follow-ok :expr r))
       (implies (sfollow-ok :shape r) (follow-ok :expr r))
       (implies (sfollow-ok :shape r) (consp r))
       (implies (sfollow-ok :range r) (follow-ok :expr r))
       (implies (sfollow-ok :range r) (consp r))
       (implies (and (sfollow-ok :range r) (not (equal (car r) (op ",")))) (equal (car r) (op ")")))
       ; PRINT's items, ONLY's names, DO's control, a statement: the statement's end follows
       (implies (and (sfollow-ok nt r) (member-eq nt '(:items :onames :ctl :stmt))) (atom r))
       (implies (sfollow-ok :items r) (and (atom r) (follow-ok :expr r)))
       (implies (sfollow-ok :ctl r) (and (atom r) (follow-ok :expr r)))
       (implies (and (sfollow-ok :shape r) (not (equal (car r) (op ",")))) (equal (car r) (op ")")))
       (implies (sfollow-ok :ent r) (sfollow-ok :init r))
       (implies (sfollow-ok :ents r) (sfollow-ok :ent r))
       (implies (sfollow-ok :decl-rest r) (sfollow-ok :ents r)))
  :hints (("Goal" :in-theory (enable sfollow-ok follow-ok member-equal))))

(in-theory (disable sfollow-ok scont-tok-p))

; fgs and fys opened one level on a variable tree (a subtree a hypothesis
; speaks of is no variable, and stays closed)
(defmacro def-var-opener (name call)
  `(make-event
    (let ((fn (car ',call)))
      `(defthm ,',name
         (implies (syntaxp (and (quotep nt) (symbolp x))) (equal ,',call ,(body fn nil (w state))))
         :hints (("Goal" :expand (,',call)))))))
(def-var-opener fgs-var-open (fgs nt x))
(def-var-opener fys-var-open (fys nt x))

; fps opens on a constant nt over tokens that are a cons, or the spelling
; of a tree of another nt; never over (append (fys 'nt t) r), the call an
; induction hypothesis or an earlier fps-complete- lemma answers
(make-event
 `(defthm fps-open
    (implies (syntaxp (and (quotep nt) (consp toks)
                           (or (eq (car toks) 'cons)
                               (and (eq (car toks) 'binary-append)
                                    (consp (cadr toks)) (member-eq (car (cadr toks)) '(fys fy))
                                    (not (equal (cadr (cadr toks)) nt))))))
             (equal (fps nt toks) ,(body 'fps nil (w state))))
    :hints (("Goal" :expand ((fps nt toks))))))

; an expression stays whole here: fp-complete reads it back
(in-theory (disable fy-open fg-open fp-open))

; an expression's spelling begins with none of the punctuation around it
(defthm expr-first-not
  (implies (fg :expr x)
           (and (consp (fy :expr x))
                (not (equal (car (fy :expr x)) '(:op ":"))) (not (equal (car (fy :expr x)) '(:op ",")))
                (not (equal (car (fy :expr x)) '(:op ")"))) (not (equal (car (fy :expr x)) '(:op "=")))))
  :hints (("Goal" :use ((:instance fy-first-expr)) :in-theory (e/d (start-tok-p) (fy-first-expr)))))

; the parts that may be empty, read back as empty
(defthm fps-empty
  (and (implies (sfollow-ok :init r) (equal (fps :init r) (mv t nil r)))
       (implies (sfollow-ok :attrs r) (equal (fps :attrs r) (mv t nil r)))
       (implies (sfollow-ok :items r) (equal (fps :items r) (mv t nil r)))
       (implies (sfollow-ok :prefix r) (equal (fps :prefix r) (mv t nil r)))
       (implies (sfollow-ok :onames r) (equal (fps :onames r) (mv t nil r)))
       (implies (sfollow-ok :ctl r) (equal (fps :ctl r) (mv t nil r))))
  :hints (("Goal" :expand ((fps :init r) (fps :attrs r) (fps :items r) (fps :prefix r) (fps :onames r) (fps :ctl r))
           :in-theory (enable sfollow-ok scont-tok-p cont-tok-p member-equal))))

; first tokens of the parts' spellings, and their shapes
(defthm fys-first
  (and (implies (not (consp x)) (and (equal (fys :items x) nil) (equal (fys :attrs x) nil) (equal (fys :prefix x) nil)
                                     (equal (fys :onames x) nil) (equal (fys :ctl x) nil) (equal (fys :init x) nil)))
       (implies (fgs :ts x) (and (consp (fys :ts x)) (tok-in (car (fys :ts x)) *type-kws*)))
       (implies (and (fgs :attrs x) (consp x)) (and (consp (fys :attrs x)) (equal (car (fys :attrs x)) (op ","))))
       (implies (and (fgs :items x) (consp x)) (and (consp (fys :items x)) (equal (car (fys :items x)) (op ","))))
       (implies (and (fgs :prefix x) (consp x))
                (and (consp (fys :prefix x))
                     (or (tok-in (car (fys :prefix x)) *prefix-kws*) (tok-in (car (fys :prefix x)) *type-kws*))))
       (implies (fgs :ent x) (and (consp (fys :ent x)) (name-tok-p (car (fys :ent x)))))
       (implies (fgs :ents x) (and (consp (fys :ents x)) (name-tok-p (car (fys :ents x)))))
       (implies (and (fgs :init x) x) (and (consp (fys :init x)) (equal (car (fys :init x)) (op "="))))
       (implies (and (fgs :init x) (not x)) (equal (fys :init x) nil))
       (implies (fgs :shape x) (and (consp (fys :shape x))
                                    (or (start-tok-p (car (fys :shape x))) (equal (car (fys :shape x)) (op ":")))))
       (implies (fgs :range x) (and (consp (fys :range x))
                                    (or (start-tok-p (car (fys :range x))) (equal (car (fys :range x)) (op ":")))))
       (implies (fgs :ranges x) (and (consp (fys :ranges x))
                                     (or (start-tok-p (car (fys :ranges x))) (equal (car (fys :ranges x)) (op ":")))))
       (implies (fgs :shapes* x) (and (consp (fys :shapes* x))
                                      (or (start-tok-p (car (fys :shapes* x))) (equal (car (fys :shapes* x)) (op ":")))))
       (implies (and (fgs :onames x) (consp x)) (and (consp (fys :onames x)) (name-tok-p (car (fys :onames x)))))
       (implies (fgs :names1 x) (and (consp (fys :names1 x)) (name-tok-p (car (fys :names1 x)))))
       (implies (and (fgs :ctl x) x)
                (and (consp (fys :ctl x)) (or (equal (car (fys :ctl x)) (op ",")) (name-tok-p (car (fys :ctl x)))))))
  :hints (("Goal" :in-theory (enable fgs fys names-p names-y onames-y member-equal)
           :expand ((fgs :shapes* x) (fys :shapes* x) (fgs :ranges x) (fys :ranges x) (fgs :ents x) (fys :ents x) (fgs :prefix x) (fys :prefix x)
                    (onames-y x) (names-y x) (names-p x)))))

; each lemma expands its own call on the spelling, and nothing else of its nt
; what follows an item: another, or the statement's end
; a name is no punctuation
(defthm name-tok-not-punct
  (implies (name-tok-p tk)
           (and (not (equal tk '(:op ":"))) (not (equal tk '(:op ","))) (not (equal tk '(:op "(")))
                (not (equal tk '(:op "="))) (not (equal tk '(:op ")")))
                (not (equal tk '(:name "function"))) (not (equal tk '(:name "subroutine")))))
  :hints (("Goal" :in-theory (enable name-tok-p))))

; a one-part list, and a six-part list (DO's range), equal the list of their parts
(defthm equal-list1
  (implies (and (true-listp x) (equal (len x) 1)) (equal (equal x (list a)) (equal (car x) a)))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (true-listp x) (true-listp (cdr x))))))
(defthm equal-list3
  (implies (and (true-listp x) (equal (len x) 3))
           (equal (equal x (list a b c))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c))))
  :hints (("Goal" :expand ((len x) (true-listp x) (len (cdr x)) (true-listp (cdr x)) (len (cddr x)) (true-listp (cddr x)) (len (cdddr x)) (true-listp (cdddr x))))))
(defthm equal-list4
  (implies (and (true-listp x) (equal (len x) 4))
           (equal (equal x (list a b c d))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d))))
  :hints (("Goal" :expand ((len x) (true-listp x) (len (cdr x)) (true-listp (cdr x)) (len (cddr x)) (true-listp (cddr x)) (len (cdddr x)) (true-listp (cdddr x)) (len (cddddr x)) (true-listp (cddddr x))))))
(defthm equal-list5
  (implies (and (true-listp x) (equal (len x) 5))
           (equal (equal x (list a b c d e))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d) (equal (car (cddddr x)) e))))
  :hints (("Goal" :expand ((len x) (true-listp x) (len (cdr x)) (true-listp (cdr x)) (len (cddr x)) (true-listp (cddr x)) (len (cdddr x)) (true-listp (cdddr x)) (len (cddddr x)) (true-listp (cddddr x)) (len (cdr (cddddr x))) (true-listp (cdr (cddddr x)))))))
(defthm equal-list6
  (implies (and (true-listp x) (equal (len x) 6))
           (equal (equal x (list a b c d e g))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d)
                       (equal (car (cddddr x)) e) (equal (cadr (cddddr x)) g))))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x)) (len (cddddr x))
                            (len (cdr (cddddr x))) (len (cddr (cddddr x)))
                            (true-listp x) (true-listp (cdr x)) (true-listp (cddr x)) (true-listp (cdddr x))
                            (true-listp (cddddr x)) (true-listp (cdr (cddddr x))) (true-listp (cddr (cddddr x)))))))

(defthm items-follow
  (implies (and (fgs :items y) (sfollow-ok :items r)) (follow-ok :expr (append (fys :items y) r)))
  :hints (("Goal" :cases ((consp y)))))

; what follows a prefix's type-spec: more prefix, or what follows the prefix
(defthm prefix-first-not-paren
  (implies (and (fgs :prefix y) (consp y)) (not (equal (car (fys :prefix y)) '(:op "("))))
  :hints (("Goal" :expand ((fgs :prefix y) (fys :prefix y)) :in-theory (enable fgs fys))))
(defthm prefix-follow
  (implies (and (fgs :prefix y) (sfollow-ok :prefix r)) (sfollow-ok :ts (append (fys :prefix y) r)))
  :hints (("Goal" :cases ((consp y)) :in-theory (enable sfollow-ok scont-tok-p))))

(defun top-expand-hint (id term)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :primes) 0) `(:expand (,term))))

(defun complete-yield (nt x)          ; the spelling, in the canonical forms
  (declare (xargs :mode :program))
  (case nt ((:names :names1) `(names-y ,x)) (:onames `(onames-y ,x)) (:shapes `(fys :shapes* ,x)) (otherwise `(fys ,nt ,x))))
(defun complete-hyp (nt x)
  (declare (xargs :mode :program))
  (case nt ((:names :onames) `(names-p ,x)) (:names1 `(and (consp ,x) (names-p ,x)))
    (:shapes `(and (consp ,x) (shapes-same ,x (shape-kind (car ,x))) (fgs :shapes* ,x)))
    (otherwise `(fgs ,nt ,x))))

(defmacro fps-complete-at (nt)
  (let ((top `(fps ,nt (binary-append ,(complete-yield nt 'x) r))))
    `(defthm ,(packn (list 'fps-complete- nt))
       (implies (and ,(complete-hyp nt 'x) (sfollow-ok ,nt r))
                (equal ,top (mv t x r)))
       :hints (("Goal" ,@(if (member-eq nt '(:shapes* :names1 :onames :attrs :ents :items :prefix :ranges))
                              '(:induct (len x)) nil)
                :expand (,top) :in-theory (enable member-equal))
               (top-expand-hint id ',top)))))

(fps-complete-at :init)
(fps-complete-at :ts)
(fps-complete-at :shape)
(fps-complete-at :shapes*)
(fps-complete-at :range)
(fps-complete-at :ranges)
(fps-complete-at :shapes)
(fps-complete-at :names1)
(fps-complete-at :names)
(fps-complete-at :onames)
(fps-complete-at :items)
(fps-complete-at :ctl)
(fps-complete-at :attr)
(fps-complete-at :attrs)
(fps-complete-at :ent)
(fps-complete-at :ents)
(fps-complete-at :decl-rest)
(fps-complete-at :prefix)
(fps-complete-at :fn-rest)
(fps-complete-at :sub-rest)

; a declaration's rest begins with no prefix-spec: ",", ":" or a name
(defthm name-tok-not-prefix
  (implies (name-tok-p tk) (and (not (tok-in tk *prefix-kws*)) (not (tok-in tk *type-kws*))
                                (not (tok-in tk '("function" "subroutine"))) (not (tok-in tk *simple-kinds*))))
  :hints (("Goal" :in-theory (enable name-tok-p tok-in member-equal))))
(defthm decl-rest-follow
  (implies (fgs :decl-rest d)
           (and (sfollow-ok :prefix (append (fys :decl-rest d) r))
                (consp (fys :decl-rest d))
                (not (equal (car (fys :decl-rest d)) '(:name "function")))
                (not (equal (car (fys :decl-rest d)) '(:name "subroutine")))))
  :hints (("Goal" :expand ((fgs :decl-rest d) (fys :decl-rest d) (fys :attrs (car d)))
           :in-theory (enable sfollow-ok scont-tok-p tok-in))))

; a declaration's type-spec, read as a prefix: the prefix of that one spec
(defthm fps-complete-prefix-ts
  (implies (and (fgs :ts ts) (sfollow-ok :prefix r))
           (equal (fps :prefix (append (fys :ts ts) r)) (mv t (list (list :ts ts)) r)))
  :hints (("Goal" :use ((:instance fps-complete-prefix (x (list (list :ts ts)))))
           :in-theory (disable fps-complete-prefix fps-open))))

; a function's and a subroutine's rest begin with their keyword
(defthm rest-first
  (and (implies (fgs :fn-rest x) (and (consp (fys :fn-rest x)) (equal (car (fys :fn-rest x)) '(:name "function"))))
       (implies (fgs :sub-rest x) (and (consp (fys :sub-rest x)) (equal (car (fys :sub-rest x)) '(:name "subroutine")))))
  :hints (("Goal" :expand ((fgs :fn-rest x) (fys :fn-rest x) (fgs :sub-rest x) (fys :sub-rest x)))))

; the statement kind a first token announces
(defthm stmt-nt-facts
  (and (implies (name-tok-p tk) (equal (stmt-nt tk) :s-assign))
       (implies (fgs :ts ts) (equal (stmt-nt (car (fys :ts ts))) :s-unit))
       (implies (and (fgs :prefix p) (consp (fys :prefix p))) (equal (stmt-nt (car (fys :prefix p))) :s-unit)))
  :hints (("Goal" :expand ((fgs :ts ts) (fys :ts ts) (fgs :prefix p) (fys :prefix p) (fgs :ts (cadr (car p))) (fys :ts (cadr (car p))))
           :in-theory (enable name-tok-p tok-in member-equal))))

(in-theory (disable tok-in stmt-nt))

; the statements, kind by kind: a statement is whole, nothing follows it
(defmacro fps-complete-kind (k)
  (let ((top '(fps :stmt (binary-append (fys :stmt x) r))))
    `(defthm ,(packn (list 'fps-complete-stmt- k))
       (implies (and (fgs :stmt x) (equal (car x) ,k) (atom r))
                (equal ,top (mv t x r)))
       :hints (("Goal" :expand (,top) :in-theory (enable member-equal))))))

(fps-complete-kind :program)
(fps-complete-kind :module)
(fps-complete-kind :end)
(fps-complete-kind :contains)
(fps-complete-kind :implicit-none)
(fps-complete-kind :else)
(fps-complete-kind :use)
(fps-complete-kind :decl)
(fps-complete-kind :assign)
(fps-complete-kind :if-then)
(fps-complete-kind :else-if)
(fps-complete-kind :do)
(fps-complete-kind :simple)
(fps-complete-kind :call)
(fps-complete-kind :print)
(fps-complete-kind :function)
(fps-complete-kind :subroutine)
(fps-complete-kind :if)
(fps-complete-kind :select)
(fps-complete-kind :case)
(fps-complete-kind :case-default)

(defun kind-cases (ks) (declare (xargs :mode :program))
  (if (endp ks) nil (cons `(equal (car x) ,(car ks)) (kind-cases (cdr ks)))))

; fps-complete: a statement's tokens are read back as that statement
(make-event
 `(defthm fps-complete
    (implies (and (fgs :stmt x) (atom r))
             (equal (fps :stmt (append (fys :stmt x) r)) (mv t x r)))
    :hints (("Goal" :cases ,(kind-cases '(:program :module :end :contains :implicit-none :else :use :decl :assign
                                          :if-then :else-if :do :simple :call :print :function :subroutine :if
                                          :select :case :case-default))
             :in-theory (enable member-equal))
            ("Subgoal 1" :expand ((fgs :stmt x))))))

; ---- cost: fps-steps counts fps's calls, each fp call counted by fp-steps
;      (generated: bb mksteps.bb fstmt.lisp fps fps-steps fp)
(encapsulate () (local (in-theory (enable stmt-nt tok-in)))
(defun
 fps-steps
 (nt toks)
 (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fps-rank nt)) :verify-guards nil))
 (let
  ((tk (kar toks)))
  (if
   (atom toks)
   (if (member-eq nt ' (:attrs :onames :items :ctl :prefix :init)) (+ 1) (+ 1))
   (case
    nt
    (:stmt (let ((c1 (fps-steps (stmt-nt tk) toks))) (+ 1 c1)))
    (:s-head
     (if (and (or (equal tk (kw "program")) (equal tk (kw "module"))) (name-tok-p (kadr toks))) (+ 1) (+ 1)))
    (:s-end
     (if
      (not (equal tk (kw "end")))
      (+ 1)
      (if
       (tok-in (kadr toks) *end-kinds*)
       (if (and (tok-in (kadr toks) *unit-ends*) (name-tok-p (kaddr toks))) (+ 1) (+ 1))
       (+ 1))))
    (:s-other
     (cond
      ((equal tk (kw "contains")) (+ 1))
      ((and (equal tk (kw "implicit")) (equal (kadr toks) (kw "none"))) (+ 1))
      ((tok-in tk *simple-kinds*) (+ 1))
      (t (+ 1))))
    (:s-use
     (if
      (not (equal tk (kw "use")))
      (+ 1)
      (let*
       ((t1 (kdr toks))
        (nat
         (cond
          ((and (equal (kar t1) (op ":")) (equal (kadr t1) (op ":"))) :dc)
          ((and
            (equal (kar t1) (op ","))
            (tok-in (kadr t1) ' ("intrinsic" "non_intrinsic"))
            (equal (kaddr t1) (op ":"))
            (equal (kadddr t1) (op ":")))
           (kadr (kadr t1)))
          (t nil)))
        (t2 (cond ((eq nat :dc) (kdr (kdr t1))) (nat (kdr (kdr (kdr (kdr t1))))) (t t1))))
       (cond
        ((not (name-tok-p (kar t2))) (+ 1))
        ((and (equal (kadr t2) (op ",")) (equal (kaddr t2) (kw "only")) (equal (kadddr t2) (op ":")))
         (mv-let
          (ok ns r)
          (fps :onames (kdr (kdr (kdr (kdr t2)))))
          (declare (ignorable ok ns r))
          (let ((c2 (fps-steps :onames (kdr (kdr (kdr (kdr t2))))))) (if ok (+ 1 c2) (+ 1 c2)))))
        (t (+ 1))))))
    (:s-else
     (if
      (not (equal tk (kw "else")))
      (+ 1)
      (if
       (and (equal (kadr toks) (kw "if")) (equal (kaddr toks) (op "(")))
       (mv-let
        (ok e r)
        (fp :expr (kdr (kdr (kdr toks))))
        (declare (ignorable ok e r))
        (let
         ((c3 (fp-steps :expr (kdr (kdr (kdr toks))))))
         (if (and ok (equal (kar r) (op ")")) (equal (kadr r) (kw "then"))) (+ 1 c3) (+ 1 c3))))
       (+ 1))))
    (:s-if
     (if
      (and (equal tk (kw "if")) (equal (kadr toks) (op "(")))
      (mv-let
       (ok e r)
       (fp :expr (kdr (kdr toks)))
       (declare (ignorable ok e r))
       (let
        ((c4 (fp-steps :expr (kdr (kdr toks)))))
        (cond
         ((not (and ok (equal (kar r) (op ")")))) (+ 1 c4))
         ((and (equal (kadr r) (kw "then")) (atom (kdr (kdr r)))) (+ 1 c4))
         ((not (< (len (kdr r)) (len toks))) (+ 1 c4))
         (t
          (mv-let
           (ok2 s r2)
           (fps :stmt (kdr r))
           (declare (ignorable ok2 s r2))
           (let
            ((c5 (fps-steps :stmt (kdr r))))
            (if (and ok2 (action-kind-p (kar s))) (+ 1 c5 c4) (+ 1 c5 c4))))))))
      (+ 1)))
    (:s-do
     (if
      (not (equal tk (kw "do")))
      (+ 1)
      (mv-let
       (ok c r)
       (fps :ctl (kdr toks))
       (declare (ignorable ok c r))
       (let ((c6 (fps-steps :ctl (kdr toks)))) (if ok (+ 1 c6) (+ 1 c6))))))
    (:s-call
     (cond
      ((not (and (equal tk (kw "call")) (name-tok-p (kadr toks)))) (+ 1))
      ((equal (kaddr toks) (op "("))
       (mv-let
        (ok as r)
        (fp :args (kdr (kdr (kdr toks))))
        (declare (ignorable ok as r))
        (let ((c7 (fp-steps :args (kdr (kdr (kdr toks)))))) (if ok (+ 1 c7) (+ 1 c7)))))
      (t (+ 1))))
    (:s-print
     (if
      (and (equal tk (kw "print")) (equal (kadr toks) (op "*")))
      (mv-let
       (ok is r)
       (fps :items (kdr (kdr toks)))
       (declare (ignorable ok is r))
       (let ((c8 (fps-steps :items (kdr (kdr toks))))) (if ok (+ 1 c8) (+ 1 c8))))
      (+ 1)))
    (:s-assign
     (if
      (not (name-tok-p tk))
      (+ 1)
      (if
       (equal (kadr toks) (op "("))
       (mv-let
        (ok as r)
        (fp :args (kdr (kdr toks)))
        (declare (ignorable ok as r))
        (let
         ((c9 (fp-steps :args (kdr (kdr toks)))))
         (if
          (and ok (no-kw-args as) (equal (kar r) (op "=")))
          (mv-let
           (ok2 e r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 e r2))
           (let ((c10 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c10 c9) (+ 1 c10 c9))))
          (+ 1 c9))))
       (if
        (equal (kadr toks) (op "="))
        (mv-let
         (ok e r)
         (fp :expr (kdr (kdr toks)))
         (declare (ignorable ok e r))
         (let ((c11 (fp-steps :expr (kdr (kdr toks))))) (if ok (+ 1 c11) (+ 1 c11))))
        (+ 1)))))
    (:s-select
     (if
      (and (equal tk (kw "select")) (equal (kadr toks) (kw "case")) (equal (kaddr toks) (op "(")))
      (mv-let
       (ok e r)
       (fp :expr (kdr (kdr (kdr toks))))
       (declare (ignorable ok e r))
       (let
        ((c12 (fp-steps :expr (kdr (kdr (kdr toks))))))
        (if (and ok (equal (kar r) (op ")"))) (+ 1 c12) (+ 1 c12))))
      (+ 1)))
    (:s-case
     (cond
      ((not (equal tk (kw "case"))) (+ 1))
      ((equal (kadr toks) (kw "default")) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok rs r)
        (fps :ranges (kdr (kdr toks)))
        (declare (ignorable ok rs r))
        (let ((c13 (fps-steps :ranges (kdr (kdr toks))))) (if ok (+ 1 c13) (+ 1 c13)))))
      (t (+ 1))))
    (:ranges
     (mv-let
      (ok s r)
      (fps :range toks)
      (declare (ignorable ok s r))
      (let
       ((c14 (fps-steps :range toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c14))
        ((equal (kar r) (op ")")) (+ 1 c14))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :ranges (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c15 (fps-steps :ranges (kdr r)))) (if ok2 (+ 1 c15 c14) (+ 1 c15 c14)))))
        (t (+ 1 c14))))))
    (:range
     (if
      (equal tk (op ":"))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let ((c16 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c16) (+ 1 c16))))
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c17 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c17))
         ((not (equal (kar r) (op ":"))) (+ 1 c17))
         ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (+ 1 c17))
         (t
          (mv-let
           (ok2 b r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 b r2))
           (let ((c18 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c18 c17) (+ 1 c18 c17))))))))))
    (:s-unit
     (mv-let
      (ok pre r)
      (fps :prefix toks)
      (declare (ignorable ok pre r))
      (let
       ((c19 (fps-steps :prefix toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c19))
        ((equal (kar r) (kw "function"))
         (mv-let
          (ok2 fr r2)
          (fps :fn-rest r)
          (declare (ignorable ok2 fr r2))
          (let ((c20 (fps-steps :fn-rest r))) (if ok2 (+ 1 c20 c19) (+ 1 c20 c19)))))
        ((equal (kar r) (kw "subroutine"))
         (if
          (assoc-eq :ts pre)
          (+ 1 c19)
          (mv-let
           (ok2 sr r2)
           (fps :sub-rest r)
           (declare (ignorable ok2 sr r2))
           (let ((c21 (fps-steps :sub-rest r))) (if ok2 (+ 1 c21 c19) (+ 1 c21 c19))))))
        ((and (consp pre) (null (cdr pre)) (eq (kar (car pre)) :ts))
         (mv-let
          (ok2 dr r2)
          (fps :decl-rest r)
          (declare (ignorable ok2 dr r2))
          (let ((c22 (fps-steps :decl-rest r))) (if ok2 (+ 1 c22 c19) (+ 1 c22 c19)))))
        (t (+ 1 c19))))))
    (:fn-rest
     (if
      (and (equal tk (kw "function")) (name-tok-p (kadr toks)) (equal (kaddr toks) (op "(")))
      (mv-let
       (ok ds r)
       (fps :names (kdr (kdr (kdr toks))))
       (declare (ignorable ok ds r))
       (let
        ((c23 (fps-steps :names (kdr (kdr (kdr toks))))))
        (cond
         ((not ok) (+ 1 c23))
         ((and
           (equal (kar r) (kw "result"))
           (equal (kadr r) (op "("))
           (name-tok-p (kaddr r))
           (equal (kadddr r) (op ")")))
          (+ 1 c23))
         (t (+ 1 c23)))))
      (+ 1)))
    (:sub-rest
     (cond
      ((not (and (equal tk (kw "subroutine")) (name-tok-p (kadr toks)))) (+ 1))
      ((equal (kaddr toks) (op "("))
       (mv-let
        (ok ds r)
        (fps :names (kdr (kdr (kdr toks))))
        (declare (ignorable ok ds r))
        (let ((c24 (fps-steps :names (kdr (kdr (kdr toks)))))) (if ok (+ 1 c24) (+ 1 c24)))))
      (t (+ 1))))
    (:decl-rest
     (mv-let
      (ok as r)
      (fps :attrs toks)
      (declare (ignorable ok as r))
      (let
       ((c25 (fps-steps :attrs toks)))
       (if
        (not (and ok (<= (len r) (len toks))))
        (+ 1 c25)
        (let*
         ((dc (and (equal (kar r) (op ":")) (equal (kadr r) (op ":")))) (r1 (if dc (kdr (kdr r)) r)))
         (mv-let
          (ok2 es r2)
          (fps :ents r1)
          (declare (ignorable ok2 es r2))
          (let
           ((c26 (fps-steps :ents r1)))
           (if
            (and ok2 (consp es) (implies (or (consp as) (ents-init-p es)) dc))
            (+ 1 c26 c25)
            (+ 1 c26 c25)))))))))
    (:ts
     (cond
      ((not (tok-in tk *type-kws*)) (+ 1))
      ((equal (kadr toks) (op "("))
       (let*
        ((kwp (and (equal (kaddr toks) (kw "kind")) (kw-head-p (kdr (kdr toks)))))
         (t1 (if kwp (kdr (kdr (kdr (kdr toks)))) (kdr (kdr toks)))))
        (mv-let
         (ok e r)
         (fp :expr t1)
         (declare (ignorable ok e r))
         (let ((c27 (fp-steps :expr t1))) (if (and ok (equal (kar r) (op ")"))) (+ 1 c27) (+ 1 c27))))))
      (t (+ 1))))
    (:attrs
     (if
      (equal tk (op ","))
      (mv-let
       (ok a r)
       (fps :attr (kdr toks))
       (declare (ignorable ok a r))
       (let
        ((c28 (fps-steps :attr (kdr toks))))
        (if
         (not (and ok (<= (len r) (len (kdr toks)))))
         (+ 1 c28)
         (mv-let
          (ok2 as r2)
          (fps :attrs r)
          (declare (ignorable ok2 as r2))
          (let ((c29 (fps-steps :attrs r))) (if ok2 (+ 1 c29 c28) (+ 1 c29 c28)))))))
      (+ 1)))
    (:attr
     (cond
      ((equal tk (kw "parameter")) (+ 1))
      ((equal tk (kw "value")) (+ 1))
      ((and (equal tk (kw "intent")) (equal (kadr toks) (op "(")))
       (cond
        ((and
          (equal (kaddr toks) (kw "in"))
          (equal (kadddr toks) (kw "out"))
          (equal (kar (kdr (kdr (kdr (kdr toks))))) (op ")")))
         (+ 1))
        ((and (tok-in (kaddr toks) ' ("in" "out" "inout")) (equal (kadddr toks) (op ")"))) (+ 1))
        (t (+ 1))))
      ((and (equal tk (kw "dimension")) (equal (kadr toks) (op "(")))
       (mv-let
        (ok ss r)
        (fps :shapes (kdr (kdr toks)))
        (declare (ignorable ok ss r))
        (let ((c30 (fps-steps :shapes (kdr (kdr toks))))) (if ok (+ 1 c30) (+ 1 c30)))))
      (t (+ 1))))
    (:shapes
     (mv-let
      (ok ss r)
      (fps :shapes* toks)
      (declare (ignorable ok ss r))
      (let
       ((c31 (fps-steps :shapes* toks)))
       (if (and ok (consp ss) (shapes-same ss (shape-kind (car ss)))) (+ 1 c31) (+ 1 c31)))))
    (:shapes*
     (mv-let
      (ok s r)
      (fps :shape toks)
      (declare (ignorable ok s r))
      (let
       ((c32 (fps-steps :shape toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c32))
        ((equal (kar r) (op ")")) (+ 1 c32))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :shapes* (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c33 (fps-steps :shapes* (kdr r)))) (if ok2 (+ 1 c33 c32) (+ 1 c33 c32)))))
        (t (+ 1 c32))))))
    (:shape
     (if
      (equal tk (op ":"))
      (+ 1)
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c34 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c34))
         ((not (equal (kar r) (op ":"))) (+ 1 c34))
         ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (+ 1 c34))
         (t
          (mv-let
           (ok2 hi r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 hi r2))
           (let ((c35 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c35 c34) (+ 1 c35 c34))))))))))
    (:ents
     (mv-let
      (ok e r)
      (fps :ent toks)
      (declare (ignorable ok e r))
      (let
       ((c36 (fps-steps :ent toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c36))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 es r2)
          (fps :ents (kdr r))
          (declare (ignorable ok2 es r2))
          (let ((c37 (fps-steps :ents (kdr r)))) (if ok2 (+ 1 c37 c36) (+ 1 c37 c36)))))
        (t (+ 1 c36))))))
    (:ent
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok ss r)
        (fps :shapes (kdr (kdr toks)))
        (declare (ignorable ok ss r))
        (let
         ((c38 (fps-steps :shapes (kdr (kdr toks)))))
         (if
          (not (and ok (<= (len r) (len toks))))
          (+ 1 c38)
          (mv-let
           (ok2 i r2)
           (fps :init r)
           (declare (ignorable ok2 i r2))
           (let ((c39 (fps-steps :init r))) (if ok2 (+ 1 c39 c38) (+ 1 c39 c38))))))))
      (t
       (mv-let
        (ok2 i r2)
        (fps :init (kdr toks))
        (declare (ignorable ok2 i r2))
        (let ((c40 (fps-steps :init (kdr toks)))) (if ok2 (+ 1 c40) (+ 1 c40)))))))
    (:init
     (if
      (equal tk (op "="))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let ((c41 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c41) (+ 1 c41))))
      (+ 1)))
    (:names (if (equal tk (op ")")) (+ 1) (let ((c42 (fps-steps :names1 toks))) (+ 1 c42))))
    (:names1
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op ")")) (+ 1))
      ((equal (kadr toks) (op ","))
       (mv-let
        (ok ns r)
        (fps :names1 (kdr (kdr toks)))
        (declare (ignorable ok ns r))
        (let ((c43 (fps-steps :names1 (kdr (kdr toks))))) (if ok (+ 1 c43) (+ 1 c43)))))
      (t (+ 1))))
    (:onames
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op ","))
       (mv-let
        (ok ns r)
        (fps :onames (kdr (kdr toks)))
        (declare (ignorable ok ns r))
        (let ((c44 (fps-steps :onames (kdr (kdr toks))))) (if (and ok (consp ns)) (+ 1 c44) (+ 1 c44)))))
      (t (+ 1))))
    (:items
     (if
      (equal tk (op ","))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let
        ((c45 (fp-steps :expr (kdr toks))))
        (if
         (not (and ok (< (len r) (len toks))))
         (+ 1 c45)
         (mv-let
          (ok2 es r2)
          (fps :items r)
          (declare (ignorable ok2 es r2))
          (let ((c46 (fps-steps :items r))) (if ok2 (+ 1 c46 c45) (+ 1 c46 c45)))))))
      (+ 1)))
    (:ctl
     (if
      (atom toks)
      (+ 1)
      (let*
       ((c (equal tk (op ","))) (t1 (if c (kdr toks) toks)))
       (cond
        ((and (equal (kar t1) (kw "while")) (equal (kadr t1) (op "(")))
         (mv-let
          (ok e r)
          (fp :expr (kdr (kdr t1)))
          (declare (ignorable ok e r))
          (let
           ((c47 (fp-steps :expr (kdr (kdr t1)))))
           (if (and ok (equal (kar r) (op ")"))) (+ 1 c47) (+ 1 c47)))))
        ((and (name-tok-p (kar t1)) (equal (kadr t1) (op "=")))
         (mv-let
          (ok e1 r)
          (fp :expr (kdr (kdr t1)))
          (declare (ignorable ok e1 r))
          (let
           ((c48 (fp-steps :expr (kdr (kdr t1)))))
           (if
            (not (and ok (equal (kar r) (op ","))))
            (+ 1 c48)
            (mv-let
             (ok2 e2 r2)
             (fp :expr (kdr r))
             (declare (ignorable ok2 e2 r2))
             (let
              ((c49 (fp-steps :expr (kdr r))))
              (cond
               ((not ok2) (+ 1 c49 c48))
               ((equal (kar r2) (op ","))
                (mv-let
                 (ok3 e3 r3)
                 (fp :expr (kdr r2))
                 (declare (ignorable ok3 e3 r3))
                 (let ((c50 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c50 c49 c48) (+ 1 c50 c49 c48)))))
               (t (+ 1 c49 c48)))))))))
        (t (+ 1))))))
    (:prefix
     (cond
      ((tok-in tk *prefix-kws*)
       (mv-let
        (ok ps r)
        (fps :prefix (kdr toks))
        (declare (ignorable ok ps r))
        (let ((c51 (fps-steps :prefix (kdr toks)))) (if ok (+ 1 c51) (+ 1 c51)))))
      ((tok-in tk *type-kws*)
       (mv-let
        (ok ts r)
        (fps :ts toks)
        (declare (ignorable ok ts r))
        (let
         ((c52 (fps-steps :ts toks)))
         (if
          (not (and ok (< (len r) (len toks))))
          (+ 1 c52)
          (mv-let
           (ok2 ps r2)
           (fps :prefix r)
           (declare (ignorable ok2 ps r2))
           (let ((c53 (fps-steps :prefix r))) (if ok2 (+ 1 c53 c52) (+ 1 c53 c52))))))))
      (t (+ 1))))
    (otherwise (+ 1)))))))

(defthm fps-steps-natp (natp (fps-steps nt toks)) :rule-classes :type-prescription)

(defthm fp-cost-linear
  (implies (mv-nth 0 (fp nt toks))
           (<= (+ (fp-steps nt toks) (* 32 (len (mv-nth 2 (fp nt toks)))))
               (+ (* 32 (len toks)) (fp-d nt))))
  :rule-classes ((:linear :trigger-terms ((fp-steps nt toks)))) :hints (("Goal" :by fp-cost)))

(defthm len-cdr-consp (implies (consp x) (equal (len (cdr x)) (+ -1 (len x)))))

; the constant each nt adds; a type-spec always reads its keyword, so it
; may owe less than nothing
(defun fps-d (nt)
  (declare (xargs :guard t))
  (case nt (:stmt 48) (:s-unit 40) (:decl-rest 32) (:shapes 48) (:shapes* 40) (:shape 32) (:ents 16)
    (:init 16) (:ent 8) (:attrs 8) (:names 8) (:ranges 40) (:range 32) (:ts -63) (otherwise 4)))

(defun fps-cost-hint (id clause)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :pool-lst) (quote (1)))
       (equal (len (access clause-id id :case-lst)) 1)
       (equal (access clause-id id :primes) 0)
       (let ((cs (case-nts clause)))
         (list :expand (append (quote ((fps nt toks) (fps-steps nt toks)))
                               (loop$ for c in cs append (list (list (quote fps) c (quote toks)) (list (quote fps-steps) c (quote toks)))))))))

(defthm stmt-nt-is-s
  (implies (not (member-equal c (quote (:s-head :s-end :s-other :s-use :s-else :s-if :s-do :s-call :s-print :s-assign :s-unit :s-select :s-case))))
           (not (equal (stmt-nt tk) c)))
  :hints (("Goal" :in-theory (enable stmt-nt))))

; a successful statement parse makes at most 64 calls per token it consumes,
; plus fps-d nt
(defthm fps-cost
  (implies (mv-nth 0 (fps nt toks))
           (<= (+ (fps-steps nt toks) (* 64 (len (mv-nth 2 (fps nt toks)))))
               (+ (* 64 (len toks)) (fps-d nt))))
  :hints (("Goal" :induct (fps-steps nt toks) :in-theory (enable member-equal)) (fps-cost-hint id clause)))
