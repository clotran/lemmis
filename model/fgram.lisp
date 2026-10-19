; fgram: the concrete grammar of Lemmis's Fortran subset (Stage A, item 1),
; over the tokens flex.lisp makes, each production citing its rule in
; J3/24-007 (Fortran 2023). A grammar here is a recognizer of parse trees,
; fg, and the tokens a tree spells, fy: a token list is in the language of
; nonterminal nt when some tree x has (fg nt x) and (fy nt x) equal to it.
; fparse.lisp's parser is proved to accept exactly that language, and to
; answer the one tree that spells it.
;
; The standard writes its left-associative levels left-recursively
; (R1006, R1007, R1016-R1018: [ x op ] y); a tree here holds the first
; operand and the list of (op operand) after it, the same strings, with
; the left association kept by the meaning's fold.
;
; Tokens (flex.lisp):
;   (:name s)        a name (R603), lower case; never one of *fkeywords*
;   (:int d k)       int-literal-constant (R708): digits d, kind-param k
;                    (R709) nil or a string
;   (:log b k)       logical-literal-constant (R725), b t or nil
;   (:char s)        char-literal-constant (R724), s its characters
;   (:op s)          an operator or punctuation, s from *fops*
;
; Subset restriction: Fortran has no reserved words, so a name may spell
; a keyword ("if = 1" is an assignment). In the subset a name is never one
; of *fkeywords*, the words a statement can begin with; with that, each
; statement's kind is known from its first tokens.

(in-package "ACL2")

(include-book "fsyn")   ; fname-p (R603, C601)

(defconst *fkeywords*
  '("program" "end" "module" "contains" "use" "implicit" "integer" "logical" "real"
    "double" "character" "complex" "type" "if" "else" "elseif" "endif" "do" "enddo"
    "select" "case" "cycle" "exit" "return" "stop" "continue" "call" "print"
    "function" "subroutine" "pure" "elemental" "impure" "recursive" "non_recursive"
    "endprogram" "endmodule" "endfunction" "endsubroutine" "endselect" "selectcase"))

(defconst *fops*
  '("+" "-" "*" "/" "**" "==" "/=" "<" "<=" ">" ">=" "(" ")" "," "=" ":" "::" "[" "]" "%"
    ".eq." ".ne." ".lt." ".le." ".gt." ".ge." ".not." ".and." ".or." ".eqv." ".neqv."))

(defun op (s) (declare (xargs :guard t)) (list :op s))

; ---- tokens

(defun digits-p (cs)
  (declare (xargs :guard t))
  (if (atom cs) (null cs)
    (and (characterp (car cs)) (digit-char-p (car cs)) (digits-p (cdr cs)))))

(defun digit-string-p (s)          ; R711
  (declare (xargs :guard t))
  (and (stringp s) (consp (coerce s 'list)) (digits-p (coerce s 'list))))

(defun kind-param-p (k)            ; R709: digit-string or scalar-int-constant-name
  (declare (xargs :guard t))
  (or (null k) (digit-string-p k) (fname-p k)))

(defun name-tok-p (x)              ; R603, and the subset's restriction
  (declare (xargs :guard t))
  (and (true-listp x) (= (len x) 2) (eq (car x) :name) (fname-p (cadr x))
       (not (member-equal (cadr x) *fkeywords*))))

(defun lit-tok-p (x)               ; R708, R725, R724
  (declare (xargs :guard t))
  (and (true-listp x)
       (case (car x)
         (:int (and (= (len x) 3) (digit-string-p (cadr x)) (kind-param-p (caddr x))))
         (:log (and (= (len x) 3) (booleanp (cadr x)) (kind-param-p (caddr x))))
         (:char (and (= (len x) 2) (stringp (cadr x))))
         (otherwise nil))))

(defconst *eqv-ops* (list (op ".eqv.") (op ".neqv.")))                 ; R1022
(defconst *or-ops* (list (op ".or.")))                                ; R1021
(defconst *and-ops* (list (op ".and.")))                              ; R1020
(defconst *rel-ops* (list (op "==") (op "/=") (op "<") (op "<=") (op ">") (op ">=")
                          (op ".eq.") (op ".ne.") (op ".lt.") (op ".le.") (op ".gt.") (op ".ge.")))  ; R1014
(defconst *add-ops* (list (op "+") (op "-")))                         ; R1010
(defconst *mult-ops* (list (op "*") (op "/")))                        ; R1009

; the operators of each left-associative level, and the level of its operands
(defun lev-ops (nt)
  (declare (xargs :guard t))
  (case nt
    ((:expr :expr*) *eqv-ops*) ((:equiv :equiv*) *or-ops*) ((:or :or*) *and-ops*)
    ((:l2 :l2*) *add-ops*) (otherwise *mult-ops*)))
(defun lev-sub (nt)
  (declare (xargs :guard t))
  (case nt ((:expr :expr*) :equiv) ((:equiv :equiv*) :or) ((:or :or*) :and)
    ((:l2 :l2*) :add) (otherwise :mult)))
(defun lev-rest (nt)
  (declare (xargs :guard t))
  (case nt (:expr :expr*) (:equiv :equiv*) (:or :or*) (:l2 :l2*) (otherwise :add*)))

; ---- the expression grammar
;
;  :expr   (first rest)         R1023 expr (no defined-binary-op), R1018
;                               level-5-expr: equiv-operand {equiv-op equiv-operand}
;  :equiv  (first rest)         R1017 equiv-operand: or-operand {or-op or-operand}
;  :or     (first rest)         R1016 or-operand: and-operand {and-op and-operand}
;  :expr* :equiv* :or* :l2* :add*   the ((op operand) ...) after the first
;  :and    (notp l4)            R1015 and-operand: [not-op] level-4-expr, R1019
;  :l4     (a op b)             R1013 level-4-expr: [level-3-expr rel-op]
;                               level-3-expr; op, b nil when absent. R1011
;                               level-3-expr is level-2-expr here: the subset
;                               has no concat-op (no character expressions)
;  :l2     (sign first rest)    R1007 level-2-expr: [add-op] add-operand
;                               {add-op add-operand}; sign nil or + -
;  :add    (first rest)         R1006 add-operand: mult-operand {mult-op mult-operand}
;  :mult   (prim pow)           R1005 mult-operand: level-1-expr [power-op
;                               mult-operand], R1008; R1003 level-1-expr is
;                               primary (no defined-unary-op); pow nil or a :mult
;  :prim   (:lit tok)           R1001 literal-constant (R605)
;          (:name tok)          R1001 designator, R901 object-name
;          (:ref tok args)      name ( [list] ): R912 part-ref (an array
;                               element or section, R917, R918) or R1520
;                               function-reference -- one form in the text,
;                               told apart by the declarations
;          (:paren e)           R1001 ( expr )
;          (:acons es)          R777 array-constructor: lbracket ac-spec rbracket
;                               (R779, R780), R778 ac-spec: ac-value-list, R781
;                               ac-value: expr
;  :args   (arg ...)            ( [section-subscript-list | actual-arg-spec-list] ),
;                               the ")" included; :args* the same after a ","
;  :arg    (:kw tok e)          R1523 actual-arg-spec: keyword = actual-arg (R516)
;          (:sub e)             R921 section-subscript: subscript (R919), or
;                               R1524 actual-arg: expr
;          (:tri lo hi st)      R922 subscript-triplet: [subscript] : [subscript]
;                               [: stride] (R924); each nil when absent
;  :tri*   (hi st)              what follows the triplet's first ":"
;  :elist  (e ...)              ac-value-list, the "]" included; :elist* after a ","

(defun fg-measure (nt x)
  (declare (xargs :guard t))
  (+ (* 2 (acl2-count x)) (if (member-eq nt '(:args :elist)) 1 0)))

(defun fg (nt x)
  (declare (xargs :guard t :measure (fg-measure nt x)))
  (case nt
    ((:expr :equiv :or :add)
     (and (true-listp x) (= (len x) 2)
          (fg (lev-sub nt) (car x)) (fg (lev-rest nt) (cadr x))))
    ((:expr* :equiv* :or* :l2* :add*)
     (if (atom x) (null x)
       (and (true-listp (car x)) (= (len (car x)) 2)
            (member-equal (caar x) (lev-ops nt))
            (fg (lev-sub nt) (cadar x))
            (fg nt (cdr x)))))
    (:and (and (true-listp x) (= (len x) 2) (booleanp (car x)) (fg :l4 (cadr x))))
    (:l4 (and (true-listp x) (= (len x) 3) (fg :l2 (car x))
              (if (cadr x)
                  (and (member-equal (cadr x) *rel-ops*) (fg :l2 (caddr x)))
                (null (caddr x)))))
    (:l2 (and (true-listp x) (= (len x) 3)
              (or (null (car x)) (member-equal (car x) *add-ops*))
              (fg :add (cadr x)) (fg :l2* (caddr x))))
    (:mult (and (true-listp x) (= (len x) 2) (fg :prim (car x))
                (or (null (cadr x)) (fg :mult (cadr x)))))
    (:prim (and (true-listp x)
                (case (car x)
                  (:lit (and (= (len x) 2) (lit-tok-p (cadr x))))
                  (:name (and (= (len x) 2) (name-tok-p (cadr x))))
                  (:ref (and (= (len x) 3) (name-tok-p (cadr x)) (fg :args (caddr x))))
                  (:paren (and (= (len x) 2) (fg :expr (cadr x))))
                  (:acons (and (= (len x) 2) (consp (cadr x)) (fg :elist (cadr x))))
                  (otherwise nil))))
    ((:args :args*)
     (if (atom x) (null x) (and (fg :arg (car x)) (fg :args* (cdr x)))))
    (:arg (and (true-listp x)
               (case (car x)
                 (:kw (and (= (len x) 3) (name-tok-p (cadr x)) (fg :expr (caddr x))))
                 (:sub (and (= (len x) 2) (fg :expr (cadr x))))
                 (:tri (and (= (len x) 4)
                            (or (null (cadr x)) (fg :expr (cadr x)))
                            (fg :tri* (cddr x))))
                 (otherwise nil))))
    (:tri* (and (true-listp x) (= (len x) 2)
                (or (null (car x)) (fg :expr (car x)))
                (or (null (cadr x)) (fg :expr (cadr x)))))
    ((:elist :elist*)
     (if (atom x) (and (eq nt :elist*) (null x))
       (and (fg :expr (car x)) (fg :elist* (cdr x)))))
    (otherwise nil)))

(defthm acl2-count-kar
  (and (<= (acl2-count (kar x)) (acl2-count x))
       (implies (consp x) (< (acl2-count (kar x)) (acl2-count x))))
  :rule-classes :linear)
(defthm acl2-count-kdr
  (and (<= (acl2-count (kdr x)) (acl2-count x))
       (implies (consp x) (< (acl2-count (kdr x)) (acl2-count x))))
  :rule-classes :linear)

; the tokens a tree spells
(defun fy (nt x)
  (declare (xargs :guard t :measure (fg-measure nt x)))
  (if (atom x)
      (case nt ((:args :args*) (list (op ")"))) ((:elist :elist*) (list (op "]"))) (otherwise nil))
  (case nt
    ((:expr :equiv :or :add)
     (append (fy (lev-sub nt) (kar x)) (fy (lev-rest nt) (kadr x))))
    ((:expr* :equiv* :or* :l2* :add*)
     (if (atom x) nil
       (cons (kar (car x)) (append (fy (lev-sub nt) (kadr (car x))) (fy nt (cdr x))))))
    (:and (if (kar x) (cons (op ".not.") (fy :l4 (kadr x))) (fy :l4 (kadr x))))
    (:l4 (append (fy :l2 (kar x)) (if (kadr x) (cons (kadr x) (fy :l2 (kaddr x))) nil)))
    (:l2 (append (if (kar x) (list (kar x)) nil) (fy :add (kadr x)) (fy :l2* (kaddr x))))
    (:mult (append (fy :prim (kar x)) (if (kadr x) (cons (op "**") (fy :mult (kadr x))) nil)))
    (:prim (case (kar x)
             ((:lit :name) (list (kadr x)))
             (:ref (list* (kadr x) (op "(") (fy :args (kaddr x))))
             (:paren (cons (op "(") (append (fy :expr (kadr x)) (list (op ")")))))
             (otherwise (cons (op "[") (fy :elist (kadr x))))))
    (:args (if (atom x) (list (op ")")) (append (fy :arg (car x)) (fy :args* (cdr x)))))
    (:args* (if (atom x) (list (op ")")) (cons (op ",") (append (fy :arg (car x)) (fy :args* (cdr x))))))
    (:arg (case (kar x)
            (:kw (list* (kadr x) (op "=") (fy :expr (kaddr x))))
            (:sub (fy :expr (kadr x)))
            (otherwise
             (append (if (kadr x) (fy :expr (kadr x)) nil) (cons (op ":") (fy :tri* (kdr (kdr x))))))))
    (:tri* (append (if (kar x) (fy :expr (kar x)) nil) (if (kadr x) (cons (op ":") (fy :expr (kadr x))) nil)))
    (:elist (if (atom x) (list (op "]")) (append (fy :expr (car x)) (fy :elist* (cdr x)))))
    (:elist* (if (atom x) (list (op "]")) (cons (op ",") (append (fy :expr (car x)) (fy :elist* (cdr x))))))
    (otherwise nil))))

; ---- what may follow a complete nt
;
; The parser of nt, having read a whole tree, may still look at the next
; token: tk continues nt when some decision on nt's right edge would take
; it (an operator of a level, "(" after a name, "**", a triplet's ":").
; The completeness theorem holds for a tree followed by any token that
; does not continue it; every place the grammar puts an expression ends it
; with one (")" "," "]" or the statement's end). "=" never follows an
; expression in the grammar; counting it a continuer keeps a keyword
; argument k = e from being read as the expression k.

(defun start-tok-p (tk)            ; a token that can begin an expression
  (declare (xargs :guard t))
  (or (name-tok-p tk) (lit-tok-p tk)
      (and (member-equal tk (list (op "(") (op "[") (op "+") (op "-") (op ".not."))) t)))

(defun cont-tok-p (nt tk)
  (declare (xargs :guard t))
  (let* ((p (or (equal tk (op "(")) (equal tk (op "="))))
         (m (or p (equal tk (op "**"))))
         (a (or m (member-equal tk *mult-ops*)))
         (l2 (or a (member-equal tk *add-ops*)))
         (l4 (or l2 (member-equal tk *rel-ops*)))
         (o (or l4 (member-equal tk *and-ops*)))
         (q (or o (member-equal tk *or-ops*)))
         (e (or q (member-equal tk *eqv-ops*))))
    (and (case nt
           (:prim p) (:mult m) ((:add :add*) a) ((:l2 :l2*) l2) ((:l4 :and) l4)
           ((:or :or*) o) ((:equiv :equiv*) q) ((:expr :expr*) e)
           ; an argument, and a triplet's tail, are ended by "," or ")" only
           ((:arg :tri*) (not (member-equal tk (list (op ",") (op ")")))))
           (otherwise nil))
         t)))

(defun follow-ok (nt r)
  (declare (xargs :guard t))
  (or (atom r) (not (cont-tok-p nt (car r)))))
