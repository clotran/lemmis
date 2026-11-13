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
;   (:real m l e k)  real-literal-constant (R714): significand text m,
;                    exponent letter l ("e" "d" nil), exponent text e, kind k
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
    "endprogram" "endmodule" "endfunction" "endsubroutine" "endselect" "selectcase" "go" "goto" "write" "format" "read" "doubleprecision" "save" "allocate" "deallocate" "block" "endblock" "dimension" "data" "parameter"))

(defconst *fops*
  '("+" "-" "*" "/" "**" "==" "/=" "<" "<=" ">" ">=" "(" ")" "," "=" ":" "::" "[" "]" "%" "//"
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

; R714 real-literal-constant: a significand of digits and at most one ".",
; a digit among them; without the ".", an exponent; E or D and a
; signed-digit-string (R716, R717); with a kind, the letter E (C721)
(defun sig-chars-p (cs dot)
  (declare (xargs :guard t))
  (if (atom cs) (null cs)
    (and (or (and (characterp (car cs)) (digit-char-p (car cs))) (and (eql (car cs) #\.) (not dot)))
         (sig-chars-p (cdr cs) (or dot (eql (car cs) #\.))))))
(defun some-digit-p (cs)
  (declare (xargs :guard t))
  (and (consp cs) (or (and (characterp (car cs)) (digit-char-p (car cs)) t) (some-digit-p (cdr cs)))))
(defun signed-digit-string-p (s)
  (declare (xargs :guard t))
  (and (stringp s)
       (let ((cs (coerce s 'list)))
         (if (and (consp cs) (member (car cs) '(#\+ #\-))) (and (consp (cdr cs)) (digits-p (cdr cs))) (and (consp cs) (digits-p cs))))))
(defun real-tok-p (x)
  (declare (xargs :guard t))
  (and (true-listp x) (= (len x) 5) (eq (car x) :real) (stringp (cadr x))
       (let ((cs (coerce (cadr x) 'list)) (l (caddr x)) (e (cadddr x)) (k (car (cddddr x))))
         (and (sig-chars-p cs nil) (some-digit-p cs)
              (or (member #\. cs) l)
              (if l (and (member-equal l '("e" "d")) (signed-digit-string-p e)) (null e))
              (kind-param-p k)
              (not (and k (equal l "d")))
              t))))

(defthm real-tok-car (implies (real-tok-p x) (equal (car x) :real)) :rule-classes :forward-chaining)
(in-theory (disable real-tok-p))

; a name in an expression: also REAL, the intrinsic function (16.9.170)
; whose name is a type keyword -- "real (" never begins a statement's
; expression, so the statement kinds stay told apart by their first token
(defun xname-tok-p (x)
  (declare (xargs :guard t))
  (or (name-tok-p x) (equal x '(:name "real"))))

(defun lit-tok-p (x)               ; R708, R714, R725, R724
  (declare (xargs :guard t))
  (and (true-listp x)
       (case (car x)
         (:int (and (= (len x) 3) (digit-string-p (cadr x)) (kind-param-p (caddr x))))
         (:log (and (= (len x) 3) (booleanp (cadr x)) (kind-param-p (caddr x))))
         (:char (and (= (len x) 2) (stringp (cadr x))))
         (:real (real-tok-p x))
         (otherwise nil))))

(defconst *eqv-ops* (list (op ".eqv.") (op ".neqv.")))                 ; R1022
(defconst *or-ops* (list (op ".or.")))                                ; R1021
(defconst *and-ops* (list (op ".and.")))                              ; R1020
(defconst *rel-ops* (list (op "==") (op "/=") (op "<") (op "<=") (op ">") (op ">=")
                          (op ".eq.") (op ".ne.") (op ".lt.") (op ".le.") (op ".gt.") (op ".ge.")))  ; R1014
(defconst *concat-ops* (list (op "//")))                              ; R1012
(defconst *add-ops* (list (op "+") (op "-")))                         ; R1010
(defconst *mult-ops* (list (op "*") (op "/")))                        ; R1009

; the operators of each left-associative level, and the level of its operands
(defun lev-ops (nt)
  (declare (xargs :guard t))
  (case nt
    ((:expr :expr*) *eqv-ops*) ((:equiv :equiv*) *or-ops*) ((:or :or*) *and-ops*)
    ((:l3 :l3*) *concat-ops*) ((:l2 :l2*) *add-ops*) (otherwise *mult-ops*)))
(defun lev-sub (nt)
  (declare (xargs :guard t))
  (case nt ((:expr :expr*) :equiv) ((:equiv :equiv*) :or) ((:or :or*) :and)
    ((:l3 :l3*) :l2) ((:l2 :l2*) :add) (otherwise :mult)))
(defun lev-rest (nt)
  (declare (xargs :guard t))
  (case nt (:expr :expr*) (:equiv :equiv*) (:or :or*) (:l3 :l3*) (:l2 :l2*) (otherwise :add*)))

; ---- the expression grammar
;
;  :expr   (first rest)         R1023 expr (no defined-binary-op), R1018
;                               level-5-expr: equiv-operand {equiv-op equiv-operand}
;  :equiv  (first rest)         R1017 equiv-operand: or-operand {or-op or-operand}
;  :or     (first rest)         R1016 or-operand: and-operand {and-op and-operand}
;  :expr* :equiv* :or* :l3* :l2* :add*   the ((op operand) ...) after the first
;  :and    (notp l4)            R1015 and-operand: [not-op] level-4-expr, R1019
;  :l4     (a op b)             R1013 level-4-expr: [level-3-expr rel-op]
;                               level-3-expr; op, b nil when absent
;  :l3     (first rest)         R1011 level-3-expr: level-2-expr {concat-op
;                               level-2-expr}, R1012 concat-op //
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
;          (:sref tok args rng) R908 substring: parent-string ( substring-range ),
;                               R909 parent-string an array-element (a
;                               scalar-variable-name's substring is a :ref of
;                               one triplet), R910 substring-range: [e] : [e],
;                               rng an :arg (:tri lo hi nil)
;          (:dref b parts)      R911 data-ref: part-ref {% part-ref} (R912), a
;                               structure component (R913) or an element of
;                               one: b the first part-ref, a :name or :ref
;                               tree, then the :parts
;          (:paren e)           R1001 ( expr )
;          (:cplx re im)        R718 complex-literal-constant: ( real-part ,
;                               imag-part ), R719, R720 each a signed int- or
;                               real-literal-constant, an :expr tree (cpart-p)
;          (:acons es)          R777 array-constructor: lbracket ac-spec rbracket
;                               (R779, R780), R778 ac-spec: ac-value-list
;  :args   (arg ...)            ( [section-subscript-list | actual-arg-spec-list] ),
;                               the ")" included; :args* the same after a ","
;  :arg    (:kw tok e)          R1523 actual-arg-spec: keyword = actual-arg (R516)
;          (:sub e)             R921 section-subscript: subscript (R919), or
;                               R1524 actual-arg: expr
;          (:tri lo hi st)      R922 subscript-triplet: [subscript] : [subscript]
;                               [: stride] (R924); each nil when absent
;  :tri*   (hi st)              what follows the triplet's first ":"
;  :base                        the :name, :ref and :sref trees, read on their own
;  :parts  (part ...) nonempty  each a :part, % name [( args )]
;  :part   (tok refp args)      % tok, then ( args ) when refp
;  :elist  (v ...)              ac-value-list, the "]" included; :elist* after a ","
;  :acv    (:e e) | (:ido . il) R781 ac-value: expr (not beginning with "(": the
;                               subset's), or R782 ac-implied-do: ( il ), il an :ilist
;  :ilist  (v . il*)            R782's ac-value-list , ac-implied-do-control (R783):
;                               an ac-value, then the :ilist* after it
;  :ilist* (v . il*) | (:ctl var lo hi st)   ", ac-value" and more, or the
;                               control ", [integer-type-spec ::] var = lo , hi [, st] )":
;                               R783 ac-implied-do-control, R784 ac-do-variable;
;                               var a name, or (:int name sel) after INTEGER
;                               [( [KIND =] k )] ::, sel nil or (kw k) as R706
;  :ictl   (lo hi st)           "lo , hi [, st] )", st nil when absent

;  R719 real-part, R720 imag-part: [sign] int- or real-literal-constant
;  (no named constant), read as the expression it spells: the :expr tree
;  of one level-2-expr whose add-operand is the literal alone
(defun cpart-p (e)
  (declare (xargs :guard t))
  (let* ((l2 (kar (kar (kadr (kar (kar (kar e)))))))
         (sign (kar l2))
         (tk (kadr (kar (kar (kadr l2))))))
    (and (or (null sign) (member-equal sign *add-ops*))
         (member-eq (kar tk) '(:int :real)) (lit-tok-p tk)
         (equal e (list (list (list (list nil (list (list (list sign (list (list (list :lit tk) nil) nil) nil) nil) nil nil)) nil) nil) nil)))))

(defun fg-measure (nt x)
  (declare (xargs :guard t))
  (+ (* 2 (acl2-count x)) (if (member-eq nt '(:args :elist :prim)) 1 0)))

; the tokens a tree spells
(defun fy (nt x)
  (declare (xargs :guard t :measure (fg-measure nt x)))
  (if (atom x)
      (case nt ((:args :args*) (list (op ")"))) ((:elist :elist*) (list (op "]"))) (otherwise nil))
  (case nt
    ((:expr :equiv :or :l3 :add)
     (append (fy (lev-sub nt) (kar x)) (fy (lev-rest nt) (kadr x))))
    ((:expr* :equiv* :or* :l3* :l2* :add*)
     (if (atom x) nil
       (cons (kar (car x)) (append (fy (lev-sub nt) (kadr (car x))) (fy nt (cdr x))))))
    (:and (if (kar x) (cons (op ".not.") (fy :l4 (kadr x))) (fy :l4 (kadr x))))
    (:l4 (append (fy :l3 (kar x)) (if (kadr x) (cons (kadr x) (fy :l3 (kaddr x))) nil)))
    (:l2 (append (if (kar x) (list (kar x)) nil) (fy :add (kadr x)) (fy :l2* (kaddr x))))
    (:mult (append (fy :prim (kar x)) (if (kadr x) (cons (op "**") (fy :mult (kadr x))) nil)))
    (:prim (case (kar x)
             (:lit (list (kadr x)))
             ((:name :ref :sref) (fy :base x))
             (:dref (append (fy :base (kadr x)) (fy :parts (kaddr x))))
             (:paren (cons (op "(") (append (fy :expr (kadr x)) (list (op ")")))))
             (:cplx (cons (op "(") (append (fy :expr (kadr x)) (cons (op ",") (append (fy :expr (kaddr x)) (list (op ")")))))))
             (otherwise (cons (op "[") (fy :elist (kadr x))))))
    (:base (case (kar x)
             (:name (list (kadr x)))
             (:ref (list* (kadr x) (op "(") (fy :args (kaddr x))))
             (otherwise (list* (kadr x) (op "(") (append (fy :args (kaddr x)) (cons (op "(") (append (fy :arg (kadddr x)) (list (op ")")))))))))
    (:parts (append (fy :part (car x)) (fy :parts (cdr x))))
    (:part (list* (op "%") (car x) (if (kadr x) (cons (op "(") (fy :args (kaddr x))) nil)))
    (:args (if (atom x) (list (op ")")) (append (fy :arg (car x)) (fy :args* (cdr x)))))
    (:args* (if (atom x) (list (op ")")) (cons (op ",") (append (fy :arg (car x)) (fy :args* (cdr x))))))
    (:arg (case (kar x)
            (:kw (list* (kadr x) (op "=") (fy :expr (kaddr x))))
            (:sub (fy :expr (kadr x)))
            (otherwise
             (append (if (kadr x) (fy :expr (kadr x)) nil) (cons (op ":") (fy :tri* (kdr (kdr x))))))))
    (:tri* (append (if (kar x) (fy :expr (kar x)) nil) (if (kadr x) (cons (op ":") (fy :expr (kadr x))) nil)))
    (:elist (if (atom x) (list (op "]")) (append (fy :acv (car x)) (fy :elist* (cdr x)))))
    (:elist* (if (atom x) (list (op "]")) (cons (op ",") (append (fy :acv (car x)) (fy :elist* (cdr x))))))
    (:acv (if (eq (kar x) :ido) (cons (op "(") (fy :ilist (kdr x))) (fy :expr (kadr x))))
    (:ilist (append (fy :acv (kar x)) (fy :ilist* (kdr x))))
    (:ilist* (if (eq (kar x) :ctl)
                 (cons (op ",")
                       (append (if (eq (kar (kadr x)) :int)       ; R783's integer-type-spec ::
                                   (cons '(:name "integer")
                                         (append (if (kaddr (kadr x))
                                                     (cons (op "(") (append (if (kar (kaddr (kadr x))) (list '(:name "kind") (op "=")) nil)
                                                                            (append (fy :expr (kadr (kaddr (kadr x)))) (list (op ")")))))
                                                   nil)
                                                 (list (op ":") (op ":") (kadr (kadr x)))))
                                 (list (kadr x)))
                               (cons (op "=") (fy :ictl (kdr (kdr x))))))
               (cons (op ",") (append (fy :acv (kar x)) (fy :ilist* (kdr x))))))
    (:ictl (append (fy :expr (kar x))
                   (cons (op ",") (append (fy :expr (kadr x))
                                          (if (kaddr x) (cons (op ",") (append (fy :expr (kaddr x)) (list (op ")")))) (list (op ")")))))))
    (otherwise nil))))

(defun fg (nt x)
  (declare (xargs :guard t :measure (fg-measure nt x)))
  (case nt
    ((:expr :equiv :or :l3 :add)
     (and (true-listp x) (= (len x) 2)
          (fg (lev-sub nt) (car x)) (fg (lev-rest nt) (cadr x))))
    ((:expr* :equiv* :or* :l3* :l2* :add*)
     (if (atom x) (null x)
       (and (true-listp (car x)) (= (len (car x)) 2)
            (member-equal (caar x) (lev-ops nt))
            (fg (lev-sub nt) (cadar x))
            (fg nt (cdr x)))))
    (:and (and (true-listp x) (= (len x) 2) (booleanp (car x)) (fg :l4 (cadr x))))
    (:l4 (and (true-listp x) (= (len x) 3) (fg :l3 (car x))
              (if (cadr x)
                  (and (member-equal (cadr x) *rel-ops*) (fg :l3 (caddr x)))
                (null (caddr x)))))
    (:l2 (and (true-listp x) (= (len x) 3)
              (or (null (car x)) (member-equal (car x) *add-ops*))
              (fg :add (cadr x)) (fg :l2* (caddr x))))
    (:mult (and (true-listp x) (= (len x) 2) (fg :prim (car x))
                (or (null (cadr x)) (fg :mult (cadr x)))))
    (:prim (and (true-listp x)
                (case (car x)
                  (:lit (and (= (len x) 2) (lit-tok-p (cadr x))))
                  ((:name :ref :sref) (fg :base x))
                  (:dref (and (= (len x) 3) (member-eq (kar (cadr x)) '(:name :ref)) (fg :base (cadr x))
                              (fg :parts (caddr x))))
                  (:paren (and (= (len x) 2) (fg :expr (cadr x))))
                  (:cplx (and (= (len x) 3) (fg :expr (cadr x)) (fg :expr (caddr x)) (cpart-p (cadr x)) (cpart-p (caddr x))))
                  (:acons (and (= (len x) 2) (consp (cadr x)) (fg :elist (cadr x))))
                  (otherwise nil))))
    (:base (and (true-listp x)
                (case (car x)
                  (:name (and (= (len x) 2) (xname-tok-p (cadr x))))
                  (:ref (and (= (len x) 3) (xname-tok-p (cadr x)) (fg :args (caddr x))))
                  (:sref (and (= (len x) 4) (xname-tok-p (cadr x)) (fg :args (caddr x))
                              (fg :arg (cadddr x)) (eq (kar (cadddr x)) :tri) (null (kadddr (cadddr x)))))
                  (otherwise nil))))
    (:parts (and (consp x) (fg :part (car x)) (or (null (cdr x)) (fg :parts (cdr x)))))
    (:part (and (true-listp x) (= (len x) 3) (xname-tok-p (car x)) (booleanp (cadr x))
                (if (cadr x) (fg :args (caddr x)) (null (caddr x)))))
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
       (and (fg :acv (car x)) (fg :elist* (cdr x)))))
    ; an ac-value: an ac-implied-do, or an expression not beginning with "("
    (:acv (if (eq (kar x) :ido)
              (and (consp (cdr x)) (fg :ilist (cdr x)))
            (and (true-listp x) (= (len x) 2) (eq (car x) :e)
                 (fg :expr (cadr x)) (not (equal (car (fy :expr (cadr x))) (op "("))))))
    (:ilist (and (consp x) (fg :acv (car x)) (fg :ilist* (cdr x))))
    (:ilist* (and (consp x)
                  (if (eq (car x) :ctl)
                      (and (consp (cdr x))
                           (if (eq (kar (cadr x)) :int)
                               (and (true-listp (cadr x)) (= (len (cadr x)) 3) (name-tok-p (cadr (cadr x)))
                                    (or (null (caddr (cadr x)))
                                        (and (true-listp (caddr (cadr x))) (= (len (caddr (cadr x))) 2)
                                             (booleanp (car (caddr (cadr x)))) (fg :expr (cadr (caddr (cadr x)))))))
                             (name-tok-p (cadr x)))
                           (fg :ictl (cddr x)))
                    (and (fg :acv (car x)) (fg :ilist* (cdr x))))))
    (:ictl (and (true-listp x) (= (len x) 3) (fg :expr (car x)) (fg :expr (cadr x))
                (or (null (caddr x)) (fg :expr (caddr x)))))
    (otherwise nil)))

(defthm acl2-count-kar
  (and (<= (acl2-count (kar x)) (acl2-count x))
       (implies (consp x) (< (acl2-count (kar x)) (acl2-count x))))
  :rule-classes :linear)
(defthm acl2-count-kdr
  (and (<= (acl2-count (kdr x)) (acl2-count x))
       (implies (consp x) (< (acl2-count (kdr x)) (acl2-count x))))
  :rule-classes :linear)

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
  (or (xname-tok-p tk) (lit-tok-p tk)
      (and (member-equal tk (list (op "(") (op "[") (op "+") (op "-") (op ".not."))) t)))

(defun cont-tok-p (nt tk)
  (declare (xargs :guard t))
  (let* ((p (or (equal tk (op "(")) (equal tk (op "=")) (equal tk (op "%"))))
         (m (or p (equal tk (op "**"))))
         (a (or m (member-equal tk *mult-ops*)))
         (l2 (or a (member-equal tk *add-ops*)))
         (l3 (or l2 (member-equal tk *concat-ops*)))
         (l4 (or l3 (member-equal tk *rel-ops*)))
         (o (or l4 (member-equal tk *and-ops*)))
         (q (or o (member-equal tk *or-ops*)))
         (e (or q (member-equal tk *eqv-ops*))))
    (and (case nt
           (:prim p) (:mult m)
           ; a base is continued by "(" (its arguments, its substring); the
           ; "%" after it is the primary's, not the base's
           (:base (or (equal tk (op "(")) (equal tk (op "="))))
           ; a component is continued by "(" after its name, a list of them by "%" too
           (:part (equal tk (op "(")))
           (:parts (or (equal tk (op "(")) (equal tk (op "%")))) ((:add :add*) a) ((:l2 :l2*) l2) ((:l3 :l3*) l3) ((:l4 :and) l4)
           ((:or :or*) o) ((:equiv :equiv*) q) ((:expr :expr* :acv) e)
           ; an argument, and a triplet's tail, are ended by "," or ")" only
           ((:arg :tri*) (not (member-equal tk (list (op ",") (op ")")))))
           (otherwise nil))
         t)))

(defun follow-ok (nt r)
  (declare (xargs :guard t))
  (or (atom r) (not (cont-tok-p nt (car r)))))
