; fstmt-base: the tokens and predicates fstmt.lisp's statement grammar is
; written with: keywords, labels (R611), formats (R1215), the I/O control
; list's constraints (C1210, C1211, C1218, C1223), input items (R1216).

(in-package "ACL2")

(include-book "fparse-cost")

(defun kw (s) (declare (xargs :guard t)) (list :name s))

(defconst *end-kinds* '("program" "module" "function" "subroutine" "do" "if" "select" "type"))
(defconst *unit-ends* '("program" "module" "function" "subroutine" "type"))
(defconst *simple-kinds* '("cycle" "exit" "return" "continue" "stop"))
(defconst *prefix-kws* '("pure" "elemental" "impure" "recursive" "non_recursive"))
(defconst *type-kws* '("integer" "logical" "real" "character" "double"))
; R723 char-length's int-literal-constant, CHARACTER * n (no kind-param: C730)
(defun len-tok-p (x)
  (declare (xargs :guard t))
  (and (true-listp x) (= (len x) 3) (eq (car x) :int) (digit-string-p (cadr x)) (null (caddr x))))
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

; R910 substring-range [e] : [e], read as an argument (:tri lo hi nil)
(defun substr-rng-p (g) (declare (xargs :guard t)) (and (fg :arg g) (eq (kar g) :tri) (null (kadddr g))))

; R722's "*" char-length "," (C724, C725: in a type-declaration-stmt with
; no "::"), the ts ("character" (:len tk :comma)); the subset tells it from
; an attr-spec's "," by the word after it, never an attr-spec's keyword
(defconst *attr-kws* '("parameter" "value" "intent" "dimension"))
(defun attr-kw-tok-p (tk) (declare (xargs :guard t)) (and (eq (kar tk) :name) (member-equal (kadr tk) *attr-kws*) t))
(defun ts-comma-p (ts)
  (declare (xargs :guard t))
  (and (true-listp ts) (= (len ts) 2) (equal (car ts) "character") (true-listp (cadr ts)) (= (len (cadr ts)) 3)
       (eq (car (cadr ts)) :len) (len-tok-p (cadr (cadr ts))) (eq (caddr (cadr ts)) :comma)))

(defun action-kind-p (k)          ; R515, C1143
  (declare (xargs :guard t))
  (and (member-eq k '(:assign :cassign :simple :call :print :goto :write :read :readf)) t))

(defun nonzero-digit-p (cs)
  (declare (xargs :guard t))
  (and (consp cs) (or (and (characterp (car cs)) (digit-char-p (car cs)) (not (eql (car cs) #\0)) t) (nonzero-digit-p (cdr cs)))))
(defun label-digits-p (d)         ; R611: one to five digits, one of them not zero (C613)
  (declare (xargs :guard t))
  (and (digit-string-p d) (<= (len (coerce d 'list)) 5) (nonzero-digit-p (coerce d 'list))))
(defun label-int-p (tk)           ; a label written as a number (GO TO 10)
  (declare (xargs :guard t))
  (and (true-listp tk) (= (len tk) 3) (eq (car tk) :int) (label-digits-p (cadr tk)) (null (caddr tk))))
(defun label-tok-p (tk)           ; a statement's label, as the lexers write it
  (declare (xargs :guard t))
  (and (true-listp tk) (= (len tk) 2) (eq (car tk) :lab) (label-digits-p (cadr tk))))
(defun fmt-tok-p (tk) (declare (xargs :guard t)) (and (true-listp tk) (= (len tk) 2) (eq (car tk) :fmt) (stringp (cadr tk))))
(defun lab-int (d) (declare (xargs :guard t)) (list :int d nil))
(defun char-tok-p (tk) (declare (xargs :guard t)) (and (true-listp tk) (= (len tk) 2) (eq (car tk) :char) (stringp (cadr tk))))
; R1215 format: * (:star), a label (its digits), a character literal (its token)
(defun fmt-spec-p (f) (declare (xargs :guard t)) (or (eq f :star) (label-digits-p f) (char-tok-p f)))
(defun fmt-tok (f) (declare (xargs :guard t)) (cond ((eq f :star) (op "*")) ((stringp f) (lab-int f)) (t f)))
(defun fmt-head-p (tk) (declare (xargs :guard t)) (or (equal tk (op "*")) (label-int-p tk) (char-tok-p tk)))
(defun fmt-of (tk) (declare (xargs :guard t)) (cond ((equal tk (op "*")) :star) ((label-int-p tk) (cadr tk)) (t tk)))
(defun unit-pos-p (c) (declare (xargs :guard t)) (and (eq (kar c) :unit) (null (kadr c))))
(defun fmt-pos-p (c)                 ; the format written without FMT=
  (declare (xargs :guard t))
  (and (true-listp c) (= (len c) 3) (eq (car c) :fmt) (null (cadr c)) (fmt-spec-p (caddr c))))
(defun ios-count (k cs) (declare (xargs :guard t)) (if (atom cs) 0 (+ (if (equal (kar (car cs)) k) 1 0) (ios-count k (cdr cs)))))
(defun ios-fmt (cs) (declare (xargs :guard t)) (if (atom cs) nil (if (eq (kar (car cs)) :fmt) (kaddr (car cs)) (ios-fmt (cdr cs)))))
(defun ios-ok (cs)                   ; C1210, C1211, C1223; one format
  (declare (xargs :guard t))
  (and (equal (ios-count :unit cs) 1) (equal (ios-count :fmt cs) 1) (<= (ios-count :adv cs) 1)
       (or (equal (ios-count :adv cs) 0) (not (eq (ios-fmt cs) :star)))))
; an expression tree that is a lone name or a lone name(args), and nothing
; else: a designator, an input item (R1216)
(defun lone-prim (e)                 ; the :prim tree, or nil
  (declare (xargs :guard t))
  (let* ((eq1 (kar e)) (or1 (kar eq1)) (and1 (kar or1)) (l4 (kadr and1)) (l3 (kar l4)) (l2 (kar l3)) (add (kadr l2))
         (mult (kar add)) (prim (kar mult)))
    (and (null (kadr e)) (null (kadr eq1)) (null (kadr or1)) (null (kar and1))
         (null (kadr l4)) (null (kadr l3)) (null (kar l2)) (null (kaddr l2)) (null (kadr add)) (null (kadr mult))
         (member-eq (kar prim) '(:name :ref :sref)) prim)))
(defun all-lone (es) (declare (xargs :guard t)) (if (atom es) t (and (lone-prim (car es)) (all-lone (cdr es)))))
; the three labels of an arithmetic IF after its ( expr ), and the statement's end
(defun aif-labs-p (r)
  (declare (xargs :guard t))
  (and (label-int-p (kar r)) (equal (kadr r) (op ",")) (label-int-p (kaddr r)) (equal (kadddr r) (op ","))
       (label-int-p (kar (kdr (kdr (kdr (kdr r))))))))

(defun ents-init-p (ents)
  (declare (xargs :guard t))
  (if (atom ents) nil (or (and (consp (car ents)) (kaddr (car ents)) t) (ents-init-p (cdr ents)))))
