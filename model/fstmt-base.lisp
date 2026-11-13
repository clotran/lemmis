; fstmt-base: the tokens and predicates fstmt.lisp's statement grammar is
; written with: keywords, labels (R611), formats (R1215), the I/O control
; list's constraints (C1210, C1211, C1218, C1223), input items (R1216).

(in-package "ACL2")

(include-book "fparse-cost")

(defun kw (s) (declare (xargs :guard t)) (list :name s))

(defconst *end-kinds* '("program" "module" "function" "subroutine" "do" "if" "select" "type" "block"))
(defconst *unit-ends* '("program" "module" "function" "subroutine" "type"))
(defconst *simple-kinds* '("cycle" "exit" "return" "continue" "stop"))
(defconst *prefix-kws* '("pure" "elemental" "impure" "recursive" "non_recursive"))
(defconst *type-kws* '("integer" "logical" "real" "character" "double" "complex"))
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
(defconst *attr-kws* '("parameter" "value" "intent" "dimension" "save" "allocatable"))
(defun attr-kw-tok-p (tk) (declare (xargs :guard t)) (and (eq (kar tk) :name) (member-equal (kadr tk) *attr-kws*) t))
(defun ts-comma-p (ts)
  (declare (xargs :guard t))
  (and (true-listp ts) (= (len ts) 2) (equal (car ts) "character") (true-listp (cadr ts)) (= (len (cadr ts)) 3)
       (eq (car (cadr ts)) :len) (len-tok-p (cadr (cadr ts))) (eq (caddr (cadr ts)) :comma)))

(defun action-kind-p (k)          ; R515, C1143
  (declare (xargs :guard t))
  (and (member-eq k '(:assign :cassign :simple :stop :call :print :goto :write :read :readf :allocate :deallocate)) t))

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
; R935 allocate-shape-spec, [lower-bound-expr :] upper-bound-expr: read as a
; subscript (:sub e) or a triplet (:tri lo hi nil) with both bounds
(defun alloc-spec-p (a) (declare (xargs :guard t)) (or (eq (kar a) :sub) (and (eq (kar a) :tri) (kadr a) (kaddr a) (null (kadddr a)) t)))
(defun alloc-specs-p (as) (declare (xargs :guard t)) (if (atom as) t (and (alloc-spec-p (car as)) (alloc-specs-p (cdr as)))))
; an ALLOCATE's actual (R933 allocation): name ( allocate-shape-spec-list );
; a DEALLOCATE's: a name (R934 allocate-object: a variable-name)
(defun alloc-obj-p (a d)
  (declare (xargs :guard t))
  (let ((p (and (eq (kar a) :sub) (lone-prim (kadr a)))))
    (if d (eq (kar p) :name) (and (eq (kar p) :ref) (consp (kaddr p)) (alloc-specs-p (kaddr p))))))
(defun alloc-objs-p (as d) (declare (xargs :guard t)) (if (atom as) (null as) (and (alloc-obj-p (car as) d) (alloc-objs-p (cdr as) d))))
; the three labels of an arithmetic IF after its ( expr ), and the statement's end
(defun aif-labs-p (r)
  (declare (xargs :guard t))
  (and (label-int-p (kar r)) (equal (kadr r) (op ",")) (label-int-p (kaddr r)) (equal (kadddr r) (op ","))
       (label-int-p (kar (kdr (kdr (kdr (kdr r))))))))

(defun ents-init-p (ents)
  (declare (xargs :guard t))
  (if (atom ents) nil (or (and (consp (car ents)) (kaddr (car ents)) t) (ents-init-p (cdr ents)))))

; R866 implicit-stmt IMPLICIT implicit-spec-list (R867 implicit-spec:
; declaration-type-spec ( letter-spec-list ), R868 letter-spec: letter [-
; letter]), read by a parser of its own: a spec (ts ls), ts a type-spec
; without a kind-selector (INTEGER, REAL, LOGICAL, COMPLEX, DOUBLE PRECISION,
; CHARACTER [* char-length]), ls the letter-specs, each (a b), b nil or the
; range's last letter
(defun let-tok-p (tk) (declare (xargs :guard t)) (and (name-tok-p tk) (stringp (kadr tk)) (equal (length (kadr tk)) 1)))
(defthm let-tok-p-name (implies (let-tok-p tk) (and (consp tk) (equal (car tk) :name))) :rule-classes :forward-chaining)
(in-theory (disable let-tok-p))
(defun imp-ts-p (ts)
  (declare (xargs :guard t))
  (or (equal ts '("double" nil))
      (and (true-listp ts) (= (len ts) 2) (member-equal (car ts) '("integer" "real" "logical" "complex" "character"))
           (or (null (cadr ts))
               (and (equal (car ts) "character") (true-listp (cadr ts)) (= (len (cadr ts)) 2)
                    (eq (car (cadr ts)) :len) (len-tok-p (cadr (cadr ts))))))))
(defun imp-ts-y (ts)
  (declare (xargs :guard t))
  (cons (kw (kar ts)) (cond ((equal (kar ts) "double") (list (kw "precision"))) ((kadr ts) (list (op "*") (kadr (kadr ts)))) (t nil))))
(defun lets-p (ls)
  (declare (xargs :guard t))
  (and (consp ls) (true-listp (car ls)) (= (len (car ls)) 2) (let-tok-p (car (car ls)))
       (or (null (cadr (car ls))) (let-tok-p (cadr (car ls))))
       (if (consp (cdr ls)) (lets-p (cdr ls)) (null (cdr ls)))))
(defun lets-y (ls)
  (declare (xargs :guard t))
  (if (atom ls) nil
    (append (cons (kar (car ls)) (if (kadr (car ls)) (list (op "-") (kadr (car ls))) nil))
            (if (consp (cdr ls)) (cons (op ",") (lets-y (cdr ls))) (list (op ")"))))))
(defun imps-p (ss)
  (declare (xargs :guard t))
  (and (consp ss) (true-listp (car ss)) (= (len (car ss)) 2) (imp-ts-p (car (car ss))) (lets-p (cadr (car ss)))
       (if (consp (cdr ss)) (imps-p (cdr ss)) (null (cdr ss)))))
(defun imps-y (ss)
  (declare (xargs :guard t))
  (if (atom ss) nil
    (append (imp-ts-y (kar (car ss))) (cons (op "(") (lets-y (kadr (car ss))))
            (if (consp (cdr ss)) (cons (op ",") (imps-y (cdr ss))) nil))))

(defun imp-ts (toks)                 ; (mv ts rest), ts nil when none
  (declare (xargs :guard t))
  (cond ((equal (kar toks) (kw "double"))
         (if (equal (kadr toks) (kw "precision")) (mv (list "double" nil) (kdr (kdr toks))) (mv nil nil)))
        ((and (equal (kar toks) (kw "character")) (equal (kadr toks) (op "*")) (len-tok-p (kaddr toks)))
         (mv (list "character" (list :len (kaddr toks))) (kdr (kdr (kdr toks)))))
        ((member-equal (kar toks) (list (kw "integer") (kw "real") (kw "logical") (kw "complex") (kw "character")))
         (mv (list (kadr (kar toks)) nil) (kdr toks)))
        (t (mv nil nil))))
(defun imp-lets (toks)               ; (mv ok ls rest): letter-spec-list )
  (declare (xargs :guard t :measure (len toks)))
  (if (not (and (consp toks) (let-tok-p (car toks)))) (mv nil nil nil)
    (let* ((rng (and (equal (kadr toks) (op "-")) (let-tok-p (kaddr toks))))
           (l (list (car toks) (if rng (kaddr toks) nil)))
           (r (if rng (kdr (kdr (kdr toks))) (cdr toks))))
      (cond ((equal (kar r) (op ")")) (mv t (list l) (kdr r)))
            ((equal (kar r) (op ","))
             (mv-let (ok ls r2) (imp-lets (kdr r)) (if ok (mv t (cons l ls) r2) (mv nil nil nil))))
            (t (mv nil nil nil))))))
(defthm imp-lets-len
  (and (<= (len (mv-nth 2 (imp-lets toks))) (len toks))
       (implies (mv-nth 0 (imp-lets toks)) (< (len (mv-nth 2 (imp-lets toks))) (len toks))))
  :rule-classes :linear)
(defthm len-cdr-lt (implies (consp x) (< (len (cdr x)) (len x))) :rule-classes :linear)
(defthm imp-ts-len
  (implies (car (imp-ts toks)) (< (len (mv-nth 1 (imp-ts toks))) (len toks)))
  :rule-classes :linear)
(defthm imp-ts-sound
  (implies (car (imp-ts toks))
           (and (imp-ts-p (car (imp-ts toks))) (equal (append (imp-ts-y (car (imp-ts toks))) (mv-nth 1 (imp-ts toks))) toks)))
  :hints (("Goal" :in-theory (enable len-tok-p member-equal))))
(defthm imp-ts-complete
  (implies (and (imp-ts-p ts) (not (equal (car r) (quote (:op "*"))))) (equal (imp-ts (append (imp-ts-y ts) r)) (mv ts r)))
  :hints (("Goal" :in-theory (enable len-tok-p member-equal))))
(defthm imp-ts-y-consp (and (consp (imp-ts-y ts)) (implies (imp-ts-p ts) (not (equal (car (imp-ts-y ts)) (quote (:name "none"))))))
  :hints (("Goal" :in-theory (enable imp-ts-p))))
(in-theory (disable imp-ts imp-ts-p imp-ts-y))
(defun imp-specs (toks)              ; (mv ok ss rest)
  (declare (xargs :guard t :measure (len toks)))
  (mv-let (ts r) (imp-ts toks)
    (if (not (and ts (equal (kar r) (op "(")))) (mv nil nil nil)
      (mv-let (ok ls r2) (imp-lets (kdr r))
        (cond ((not ok) (mv nil nil nil))
              ((equal (kar r2) (op ","))
               (mv-let (ok2 ss r3) (imp-specs (kdr r2)) (if ok2 (mv t (cons (list ts ls) ss) r3) (mv nil nil nil))))
              (t (mv t (list (list ts ls)) r2)))))))

(defthm imp-specs-len
  (<= (len (mv-nth 2 (imp-specs toks))) (len toks))
  :rule-classes :linear :hints (("Goal" :induct (imp-specs toks))))
(defthm imp-lets-sound
  (implies (mv-nth 0 (imp-lets toks))
           (and (lets-p (mv-nth 1 (imp-lets toks)))
                (equal (append (lets-y (mv-nth 1 (imp-lets toks))) (mv-nth 2 (imp-lets toks))) toks))))
(defthm imp-lets-complete
  (implies (lets-p x) (equal (imp-lets (append (lets-y x) r)) (mv t x r)))
  :hints (("Goal" :induct (lets-p x))))
(in-theory (disable imp-lets lets-p lets-y))
(defthm imp-specs-sound
  (implies (mv-nth 0 (imp-specs toks))
           (and (imps-p (mv-nth 1 (imp-specs toks)))
                (equal (append (imps-y (mv-nth 1 (imp-specs toks))) (mv-nth 2 (imp-specs toks))) toks)))
  :hints (("Goal" :induct (imp-specs toks))))
(defthm imp-specs-complete
  (implies (and (imps-p x) (not (equal (kar r) (op ","))))
           (equal (imp-specs (append (imps-y x) r)) (mv t x r)))
  :hints (("Goal" :induct (imps-p x))))
(defthm imps-y-first                  ; never IMPLICIT NONE
  (implies (imps-p x) (and (consp (imps-y x)) (not (equal (car (imps-y x)) (quote (:name "none"))))))
  :hints (("Goal" :expand ((imps-y x) (imps-p x)))))
(in-theory (disable imp-specs imps-y imps-p))
