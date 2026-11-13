; fstmt-complete: fps-complete, fstmt.lisp's parser complete: every statement
; fgs allows is read back as its own tree (fps-sound is fstmt-sound.lisp's).

(in-package "ACL2")

(include-book "fstmt-sound")
(include-book "fstmt-complete-thy")   ; *fsc-runes*

; the theory of name's runes in *fsc-runes*, else dflt
(defmacro thy-or (name dflt)
  (let ((r (cdr (assoc-eq name *fsc-runes*))))
    (if r `(union-theories ',r (theory 'minimal-theory)) dflt)))

(set-ignore-ok t)

; a label, kept closed: the statements' tokens are read back whole, and a
; label's spelling is only ever checked against the tree's own
; label-digits-p (opened, label-int-p and digit-string-p split every token
; in sight: the subroutine statement's proof ran past the time limit)
(defthm label-int-p-spelled           ; a label as fys spells it
  (equal (label-int-p (list :int d nil)) (label-digits-p d)))
(defthm label-int-p-not-int           ; any other token is not a label
  (implies (not (equal (car tk) :int)) (not (label-int-p tk))))
(in-theory (disable label-digits-p label-int-p))

; ---- fps-complete: every statement is read back as its own tree
;
; As fparse.lisp's fp-complete, bottom up: for each nonterminal, the
; spelling of any of its trees, followed by anything that does not
; continue it (sfollow-ok), is read back as that tree.

(defun scont-tok-p (nt tk)
  (declare (xargs :guard t))
  (case nt
    (:ts (or (equal tk (op "(")) (equal tk (op "*"))))
    (:attrs (equal tk (op ",")))
    ((:shape :range :ix :io) (not (member-equal tk (list (op ",") (op ")")))))   ; a shape or a range is ended by "," or ")" only
    (:init (cont-tok-p :expr tk))
    (:ent (or (cont-tok-p :expr tk) (equal tk (op "(")) (equal tk (op "="))))
    ((:ents :decl-rest) (or (cont-tok-p :expr tk) (equal tk (op "(")) (equal tk (op "=")) (equal tk (op ","))))
    (:prefix (or (tok-in tk *prefix-kws*) (tok-in tk *type-kws*) (equal tk (op "(")) (equal tk (op "*"))))
    (:fn-rest (equal tk (kw "result")))
    (:sub-rest (equal tk (op "(")))
    (:dobj (cont-tok-p :prim tk))
    (:dval (or (equal tk (op "*")) (cont-tok-p :prim tk)))
    ((:shapes :shapes* :names :names1 :ranges :ixs :ios :kios :dobjs :dvals) nil)
    (otherwise t)))                       ; a statement is whole; DO's control ends it

(defun sfollow-ok (nt r)
  (declare (xargs :guard t))
  (if (atom r) (not (member-eq nt '(:shape :range :ix :io))) (not (scont-tok-p nt (car r)))))

(defthm sfollow-facts
  (and (implies (and (atom r) (not (member-eq nt '(:shape :range :ix :io)))) (sfollow-ok nt r))
       (equal (sfollow-ok nt (cons a b)) (not (scont-tok-p nt a)))
       (equal (sfollow-ok nt (append a b)) (if (consp a) (not (scont-tok-p nt (car a))) (sfollow-ok nt b)))
       (implies (member-eq nt '(:shapes :shapes* :names :names1 :ranges :ixs :ios :kios :dobjs :dvals)) (sfollow-ok nt r))
       (implies (sfollow-ok :io r) (and (follow-ok :expr r) (consp r)))
       (implies (and (sfollow-ok :io r) (not (equal (car r) (op ",")))) (equal (car r) (op ")")))
       ; what follows an initialization or a shape follows its expression
       (implies (sfollow-ok :init r) (follow-ok :expr r))
       (implies (sfollow-ok :shape r) (follow-ok :expr r))
       (implies (sfollow-ok :shape r) (consp r))
       (implies (sfollow-ok :range r) (follow-ok :expr r))
       (implies (sfollow-ok :range r) (consp r))
       (implies (sfollow-ok :ix r) (follow-ok :expr r))
       (implies (sfollow-ok :ix r) (consp r))
       (implies (and (sfollow-ok :ix r) (not (equal (car r) (op ",")))) (equal (car r) (op ")")))
       (implies (and (sfollow-ok :range r) (not (equal (car r) (op ",")))) (equal (car r) (op ")")))
       ; PRINT's items, ONLY's names, DO's control, a statement: the statement's end follows
       (implies (and (sfollow-ok nt r) (member-eq nt '(:items :onames :ctl :stmt :oitems))) (atom r))
       (implies (sfollow-ok :oitems r) (and (atom r) (follow-ok :expr r)))
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
                (not (equal (car (fy :expr x)) '(:op ")"))) (not (equal (car (fy :expr x)) '(:op "=")))
                (not (equal (car (fy :expr x)) '(:op "*")))))
  :hints (("Goal" :use ((:instance fy-first-expr)) :in-theory (e/d (start-tok-p) (fy-first-expr)))))
(defthm expr-len-pos                ; the same, as a length: an output item reads a token
  (implies (fg :expr x) (< 0 (len (fy :expr x))))
  :rule-classes :linear
  :hints (("Goal" :use expr-first-not :expand ((len (fy :expr x))) :in-theory (disable expr-first-not fy-first-expr))))

; a statement's I/O parts: a format's token is no other punctuation and
; no name; UNIT=, FMT= and ADVANCE= begin a keyword spec, never an expr
(defthm fmt-tok-not
  (implies (fmt-spec-p f) (and (not (equal (fmt-tok f) '(:op "("))) (not (equal (fmt-tok f) '(:op ",")))
                               (not (equal (fmt-tok f) '(:op ")"))) (not (equal (car (fmt-tok f)) :name))))
  :hints (("Goal" :in-theory (enable fmt-spec-p fmt-tok label-digits-p char-tok-p))))
(defthm fmt-head-not-name (not (fmt-head-p (cons :name x))) :hints (("Goal" :in-theory (enable fmt-head-p char-tok-p label-int-p))))
(defthm kw-head-p-io
  (implies (and (consp toks) (member-equal (car toks) '((:name "unit") (:name "fmt") (:name "advance")))
                (consp (cdr toks)) (equal (cadr toks) '(:op "=")))
           (kw-head-p toks))
  :hints (("Goal" :in-theory (enable kw-head-p name-tok-p member-equal))))

(defthm expr-not-io-kw
  (implies (and (equal (cadr (append (fy :expr e) r)) '(:op "=")) (fg :expr e) (follow-ok :expr r))
           (and (not (equal (car (fy :expr e)) '(:name "unit"))) (not (equal (car (fy :expr e)) '(:name "fmt")))
                (not (equal (car (fy :expr e)) '(:name "advance")))))
  :hints (("Goal" :use ((:instance fp-complete (nt :expr) (x e)) (:instance kw-head-p-io (toks (append (fy :expr e) r))))
           :in-theory (disable fp-complete kw-head-p-io))))

; the parts that may be empty, read back as empty
(defthm fps-empty
  (and (implies (sfollow-ok :init r) (equal (fps :init r) (mv t nil r)))
       (implies (sfollow-ok :attrs r) (equal (fps :attrs r) (mv t nil r)))
       (implies (sfollow-ok :items r) (equal (fps :items r) (mv t nil r)))
       (implies (sfollow-ok :prefix r) (equal (fps :prefix r) (mv t nil r)))
       (implies (sfollow-ok :onames r) (equal (fps :onames r) (mv t nil r)))
       (implies (sfollow-ok :ctl r) (equal (fps :ctl r) (mv t nil r)))
       (implies (sfollow-ok :oitems r) (equal (fps :oitems r) (mv t nil r))))
  :hints (("Goal" :expand ((fps :init r) (fps :attrs r) (fps :items r) (fps :prefix r) (fps :onames r) (fps :ctl r) (fps :oitems r))
           :in-theory (thy-or fps-empty (enable sfollow-ok scont-tok-p cont-tok-p member-equal)))))

; first tokens of the parts' spellings, and their shapes
(defthm fys-ts-first
  (implies (fgs :ts x) (and (consp (fys :ts x)) (tok-in (car (fys :ts x)) *type-kws*)))
  :hints (("Goal" :expand ((fys :ts x) (fgs :ts x)) :in-theory (enable tok-in))))
(defthm fys-first
  (and (implies (not (consp x)) (and (equal (fys :items x) nil) (equal (fys :attrs x) nil) (equal (fys :prefix x) nil)
                                     (equal (fys :onames x) nil) (equal (fys :ctl x) nil) (equal (fys :init x) nil)
                                     (equal (fys :oitems x) nil)))
       (implies (and (fgs :attrs x) (consp x)) (and (consp (fys :attrs x)) (equal (car (fys :attrs x)) (op ","))))
       (implies (and (fgs :items x) (consp x)) (and (consp (fys :items x)) (equal (car (fys :items x)) (op ","))))
       (implies (fgs :ent x) (and (consp (fys :ent x)) (name-tok-p (car (fys :ent x)))))
       (implies (fgs :ents x) (and (consp (fys :ents x)) (name-tok-p (car (fys :ents x)))))
       (implies (and (fgs :init x) x) (and (consp (fys :init x)) (equal (car (fys :init x)) (op "="))))
       (implies (and (fgs :init x) (not x)) (equal (fys :init x) nil))
       (implies (fgs :shape x) (and (consp (fys :shape x))
                                    (or (start-tok-p (car (fys :shape x))) (equal (car (fys :shape x)) (op ":")))))
       (implies (fgs :ix x) (and (consp (fys :ix x)) (name-tok-p (car (fys :ix x)))))
       (implies (fgs :ixs x) (and (consp (fys :ixs x)) (name-tok-p (car (fys :ixs x)))))
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
  :hints (("Goal" :in-theory (thy-or fys-first (enable fgs fys names-p names-y onames-y member-equal))
           :expand ((fgs :shapes* x) (fys :shapes* x) (fgs :ranges x) (fys :ranges x) (fgs :ixs x) (fys :ixs x) (fgs :ents x) (fys :ents x)
                    (onames-y x) (names-y x) (names-p x)))))

(defthm fys-prefix-first
  (implies (and (fgs :prefix x) (consp x))
           (and (consp (fys :prefix x))
                (or (tok-in (car (fys :prefix x)) *prefix-kws*) (tok-in (car (fys :prefix x)) *type-kws*))))
  :hints (("Goal" :expand ((fgs :prefix x) (fys :prefix x)) :in-theory (enable tok-in))))

; each lemma expands its own call on the spelling, and nothing else of its nt
; what follows an item: another, or the statement's end
; a name is no punctuation
(defthm name-tok-not-punct
  (implies (name-tok-p tk)
           (and (not (equal tk '(:op ":"))) (not (equal tk '(:op ","))) (not (equal tk '(:op "(")))
                (not (equal tk '(:op "="))) (not (equal tk '(:op ")"))) (not (equal tk '(:op "*")))
                (not (equal tk '(:name "function"))) (not (equal tk '(:name "subroutine")))))
  :hints (("Goal" :in-theory (enable name-tok-p))))

; a one-part list, and a six-part list (DO's range), equal the list of their parts
(defthm equal-list1
  (implies (and (true-listp x) (equal (len x) 1)) (equal (equal x (list a)) (equal (car x) a)))
  :hints (("Goal" :in-theory (thy-or equal-list1 (current-theory :here)) :expand ((len x) (len (cdr x)) (true-listp x) (true-listp (cdr x))))))
(defthm equal-list3
  (implies (and (true-listp x) (equal (len x) 3))
           (equal (equal x (list a b c))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c))))
  :hints (("Goal" :in-theory (thy-or equal-list3 (current-theory :here)) :expand ((len x) (true-listp x) (len (cdr x)) (true-listp (cdr x)) (len (cddr x)) (true-listp (cddr x)) (len (cdddr x)) (true-listp (cdddr x))))))
(defthm equal-list4
  (implies (and (true-listp x) (equal (len x) 4))
           (equal (equal x (list a b c d))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d))))
  :hints (("Goal" :in-theory (thy-or equal-list4 (current-theory :here)) :expand ((len x) (true-listp x) (len (cdr x)) (true-listp (cdr x)) (len (cddr x)) (true-listp (cddr x)) (len (cdddr x)) (true-listp (cdddr x)) (len (cddddr x)) (true-listp (cddddr x))))))
(defthm equal-list5
  (implies (and (true-listp x) (equal (len x) 5))
           (equal (equal x (list a b c d e))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d) (equal (car (cddddr x)) e))))
  :hints (("Goal" :in-theory (thy-or equal-list5 (current-theory :here)) :expand ((len x) (true-listp x) (len (cdr x)) (true-listp (cdr x)) (len (cddr x)) (true-listp (cddr x)) (len (cdddr x)) (true-listp (cdddr x)) (len (cddddr x)) (true-listp (cddddr x)) (len (cdr (cddddr x))) (true-listp (cdr (cddddr x)))))))
(defthm equal-list6
  (implies (and (true-listp x) (equal (len x) 6))
           (equal (equal x (list a b c d e g))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d)
                       (equal (car (cddddr x)) e) (equal (cadr (cddddr x)) g))))
  :hints (("Goal" :in-theory (thy-or equal-list6 (current-theory :here)) :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x)) (len (cddddr x))
                            (len (cdr (cddddr x))) (len (cddr (cddddr x)))
                            (true-listp x) (true-listp (cdr x)) (true-listp (cddr x)) (true-listp (cdddr x))
                            (true-listp (cddddr x)) (true-listp (cdr (cddddr x))) (true-listp (cddr (cddddr x)))))))

(defthm items-follow
  (implies (and (fgs :items y) (sfollow-ok :items r)) (follow-ok :expr (append (fys :items y) r)))
  :hints (("Goal" :cases ((consp y)))))

; what follows a prefix's type-spec: more prefix, or what follows the prefix
(defthm prefix-first-not-paren
  (implies (and (fgs :prefix y) (consp y)) (not (equal (car (fys :prefix y)) '(:op "("))))
  :hints (("Goal" :use ((:instance fys-prefix-first (x y))) :in-theory (e/d (tok-in) (fys-prefix-first fgs-var-open fys-var-open)))))
(defthm prefix-follow
  (implies (and (fgs :prefix y) (sfollow-ok :prefix r)) (sfollow-ok :ts (append (fys :prefix y) r)))
  :hints (("Goal" :cases ((consp y)) :use ((:instance fys-prefix-first (x y)))
           :in-theory (e/d (sfollow-ok scont-tok-p tok-in) (fys-prefix-first fgs-var-open fys-var-open)))))

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
       :hints (("Goal" ,@(if (member-eq nt '(:shapes* :names1 :onames :attrs :ents :items :prefix :ranges :ixs :oitems :kios :dobjs :dvals :dsets))
                              '(:induct (len x)) nil)
                :expand (,top) :in-theory (thy-or ,(packn (list 'fps-complete- nt)) (enable member-equal)))
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
(fps-complete-at :oitems)
(fps-complete-at :io)
(defthm kios-follow                 ; a keyword spec's list begins with "," or ")"
  (implies (fgs :kios y) (sfollow-ok :io (append (fys :kios y) r)))
  :hints (("Goal" :expand ((fys :kios y) (fgs :kios y)) :in-theory (enable sfollow-ok scont-tok-p member-equal))))
(fps-complete-at :kios)
(defthm io-spelled                 ; a spec reads a token; one with its keyword begins with a name
  (implies (fgs :io c) (and (consp (fys :io c)) (implies (not (unit-pos-p c)) (equal (car (car (fys :io c))) :name))))
  :hints (("Goal" :expand ((fgs :io c) (fys :io c)) :use ((:instance expr-first-not (x (caddr c)))))))
(defthm io-len-pos (implies (fgs :io c) (< 0 (len (fys :io c)))) :rule-classes :linear
  :hints (("Goal" :use io-spelled :in-theory (disable io-spelled))))
(defthm kios-atom (implies (not (consp y)) (equal (fys :kios y) '((:op ")")))) :hints (("Goal" :expand ((fys :kios y)))))
(defthm kios-nil (implies (and (fgs :kios y) (not (consp y))) (equal y nil)) :rule-classes :forward-chaining
  :hints (("Goal" :expand ((fgs :kios y)))))
(defthm kios-second-not-fmt
  (implies (and (fgs :kios y) (consp y)) (and (equal (car (fys :kios y)) (op ",")) (not (fmt-head-p (cadr (append (fys :kios y) r))))))
  :hints (("Goal" :expand ((fys :kios y) (fgs :kios y)) :use ((:instance io-spelled (c (car y))))
           :in-theory (e/d (fmt-head-p) (io-spelled)))))
(defthm fps-complete-ios
  (implies (and (fgs :ios x) (sfollow-ok :ios r))
           (equal (fps :ios (append (fys :ios x) r)) (mv t x r)))
  :hints (("Goal" :expand ((fgs :ios x) (fys :ios x)) :in-theory (disable fgs-var-open fys-var-open)
           :cases ((and (unit-pos-p (car x)) (consp (cdr x)) (fmt-pos-p (cadr x)))))))
; a name is no type keyword
(defthm name-tok-not-type-kw
  (implies (name-tok-p tk) (and (not (equal (cadr tk) "integer")) (not (equal (cadr tk) "logical")) (not (equal (cadr tk) "real"))))
  :hints (("Goal" :in-theory (enable name-tok-p))))
(fps-complete-at :ix)
; a name is no keyword: a declaration's rest, a DO CONCURRENT's index, begin with no prefix-spec
(defthm name-tok-not-prefix
  (implies (name-tok-p tk) (and (not (tok-in tk *prefix-kws*)) (not (tok-in tk *type-kws*))
                                (not (tok-in tk '("function" "subroutine"))) (not (tok-in tk *simple-kinds*))))
  :hints (("Goal" :in-theory (enable name-tok-p tok-in member-equal))))
(fps-complete-at :ixs)
(fps-complete-at :ctl)
(fps-complete-at :attr)
(fps-complete-at :attrs)
(fps-complete-at :ent)
(defthm prim-start-not-op           ; a primary begins with no sign, comma, slash or star
  (implies (prim-start-p tk) (not (member-equal tk (list (op "+") (op "-") (op ",") (op "/") (op "*")))))
  :hints (("Goal" :in-theory (union-theories (quote ((:definition member-equal) (:executable-counterpart prim-start-p) (:executable-counterpart op))) (theory (quote minimal-theory))))))
(defthm xname-not-paren (implies (xname-tok-p tk) (not (equal tk (quote (:op "(")))))
  :hints (("Goal" :in-theory (enable xname-tok-p name-tok-p))))
(defthm fy-prim-first                ; a primary begins with a name, a literal, ( or [; a designator with a name
  (implies (fg :prim x)
           (and (consp (fy :prim x))
                (not (member-equal (car (fy :prim x)) (list (op "+") (op "-") (op ",") (op "/") (op "*"))))
                (implies (dobj-p x) (not (equal (car (fy :prim x)) (op "("))))))
  :hints (("Goal" :use (fy-first-prim (:instance prim-start-not-op (tk (car (fy :prim x)))) fy-first-base (:instance fy-first-base (x (cadr x))))
           :expand ((fy :prim x) (fg :prim x))
           :in-theory (thy-or fy-prim-first (e/d (dobj-p) (fy-first-prim prim-start-not-op fy-first-base))))))
(defthm fys-dobj-first
  (implies (fgs :dobj x) (and (consp (fys :dobj x)) (not (member-equal (car (fys :dobj x)) (list (op ",") (op "/"))))))
  :hints (("Goal" :expand ((fys :dobj x) (fgs :dobj x)) :use fy-prim-first :in-theory (thy-or fys-dobj-first (e/d (member-equal) (fy-prim-first))))))
(defthm dobj-dval-follow              ; what follows a DATA object or value follows its primary
  (and (implies (sfollow-ok :dobj r) (follow-ok :prim r))
       (implies (sfollow-ok :dval r) (and (follow-ok :prim r) (not (equal (car r) '(:op "*"))))))
  :hints (("Goal" :in-theory (union-theories (quote (  (:type-prescription len) (:definition follow-ok) (:definition scont-tok-p) (:definition sfollow-ok) (:executable-counterpart equal) (:executable-counterpart member-equal) (:executable-counterpart not)   (:executable-counterpart op) (:rewrite default-car) (:rewrite follow-atom) (:type-prescription cont-tok-p) (:type-prescription follow-ok))) (theory (quote minimal-theory))))))
; a DATA object's and value's cases, each read back by fps over its own
; spelling, the primaries kept whole (fp-complete reads them back)
(defmacro prim-case (nt name tokens tree hyps uses)
  `(defthm ,name
     (implies (and ,@hyps) (equal (fps ,nt ,tokens) (mv t ,tree r)))
     :hints (("Goal" :expand ((:free (s) (fps ,nt ,tokens))) :use ,uses
              :in-theory (union-theories '((:definition kar) (:definition kdr) (:definition mv-nth) (:definition not) (:definition member-equal)
                                           (:rewrite car-append-fp) (:rewrite consp-append-fp) (:rewrite car-cons) (:rewrite cdr-cons)
                                           (:executable-counterpart op) (:executable-counterpart equal) (:executable-counterpart member-equal)
                                           (:executable-counterpart consp) (:executable-counterpart car) (:executable-counterpart cdr)
                                           (:executable-counterpart dconst-p) (:executable-counterpart kar) (:executable-counterpart kdr)
                                           (:executable-counterpart not) (:definition follow-ok) (:definition atom) (:rewrite kadr-etc)
                                           (:rewrite kar-kdr-consp) (:executable-counterpart cont-tok-p))
                              (theory 'minimal-theory))))))
(prim-case :dobj dobj-p-case (append (fy :prim x) r) x
  ((fg :prim x) (dobj-p x) (follow-ok :prim r))
  ((:instance fp-complete (nt :prim)) fy-prim-first))
(defthm follow-ok-ilist (follow-ok :ilist r) :hints (("Goal" :in-theory (union-theories (quote ((:definition follow-ok) (:definition cont-tok-p) (:definition atom) (:definition not) (:executable-counterpart member-equal) (:executable-counterpart op) (:executable-counterpart equal))) (theory (quote minimal-theory))))))
(prim-case :dobj dobj-ido-case (cons '(:op "(") (append (fy :ilist y) r)) (cons :ido y)
  ((fg :ilist y))
  ((:instance fp-complete (nt :ilist) (x y)) follow-ok-ilist))
(defthm fps-complete-dobj
  (implies (and (fgs :dobj x) (sfollow-ok :dobj r)) (equal (fps :dobj (append (fys :dobj x) r)) (mv t x r)))
  :hints (("Goal" :expand ((fgs :dobj x) (fys :dobj x)) :use dobj-dval-follow
           :in-theory (union-theories '((:rewrite dobj-p-case) (:rewrite dobj-ido-case) (:rewrite cons-car-cdr-fp) (:definition binary-append)
                                        (:rewrite car-cons) (:rewrite cdr-cons) (:executable-counterpart equal) (:definition eq) (:definition not) (:executable-counterpart op) (:definition kar) (:executable-counterpart member-equal) (:definition dobj-p) (:definition member-equal))
                              (theory 'minimal-theory)))))
(defthm len-fys-dobj (implies (fgs :dobj x) (< 0 (len (fys :dobj x)))) :rule-classes :linear
  :hints (("Goal" :use fys-dobj-first :expand ((len (fys :dobj x))) :in-theory (union-theories (quote ((:definition len) (:type-prescription len))) (theory (quote minimal-theory))))))
; a DATA list's theory: :ents's, without its element's lemmas
(defconst *dlist-runes*
  '((:type-prescription len) (:definition atom) (:definition binary-append) (:definition fix) (:definition kar) (:definition kdr) (:definition len)
    (:definition mv-nth) (:definition not) (:definition null) (:definition synp) (:executable-counterpart binary-+) (:executable-counterpart consp)
    (:executable-counterpart eql) (:executable-counterpart equal) (:executable-counterpart fgs) (:executable-counterpart fys) (:executable-counterpart len)
    (:executable-counterpart member-equal) (:executable-counterpart name-tok-p) (:executable-counterpart not) (:executable-counterpart null)
    (:executable-counterpart op) (:executable-counterpart scont-tok-p) (:executable-counterpart tau-system) (:executable-counterpart true-listp)
    (:executable-counterpart zp) (:induction len) (:rewrite append-assoc-fp) (:rewrite append-to-nil) (:rewrite associativity-of-+)
    (:rewrite car-append-fp) (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite commutativity-2-of-+) (:rewrite commutativity-of-+)
    (:rewrite cons-car-cdr-fp) (:rewrite consp-append-fp) (:rewrite equal-list3) (:rewrite fgs-var-open) (:rewrite fps-open)
    (:definition member-equal) (:rewrite fys-var-open) (:rewrite kar-kdr-consp) (:rewrite len-append-fp) (:rewrite nonempty-parts)
    (:rewrite sfollow-facts) (:rewrite unicity-of-0) (:type-prescription binary-append) (:type-prescription fgs) (:type-prescription fps)
    (:type-prescription fys) (:type-prescription sfollow-ok)))
(defmacro fps-complete-with (nt runes)
  (let ((top `(fps ,nt (binary-append (fys ,nt x) r))))
    `(defthm ,(packn (list 'fps-complete- nt))
       (implies (and (fgs ,nt x) (sfollow-ok ,nt r)) (equal ,top (mv t x r)))
       :hints (("Goal" :induct (len x) :expand (,top) :in-theory (union-theories (append ',runes *dlist-runes*) (theory 'minimal-theory)))
               (top-expand-hint id ',top)))))
(fps-complete-with :dobjs ((:rewrite fps-complete-dobj) (:linear len-fys-dobj) (:rewrite fys-dobj-first)))
(defmacro dval-case (name tokens tree hyps uses)
  `(defthm ,name
     (implies (and ,@hyps) (equal (fps :dval ,tokens) (mv t ,tree r)))
     :hints (("Goal" :expand ((:free (s) (fps :dval ,tokens))) :use ,uses
              :in-theory (union-theories '((:definition kar) (:definition kdr) (:definition mv-nth) (:definition not) (:definition member-equal)
                                           (:rewrite car-append-fp) (:rewrite consp-append-fp) (:rewrite car-cons) (:rewrite cdr-cons)
                                           (:executable-counterpart op) (:executable-counterpart equal) (:executable-counterpart member-equal)
                                           (:executable-counterpart consp) (:executable-counterpart car) (:executable-counterpart cdr)
                                           (:executable-counterpart dconst-p) (:executable-counterpart kar) (:executable-counterpart kdr) (:executable-counterpart not) (:definition follow-ok) (:definition atom) (:rewrite kadr-etc) (:rewrite kar-kdr-consp) (:executable-counterpart cont-tok-p))
                              (theory 'minimal-theory))))))
(dval-case dval-c (append (fy :prim c) r) (list nil nil c)
  ((fg :prim c) (dconst-p nil c) (follow-ok :prim r) (not (equal (car r) '(:op "*"))))
  ((:instance fp-complete (nt :prim) (x c)) (:instance fy-prim-first (x c))))
(dval-case dval-sc (cons s (append (fy :prim c) r)) (list nil s c)
  ((fg :prim c) (dconst-p s c) (member-equal s '((:op "+") (:op "-"))) (follow-ok :prim r))
  ((:instance fp-complete (nt :prim) (x c))))
(dval-case dval-pc (append (fy :prim p) (cons '(:op "*") (append (fy :prim c) r))) (list p nil c)
  ((fg :prim p) (drep-p p) (fg :prim c) (dconst-p nil c) (follow-ok :prim r))
  ((:instance fp-complete (nt :prim) (x p) (r (cons '(:op "*") (append (fy :prim c) r)))) (:instance fp-complete (nt :prim) (x c))
   (:instance fy-prim-first (x p)) (:instance fy-prim-first (x c))))
(dval-case dval-psc (append (fy :prim p) (cons '(:op "*") (cons s (append (fy :prim c) r)))) (list p s c)
  ((fg :prim p) (drep-p p) (fg :prim c) (dconst-p s c) (member-equal s '((:op "+") (:op "-"))) (follow-ok :prim r))
  ((:instance fp-complete (nt :prim) (x p) (r (cons '(:op "*") (cons s (append (fy :prim c) r))))) (:instance fp-complete (nt :prim) (x c))
   (:instance fy-prim-first (x p))))
(defthm fps-complete-dval            ; [r *] [sign] c, each primary kept whole: fp-complete answers it
  (implies (and (fgs :dval x) (sfollow-ok :dval r)) (equal (fps :dval (append (fys :dval x) r)) (mv t x r)))
  :hints (("Goal" :expand ((fgs :dval x) (fys :dval x)) :use dobj-dval-follow
           :in-theory (union-theories '((:rewrite dval-c) (:rewrite dval-sc) (:rewrite dval-pc) (:rewrite dval-psc) (:rewrite equal-list3)
                                        (:rewrite append-assoc-fp) (:rewrite car-cons) (:rewrite cdr-cons) (:definition binary-append)
                                        (:definition member-equal) (:definition kar) (:definition kdr) (:rewrite kadr-etc) (:rewrite kar-kdr-consp)
                                        (:executable-counterpart op) (:executable-counterpart equal) (:executable-counterpart consp)
                                        (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart binary-append) (:executable-counterpart len) (:executable-counterpart fg) (:executable-counterpart dconst-p) (:definition not) (:definition atom) (:rewrite cons-equal))
                              (theory 'minimal-theory)))))
(defthm len-fy-prim (implies (fg :prim x) (< 0 (len (fy :prim x)))) :rule-classes :linear
  :hints (("Goal" :use fy-prim-first :expand ((len (fy :prim x))) :in-theory (union-theories (quote ((:definition len) (:type-prescription len))) (theory (quote minimal-theory))))))
(defthm len-fys-dval (implies (fgs :dval x) (< 0 (len (fys :dval x)))) :rule-classes :linear
  :hints (("Goal" :expand ((fgs :dval x) (fys :dval x)) :in-theory (disable fy-prim-first prim-as-base prim-as-dref fps-complete-dval))))
(defthm consp-fys-dval (implies (fgs :dval x) (consp (fys :dval x)))
  :hints (("Goal" :use len-fys-dval :in-theory (union-theories (quote ((:definition len))) (theory (quote minimal-theory))))))
(fps-complete-with :dvals ((:rewrite consp-fys-dval) (:rewrite fps-complete-dval) (:linear len-fys-dval)))
(defthm dset-open
  (and (equal (fys :dset x) (append (fys :dobjs (kar x)) (fys :dvals (kadr x))))
       (equal (fgs :dset x) (and (consp x) (consp (cdr x)) (consp (cddr x)) (null (cdddr x)) (fgs :dobjs (car x)) (fgs :dvals (cadr x)) (booleanp (caddr x)))))
  :hints (("Goal" :expand ((fys :dset x) (fgs :dset x) (len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))) :in-theory (disable fgs-var-open fys-var-open))))
(defthm len-fys-dobjs (implies (fgs :dobjs x) (< 0 (len (fys :dobjs x)))) :rule-classes :linear
  :hints (("Goal" :expand ((fgs :dobjs x) (fys :dobjs x)) :in-theory (disable fgs-var-open fys-var-open))))
(defthm len-fys-dvals (implies (fgs :dvals x) (< 0 (len (fys :dvals x)))) :rule-classes :linear
  :hints (("Goal" :expand ((fgs :dvals x) (fys :dvals x)) :in-theory (disable fgs-var-open fys-var-open))))
(defthm consp-fys-dobjs-dvals (and (implies (fgs :dobjs x) (consp (fys :dobjs x))) (implies (fgs :dvals x) (consp (fys :dvals x))))
  :hints (("Goal" :use (len-fys-dobjs len-fys-dvals) :in-theory (union-theories (quote ((:definition len))) (theory (quote minimal-theory))))))
(defthm dsets-first                   ; a set begins with an object
  (implies (fgs :dsets x) (and (consp (fys :dsets x)) (not (equal (car (fys :dsets x)) '(:op ",")))))
  :hints (("Goal" :expand ((fgs :dsets x) (fys :dsets x) (fys :dobjs (car (car x))) (fgs :dobjs (car (car x))))
           :use (:instance fys-dobj-first (x (car (car (car x)))))
           :in-theory (disable fgs-var-open fys-var-open fys-dobj-first))))
(defthm cons-equal-consp (implies (consp x) (equal (equal (cons a b) x) (and (equal a (car x)) (equal b (cdr x))))) :hints (("Goal" :in-theory (union-theories (quote ((:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-car-cdr))) (theory (quote minimal-theory))))))
(defthm equal-nil1 (implies (consp y) (equal (equal (quote (nil)) y) (and (null (car y)) (null (cdr y))))) :hints (("Goal" :in-theory (theory (quote minimal-theory)))))
(defthm dsets-follow (implies (sfollow-ok :dsets r) (atom r)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable sfollow-ok scont-tok-p))))
(fps-complete-with :dsets ((:rewrite fps-complete-dobjs) (:rewrite fps-complete-dvals) (:linear len-fys-dobjs) (:linear len-fys-dvals) (:rewrite dset-open) (:rewrite cons-equal-consp) (:rewrite consp-fys-dobjs-dvals) (:rewrite equal-nil1) (:definition kadr) (:definition kaddr) (:rewrite dsets-first) (:forward-chaining dsets-follow)))
(in-theory (disable cons-equal-consp equal-nil1 dset-open))   ; the DATA lists' own
(fps-complete-at :ents)
(fps-complete-at :decl-rest)
(fps-complete-at :prefix)
(fps-complete-at :fn-rest)
(fps-complete-at :sub-rest)

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
(defthm stmt-nt-name
  (implies (name-tok-p tk) (equal (stmt-nt tk) :s-assign))
  :hints (("Goal" :in-theory (enable name-tok-p tok-in member-equal))))
(defthm stmt-nt-label
  (equal (stmt-nt (list :lab d)) :s-label)
  :hints (("Goal" :in-theory (enable tok-in member-equal))))
(defthm stmt-nt-ts
  (implies (fgs :ts ts) (equal (stmt-nt (car (fys :ts ts))) :s-unit))
  :hints (("Goal" :expand ((fgs :ts ts) (fys :ts ts)) :in-theory (enable tok-in member-equal))))
(defthm stmt-nt-prefix
  (implies (and (fgs :prefix p) (consp (fys :prefix p))) (equal (stmt-nt (car (fys :prefix p))) :s-unit))
  :hints (("Goal" :expand ((fgs :prefix p) (fys :prefix p)) :in-theory (enable tok-in member-equal))))

(defthm stmt-nt-ts-comma
  (implies (ts-comma-p ts) (equal (stmt-nt (car (fys :ts ts))) :s-unit))
  :hints (("Goal" :expand ((fys :ts ts)) :in-theory (enable ts-comma-p tok-in member-equal))))

(in-theory (disable tok-in stmt-nt))

; R722's comma after CHARACTER * n (C725): the declaration's type-spec is
; read as the prefix CHARACTER * n, and the comma by :s-unit
(defthm ts-comma-shape
  (implies (ts-comma-p ts)
           (and (equal (list "character" (list :len (cadr (cadr ts)) :comma)) ts)
                (fgs :ts (list "character" (list :len (cadr (cadr ts)))))
                (equal (fys :ts ts) (fys :ts (list "character" (list :len (cadr (cadr ts))))))))
  :hints (("Goal" :in-theory (enable ts-comma-p tok-in member-equal)
           :expand ((fys :ts ts) (:free (y) (fys :ts y)) (:free (y) (fgs :ts y))
                    (len ts) (len (cdr ts)) (len (cddr ts)) (len (cadr ts)) (len (cdr (cadr ts))) (len (cddr (cadr ts)))
                    (len (cdddr (cadr ts))) (true-listp ts) (true-listp (cdr ts)) (true-listp (cddr ts)) (true-listp (cadr ts))
                    (true-listp (cdr (cadr ts))) (true-listp (cddr (cadr ts))) (true-listp (cdddr (cadr ts)))))))
(defthm fps-complete-prefix-ts-comma
  (implies (and (ts-comma-p ts) (sfollow-ok :prefix r))
           (equal (fps :prefix (append (fys :ts ts) r))
                  (mv t (list (list :ts (list "character" (list :len (cadr (cadr ts)))))) r)))
  :hints (("Goal" :in-theory (union-theories '(ts-comma-shape fps-complete-prefix-ts) (theory 'minimal-theory)))))
(defthm ents-first-name
  (implies (fgs :ents x) (equal (car (fys :ents x)) (car (car x))))
  :hints (("Goal" :expand ((fgs :ents x) (fys :ents x) (fgs :ent (car x)) (fys :ent (car x))))))
(defthm decl-rest-noattr-first
  (implies (and (fgs :decl-rest d) (not (car d)) (not (cadr d)))
           (equal (car (fys :decl-rest d)) (car (car (caddr d)))))
  :hints (("Goal" :expand ((fgs :decl-rest d) (fys :decl-rest d) (fys :attrs (car d))))))
(defthm attr-first-kw
  (implies (fgs :attr a) (attr-kw-tok-p (car (fys :attr a))))
  :hints (("Goal" :expand ((fgs :attr a) (fys :attr a)) :in-theory (enable attr-kw-tok-p))))
(defthm attrs-second-kw
  (implies (and (fgs :attrs as) (consp as)) (attr-kw-tok-p (cadr (fys :attrs as))))
  :hints (("Goal" :expand ((fgs :attrs as) (fys :attrs as) (fgs :attr (car as)) (fys :attr (car as))) :in-theory (enable attr-kw-tok-p))))
(defthm decl-rest-comma-second
  (implies (and (fgs :decl-rest d) (equal (car (fys :decl-rest d)) '(:op ",")))
           (and (consp (cdr (fys :decl-rest d))) (attr-kw-tok-p (cadr (fys :decl-rest d)))))
  :hints (("Goal" :expand ((fgs :decl-rest d) (fys :decl-rest d)) :cases ((consp (car d)))
           :use ((:instance attrs-second-kw (as (car d)))) :in-theory (disable attrs-second-kw attr-kw-tok-p))
          ("Subgoal 2" :expand ((fys :attrs (car d)) (fgs :attrs (car d))))))
(defthm decl-rest-comma-second-append
  (implies (and (fgs :decl-rest d) (equal (car (fys :decl-rest d)) '(:op ",")))
           (and (consp (cdr (append (fys :decl-rest d) r))) (attr-kw-tok-p (cadr (append (fys :decl-rest d) r)))))
  :hints (("Goal" :use decl-rest-comma-second :in-theory (disable decl-rest-comma-second attr-kw-tok-p fgs-var-open fys-var-open))))
(defthm name-not-attr-kw-punct (not (attr-kw-tok-p '(:op ":"))) :hints (("Goal" :in-theory (enable attr-kw-tok-p))))
(in-theory (disable ts-comma-p attr-kw-tok-p))

(defthm append-nil-left (equal (append nil x) x))
(defthm append-cons-fs (equal (append (cons a x) y) (cons a (append x y))))
(defthm decl-rest-ents-consp (implies (fgs :decl-rest d) (consp (caddr d))) :hints (("Goal" :expand ((fgs :decl-rest d)))))

; SAVE's names: none, or a name first
(defthm onames-y-consp (equal (consp (onames-y x)) (consp x)) :hints (("Goal" :expand ((onames-y x)))))
(defthm onames-y-first
  (implies (and (names-p x) (consp x)) (and (name-tok-p (car (onames-y x))) (not (equal (car (onames-y x)) '(:op ":")))))
  :hints (("Goal" :expand ((onames-y x) (names-p x)))))
; the statements, kind by kind: a statement is whole, nothing follows it
(defmacro fps-complete-kind (k)
  (let ((top '(fps :stmt (binary-append (fys :stmt x) r))))
    `(defthm ,(packn (list 'fps-complete-stmt- k))
       (implies (and (fgs :stmt x) (equal (car x) ,k) (atom r))
                (equal ,top (mv t x r)))
       :hints (("Goal" :expand (,top) :in-theory (thy-or ,(packn (list 'fps-complete-stmt- k)) (enable member-equal)))))))

(fps-complete-kind :program)
(fps-complete-kind :module)
(fps-complete-kind :end)
(fps-complete-kind :contains)
(fps-complete-kind :block)
(fps-complete-kind :implicit-none)
(fps-complete-kind :else)
(fps-complete-kind :use)
(fps-complete-kind :decl)
(fps-complete-kind :assign)
(fps-complete-kind :cassign)
(fps-complete-kind :type)
(fps-complete-kind :tdecl)
(fps-complete-kind :if-then)
(fps-complete-kind :else-if)
(fps-complete-kind :do)
(fps-complete-kind :simple)
(fps-complete-kind :stop)
(fps-complete-kind :allocate)
(fps-complete-kind :deallocate)
(fps-complete-kind :save)
(fps-complete-kind :dimstmt)
(fps-complete-kind :data)
(fps-complete-kind :implicit)
(fps-complete-kind :call)
(fps-complete-kind :print)
(fps-complete-kind :function)
(fps-complete-kind :subroutine)
(fps-complete-kind :select)
(fps-complete-kind :case)
(fps-complete-kind :case-default)
(fps-complete-kind :label)
(fps-complete-kind :goto)
(fps-complete-kind :aif)
(fps-complete-kind :ldo)
(fps-complete-kind :format)
(fps-complete-kind :write)
(fps-complete-kind :read)
(fps-complete-kind :readf)
; last: its action statement is one of the kinds above (GO TO and WRITE among them)
(fps-complete-kind :if)

(defun kind-cases (ks) (declare (xargs :mode :program))
  (if (endp ks) nil (cons `(equal (car x) ,(car ks)) (kind-cases (cdr ks)))))

(defconst *stmt-kinds*
  '(:program :module :end :contains :block :implicit-none :else :use :decl :assign :cassign :type :tdecl :if-then :else-if :do :simple :stop :allocate :deallocate :save :dimstmt :implicit :data :call :print
    :function :subroutine :if :select :case :case-default :label :goto :aif :ldo :format :write :read :readf))
(defthm fgs-stmt-kinds                ; a statement is of one of the kinds above
  (implies (fgs :stmt x) (member-equal (car x) *stmt-kinds*))
  :rule-classes nil :hints (("Goal" :expand ((fgs :stmt x)) :in-theory (enable member-equal))))

; fps-complete: a statement's tokens are read back as that statement,
; each kind by its own lemma above
(make-event
 `(defthm fps-complete
    (implies (and (fgs :stmt x) (atom r))
             (equal (fps :stmt (append (fys :stmt x) r)) (mv t x r)))
    :hints (("Goal" :cases ,(kind-cases *stmt-kinds*) :use fgs-stmt-kinds
             :in-theory (e/d (member-equal) (fgs-var-open fys-var-open fps-open))))))

; the openers stay closed past here: a proof that opens a statement says so
(in-theory (disable fgs-cons-open fys-cons-open fgs-var-open fys-var-open fps-open))
