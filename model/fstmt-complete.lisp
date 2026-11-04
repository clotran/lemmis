; fstmt-complete: fps-complete, fstmt.lisp's parser complete: every statement
; fgs allows is read back as its own tree (fps-sound is fstmt-sound.lisp's).

(in-package "ACL2")

(include-book "fstmt-sound")

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
    (:ts (equal tk (op "(")))
    (:attrs (equal tk (op ",")))
    ((:shape :range :ix :io) (not (member-equal tk (list (op ",") (op ")")))))   ; a shape or a range is ended by "," or ")" only
    (:init (cont-tok-p :expr tk))
    (:ent (or (cont-tok-p :expr tk) (equal tk (op "(")) (equal tk (op "="))))
    ((:ents :decl-rest) (or (cont-tok-p :expr tk) (equal tk (op "(")) (equal tk (op "=")) (equal tk (op ","))))
    (:prefix (or (tok-in tk *prefix-kws*) (tok-in tk *type-kws*) (equal tk (op "("))))
    (:fn-rest (equal tk (kw "result")))
    (:sub-rest (equal tk (op "(")))
    ((:shapes :shapes* :names :names1 :ranges :ixs :ios :kios) nil)
    (otherwise t)))                       ; a statement is whole; DO's control ends it

(defun sfollow-ok (nt r)
  (declare (xargs :guard t))
  (if (atom r) (not (member-eq nt '(:shape :range :ix :io))) (not (scont-tok-p nt (car r)))))

(defthm sfollow-facts
  (and (implies (and (atom r) (not (member-eq nt '(:shape :range :ix :io)))) (sfollow-ok nt r))
       (equal (sfollow-ok nt (cons a b)) (not (scont-tok-p nt a)))
       (equal (sfollow-ok nt (append a b)) (if (consp a) (not (scont-tok-p nt (car a))) (sfollow-ok nt b)))
       (implies (member-eq nt '(:shapes :shapes* :names :names1 :ranges :ixs :ios :kios)) (sfollow-ok nt r))
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
           :in-theory (enable sfollow-ok scont-tok-p cont-tok-p member-equal))))

; first tokens of the parts' spellings, and their shapes
(defthm fys-first
  (and (implies (not (consp x)) (and (equal (fys :items x) nil) (equal (fys :attrs x) nil) (equal (fys :prefix x) nil)
                                     (equal (fys :onames x) nil) (equal (fys :ctl x) nil) (equal (fys :init x) nil)
                                     (equal (fys :oitems x) nil)))
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
  :hints (("Goal" :in-theory (enable fgs fys names-p names-y onames-y member-equal)
           :expand ((fgs :shapes* x) (fys :shapes* x) (fgs :ranges x) (fys :ranges x) (fgs :ixs x) (fys :ixs x) (fgs :ents x) (fys :ents x) (fgs :prefix x) (fys :prefix x)
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
       :hints (("Goal" ,@(if (member-eq nt '(:shapes* :names1 :onames :attrs :ents :items :prefix :ranges :ixs :oitems :kios))
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
(fps-complete-at :ixs)
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
  '(:program :module :end :contains :implicit-none :else :use :decl :assign :if-then :else-if :do :simple :call :print
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
