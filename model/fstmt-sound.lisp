; fstmt-sound: fstmt.lisp's parser fps proved sound (fps-sound: every
; tree it answers spells its tokens under fgs); fstmt-complete.lisp proves
; it complete.

(in-package "ACL2")

(include-book "fstmt")

(defthm fg-expr-consp (implies (fg :expr x) (consp x)) :hints (("Goal" :expand ((fg :expr x)))))
(defthm fg-args-true-listp (implies (fg :args x) (true-listp x)) :hints (("Goal" :expand ((fg :args x)))))

; an expression fp reads is a tree, never nil
(defthm fp-expr-tree
  (implies (mv-nth 0 (fp :expr toks)) (mv-nth 1 (fp :expr toks)))
  :hints (("Goal" :use ((:instance fp-sound (nt :expr))) :in-theory (disable fp-sound))))

; fps opens only where a proof says so
(in-theory (disable fps))

; the tree nt answers: an :s-* answers a statement
(defun gnt (nt) (declare (xargs :guard t)) (if (member-eq nt '(:s-head :s-end :s-other :s-use :s-else :s-if :s-do :s-call :s-print :s-assign :s-unit :s-select :s-case :s-label :s-goto :s-format :s-write)) :stmt nt))

; the parts' shapes, and fgs and fys opened only on a tree being built
; (a cons): a subtree a hypothesis speaks of stays closed
(defthm parts-shape
  (and (implies (fgs :decl-rest x) (and (true-listp x) (equal (len x) 3)))
       (implies (fgs :fn-rest x) (and (true-listp x) (equal (len x) 3)))
       (implies (fgs :sub-rest x) (and (true-listp x) (equal (len x) 3)))
       (implies (fgs :ts x) (and (true-listp x) (equal (len x) 2))))
  :hints (("Goal" :expand ((fgs :decl-rest x) (fgs :fn-rest x) (fgs :sub-rest x) (fgs :ts x)))))

(set-ignore-ok t)

; a label written as a number, as the proofs of WRITE and IF use it: its
; digits are a label, and lab-int spells it back. With these, those proofs
; keep label-int-p, lab-int and label-digits-p closed (opened, they take
; minutes in car-cdr-elim)
(defthm label-int-p-facts
  (implies (label-int-p tk)
           (and (consp tk) (label-digits-p (cadr tk)) (label-digits-p (kar (kdr tk)))
                (equal (lab-int (cadr tk)) tk) (equal (lab-int (kar (kdr tk))) tk)))
  :rule-classes nil)
(defthm label-int-p-rules             ; enabled only where those proofs close the label
  (implies (label-int-p tk)
           (and (label-digits-p (cadr tk)) (label-digits-p (kar (kdr tk)))
                (equal (lab-int (cadr tk)) tk) (equal (lab-int (kar (kdr tk))) tk)))
  :hints (("Goal" :use label-int-p-facts)))
(in-theory (disable label-int-p-rules))
(defthm label-int-p-consp
  (implies (label-int-p tk) (and (consp tk) (consp (cdr tk)) (stringp (cadr tk))))
  :rule-classes :forward-chaining)

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
  (and (implies (fgs :shapes* x) (consp x)) (implies (fgs :ents x) (consp x)) (implies (fgs :ranges x) (consp x))
       (implies (fgs :ixs x) (consp x)))
  :hints (("Goal" :expand ((fgs :shapes* x) (fgs :ents x) (fgs :ranges x) (fgs :ixs x)))))

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
    (if (member-eq g '(:stmt :shapes :shapes* :ents :ent :names1 :ts :attr :shape :decl-rest :fn-rest :sub-rest :ranges :range :ixs :ix))
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
        (:oitems (mv-let (ok e r) (fp :expr toks) (declare (ignore e))
                   (if (and ok (equal (kar r) (op ","))) (mv t (kdr r)) (mv nil nil))))
        (:ixs (mv-let (ok s r) (fps :ix toks) (declare (ignore s))
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
  (if (member-eq nt '(:shapes* :names1 :onames :attrs :ents :items :prefix :ranges :ixs :oitems))
      `(defthm ,(packn (list 'fps-sound- nt))
         (implies (mv-nth 0 (fps ,nt toks))
                  ,(sound-concl nt `(mv-nth 1 (fps ,nt toks)) `(mv-nth 2 (fps ,nt toks)) 'toks))
         :hints (("Goal" :induct (list-ind ,nt toks) :expand ((fps ,nt toks)) :in-theory (enable member-equal))))
    `(defthm ,(packn (list 'fps-sound- nt))
       (implies (mv-nth 0 (fps ,nt toks))
                ,(sound-concl nt `(mv-nth 1 (fps ,nt toks)) `(mv-nth 2 (fps ,nt toks)) 'toks))
       :hints (("Goal" :expand ((fps ,nt toks))
                :in-theory ,(case nt (:init '(enable member-equal fgs fys))
                              (:s-write '(e/d (member-equal label-int-p-rules) (label-int-p lab-int label-digits-p)))
                              (otherwise '(enable member-equal))))))))

(fps-sound-at :init)
(fps-sound-at :ts)
(fps-sound-at :shape)
(fps-sound-at :range)
(fps-sound-at :items)
(fps-sound-at :oitems)
(fps-sound-at :ix)
(fps-sound-at :ixs)
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
(fps-sound-at :s-label)
(fps-sound-at :s-goto)
(fps-sound-at :s-format)
(fps-sound-at :s-write)
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
  (implies (and (member-eq nt '(:s-head :s-end :s-other :s-use :s-else :s-do :s-call :s-print :s-assign :s-unit :s-select :s-case :s-label :s-goto :s-format :s-write))
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
; the statement kinds other than IF's, as fps-sound-flat names them
(defthm stmt-nt-flat
  (implies (not (equal (stmt-nt tk) :s-if))
           (member-equal (stmt-nt tk) (quote (:s-head :s-end :s-other :s-use :s-else :s-do :s-call :s-print :s-assign :s-unit :s-select :s-case :s-label :s-goto :s-format :s-write))))
  :hints (("Goal" :in-theory (enable stmt-nt))))

; a statement of a kind other than IF's
(defthm fps-sound-stmt-flat
  (implies (and (not (equal (stmt-nt (kar toks)) :s-if)) (mv-nth 0 (fps :stmt toks)))
           (and (fgs :stmt (mv-nth 1 (fps :stmt toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps :stmt toks))) (mv-nth 2 (fps :stmt toks))) toks)))
  :hints (("Goal" :expand ((fps :stmt toks)) :in-theory (disable stmt-nt)
           :use ((:instance fps-sound-flat (nt (stmt-nt (kar toks))))))))

; what :s-if answers is an IF: never an action statement, so never the
; statement inside another (C1143)
(defthm fps-s-if-kind
  (implies (mv-nth 0 (fps :s-if toks))
           (member-equal (car (mv-nth 1 (fps :s-if toks))) '(:if-then :if :aif)))
  :hints (("Goal" :expand ((fps :s-if toks)) :in-theory (e/d (member-equal label-int-p-rules) (label-int-p lab-int label-digits-p)))))
(defthm fps-stmt-if-kind
  (implies (and (equal (stmt-nt (kar toks)) :s-if) (mv-nth 0 (fps :stmt toks)))
           (not (action-kind-p (car (mv-nth 1 (fps :stmt toks))))))
  :hints (("Goal" :expand ((fps :stmt toks)) :in-theory (e/d (member-equal) (stmt-nt fps-s-if-kind))
           :use ((:instance fps-s-if-kind)))))

; an action statement, the one inside an IF: of a flat kind
(defthm fps-sound-stmt-action
  (implies (and (mv-nth 0 (fps :stmt toks)) (action-kind-p (car (mv-nth 1 (fps :stmt toks)))))
           (and (fgs :stmt (mv-nth 1 (fps :stmt toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps :stmt toks))) (mv-nth 2 (fps :stmt toks))) toks)))
  :hints (("Goal" :cases ((equal (stmt-nt (kar toks)) :s-if)) :in-theory (disable stmt-nt action-kind-p))))

; an IF statement: its condition, then its action statement, of a flat kind
(defthm fps-sound-s-if
  (implies (mv-nth 0 (fps :s-if toks))
           (and (fgs :stmt (mv-nth 1 (fps :s-if toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps :s-if toks))) (mv-nth 2 (fps :s-if toks))) toks)))
  :hints (("Goal" :expand ((fps :s-if toks)) :in-theory (e/d (member-equal label-int-p-rules) (stmt-nt fps-sound-stmt-flat fps-stmt-if-kind label-int-p lab-int label-digits-p)))))

(defthm fps-sound-stmt
  (implies (and (member-eq nt '(:stmt :s-if)) (mv-nth 0 (fps nt toks)))
           (and (fgs :stmt (mv-nth 1 (fps nt toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps nt toks))) (mv-nth 2 (fps nt toks))) toks)))
  :hints (("Goal" :in-theory (e/d (member-equal) (stmt-nt)) :cases ((equal nt :s-if)))
          ("Subgoal 2" :cases ((equal (stmt-nt (kar toks)) :s-if)))
          ("Subgoal 2.1" :expand ((fps :stmt toks)))))

(defconst *fps-nts*
  '(:stmt :s-head :s-end :s-other :s-use :s-else :s-if :s-do :s-call :s-print :s-assign :s-unit :s-select :s-case
    :s-label :s-goto :s-format :s-write :oitems
    :fn-rest :sub-rest :decl-rest :ts :attrs :attr :shapes :shapes* :shape :ranges :range :ixs :ix :ents :ent :init
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

