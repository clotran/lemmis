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

(defthm fp-expr-consp
  (implies (mv-nth 0 (fp :expr toks)) (and (consp (mv-nth 1 (fp :expr toks))) (not (equal (mv-nth 1 (fp :expr toks)) :star))))
  :hints (("Goal" :use ((:instance fp-sound (nt :expr))) :in-theory (disable fp-sound))))
; fps opens only where a proof says so
(in-theory (disable fps))

; the tree nt answers: an :s-* answers a statement
(defun gnt (nt) (declare (xargs :guard t)) (if (member-eq nt '(:s-head :s-end :s-other :s-use :s-else :s-if :s-do :s-call :s-print :s-type :s-assign :s-unit :s-select :s-case :s-label :s-goto :s-format :s-write :s-read)) :stmt nt))

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

; an opener is the definition itself: proved in the minimal theory
(defmacro def-cons-opener (name call)
  `(make-event
    (let ((fn (car ',call)))
      `(defthm ,',name
         (implies (syntaxp (and (quotep nt) (consp x) (member-eq (car x) '(cons quote))))
                  (equal ,',call ,(body fn nil (w state))))
         :hints (("Goal" :in-theory (union-theories '(booleanp) (theory 'minimal-theory)) :expand (,',call)))))))
; a format as the parser reads it from its token, and back
(defthm fmt-head-facts
  (and (implies (fmt-head-p tk) (and (fmt-spec-p (fmt-of tk)) (equal (fmt-tok (fmt-of tk)) tk)))
       (implies (fmt-spec-p f) (and (fmt-head-p (fmt-tok f)) (equal (fmt-of (fmt-tok f)) f))))
  :hints (("Goal" :in-theory (enable label-int-p-rules))))
(in-theory (disable fmt-head-p fmt-of fmt-tok fmt-spec-p ios-ok all-lone))
(def-cons-opener fgs-cons-open (fgs nt x))
(def-cons-opener fys-cons-open (fys nt x))
(in-theory (disable fgs fys shape-kind))
; a spec written with its keyword is never the format written without
(defthm kios-not-fmt-pos
  (implies (and (fgs :kios cs) (consp cs)) (not (fmt-pos-p (car cs))))
  :hints (("Goal" :expand ((fgs :kios cs) (fgs :io (car cs))))))

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
    (if (member-eq g '(:stmt :shapes :shapes* :ents :ent :names1 :ts :attr :shape :decl-rest :fn-rest :sub-rest :ranges :range :ixs :ix :io :ios))
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
        (:kios (if (equal (kar toks) (op ","))
                   (mv-let (ok c r) (fps :io (kdr toks)) (declare (ignore c)) (if ok (mv t r) (mv nil nil)))
                 (mv nil nil)))
        (:items (if (equal (kar toks) (op ","))
                    (mv-let (ok e r) (fp :expr (kdr toks)) (declare (ignore e)) (if ok (mv t r) (mv nil nil)))
                  (mv nil nil)))
        (otherwise (cond ((tok-in (kar toks) *prefix-kws*) (mv t (kdr toks)))
                         ((tok-in (kar toks) *type-kws*)
                          (mv-let (ok ts r) (fps :ts toks) (declare (ignore ts)) (if ok (mv t r) (mv nil nil))))
                         (t (mv nil nil)))))
      (if (and go (< (len r) (len toks))) (list-ind nt r) nil))))

; a list nt inducts on list-ind; thy, if given, is the runes the proof uses
; (so it is as fast writing useless-runes as reading them)
(defmacro fps-sound-at (nt &optional use thy)
  (if (member-eq nt '(:shapes* :names1 :onames :attrs :ents :items :prefix :ranges :ixs :oitems :kios))
      `(defthm ,(packn (list 'fps-sound- nt))
         (implies (mv-nth 0 (fps ,nt toks))
                  ,(sound-concl nt `(mv-nth 1 (fps ,nt toks)) `(mv-nth 2 (fps ,nt toks)) 'toks))
         :hints (("Goal" :induct (list-ind ,nt toks) :expand ((fps ,nt toks)) :in-theory (enable member-equal))))
    `(defthm ,(packn (list 'fps-sound- nt))
       (implies (mv-nth 0 (fps ,nt toks))
                ,(sound-concl nt `(mv-nth 1 (fps ,nt toks)) `(mv-nth 2 (fps ,nt toks)) 'toks))
       :hints (("Goal" :expand ((fps ,nt toks)) ,@(and use `(:use ,use))
                :in-theory ,(if thy `(union-theories ,thy (theory 'minimal-theory)) (case nt (:init '(enable member-equal fgs fys))
                              ((:s-write :s-read :s-print :io :ios :kios) '(e/d (member-equal label-int-p-rules) (label-int-p lab-int label-digits-p)))
                              (otherwise '(enable member-equal)))))))))

(fps-sound-at :init)
(fps-sound-at :ts)
(fps-sound-at :shape)
(fps-sound-at :range)
(fps-sound-at :items)
(fps-sound-at :oitems)
(fps-sound-at :io)
(fps-sound-at :kios)
(fps-sound-at :ios)
(fps-sound-at :ix)
(fps-sound-at :ixs)
(fps-sound-at :ctl nil
  '((:definition binary-append) (:definition kar) (:definition kdr) (:definition len)
   (:definition member-equal) (:definition mv-nth) (:definition not) (:definition null)
   (:definition synp) (:definition tok-in) (:executable-counterpart <) (:executable-counterpart =)
   (:executable-counterpart binary-+) (:executable-counterpart booleanp) (:executable-counterpart car)
   (:executable-counterpart cdr) (:executable-counterpart cons) (:executable-counterpart consp)
   (:executable-counterpart dcolon) (:executable-counterpart eql) (:executable-counterpart equal)
   (:executable-counterpart fgs) (:executable-counterpart fys) (:executable-counterpart if)
   (:executable-counterpart kar) (:executable-counterpart kw) (:executable-counterpart len)
   (:executable-counterpart member-equal) (:executable-counterpart name-tok-p)
   (:executable-counterpart not) (:executable-counterpart null) (:executable-counterpart op)
   (:executable-counterpart tok-in) (:executable-counterpart true-listp) (:executable-counterpart zp)
   (:rewrite append-assoc-fp) (:rewrite append-to-nil) (:rewrite car-cons) (:rewrite cdr-cons)
   (:rewrite cons-car-cdr-fp) (:rewrite fgs-cons-open) (:rewrite fold-consts-in-+)
   (:rewrite fp-expr-tree) (:rewrite fp-sound) (:rewrite fps-sound-ixs) (:rewrite fps-sound-ts)
   (:rewrite fys-cons-open) (:rewrite kadr-etc) (:rewrite kar-kdr-consp)
   (:type-prescription binary-append) (:type-prescription fgs) (:type-prescription fp)
   (:type-prescription fps) (:type-prescription fy) (:type-prescription fys) (:type-prescription len)
   (:type-prescription name-tok-p) (:type-prescription true-listp-append)))
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
(fps-sound-at :s-other ((:instance fp-sound (nt :expr) (toks (cdr toks)))))   ; STOP stop-code
(fps-sound-at :s-use)
(fps-sound-at :s-else)
(fps-sound-at :s-do)
(fps-sound-at :s-call)
(fps-sound-at :s-print)
(fps-sound-at :s-assign)
(fps-sound-at :s-type)
(fps-sound-at :s-select)
(fps-sound-at :s-case)
(fps-sound-at :s-label)
(fps-sound-at :s-goto)
(fps-sound-at :s-format)
(fps-sound-at :s-write)
(fps-sound-at :s-read)
; a declaration's type-spec, read as a prefix of one type-spec
(defthm fps-prefix-just-ts
  (let ((p (mv-nth 1 (fps :prefix toks))))
    (implies (and (mv-nth 0 (fps :prefix toks)) (consp p) (null (cdr p)) (equal (car (car p)) :ts))
             (and (consp (cdr (car p))) (fgs :ts (cadr (car p)))
                  (equal (append (fys :ts (cadr (car p))) (mv-nth 2 (fps :prefix toks))) toks))))
  :hints (("Goal" :use ((:instance prefix-just-ts (p (mv-nth 1 (fps :prefix toks))))) :in-theory (disable fps-sound-prefix))
          ("Goal'" :use fps-sound-prefix)))

; a prefix's type-spec is never the comma form (R722, C725)
(defthm ts-not-comma (implies (fgs :ts ts) (not (ts-comma-p ts)))
  :hints (("Goal" :expand ((fgs :ts ts)) :in-theory (enable ts-comma-p))))

(defthm fps-decl-rest-consp
  (implies (mv-nth 0 (fps :decl-rest toks)) (consp (mv-nth 1 (fps :decl-rest toks))))
  :hints (("Goal" :expand ((fps :decl-rest toks)))))

(defthm parts-shape-comma
  (and (implies (fgs :decl-rest x) (and (consp x) (consp (cdr x)) (consp (cddr x))))
       (implies (and (fgs :ts x) (equal (car (cadr x)) :len))
                (and (consp (cdr (cadr x))) (equal (car x) "character") (len-tok-p (cadr (cadr x))))))
  :hints (("Goal" :expand ((fgs :decl-rest x) (fgs :ts x)))))

(defthm fys-ts-comma
  (implies (and (fgs :ts ts) (equal (car (cadr ts)) :len))
           (equal (fys :ts (list "character" (list :len (cadr (cadr ts)) :comma))) (fys :ts ts)))
  :hints (("Goal" :expand ((fgs :ts ts) (fys :ts ts) (:free (x) (fys :ts x))))))

(fps-sound-at :s-unit (fps-prefix-just-ts (:instance fps-sound-decl-rest (toks (cdr (mv-nth 2 (fps :prefix toks))))))
  '((:congruence iff-implies-equal-not) (:definition =) (:definition assoc-equal)
   (:definition attr-kw-tok-p) (:definition binary-append) (:definition kar)
   (:definition kdr) (:definition len) (:definition mv-nth) (:definition not) (:definition null)
   (:definition synp) (:definition true-listp) (:definition ts-comma-p) (:executable-counterpart =)
   (:executable-counterpart attr-kw-tok-p) (:executable-counterpart binary-+)
   (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart cons)
   (:executable-counterpart consp) (:executable-counterpart eql) (:executable-counterpart equal)
   (:executable-counterpart fgs) (:executable-counterpart fps) (:executable-counterpart fys)
   (:executable-counterpart if) (:executable-counterpart kar) (:executable-counterpart kdr)
   (:executable-counterpart kw) (:executable-counterpart len) (:executable-counterpart member-equal)
   (:executable-counterpart mv-nth) (:executable-counterpart not) (:executable-counterpart null)
   (:executable-counterpart op) (:executable-counterpart zp) (:rewrite append-assoc-fp)
   (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-car-cdr-fp) (:rewrite default-car)
   (:rewrite default-cdr) (:rewrite fgs-cons-open) (:rewrite fold-consts-in-+)
   (:rewrite fps-prefix-just-ts) (:rewrite fps-sound-decl-rest) (:rewrite fps-sound-fn-rest)
   (:rewrite fps-sound-prefix) (:rewrite fps-sound-sub-rest) (:rewrite fys-cons-open)
   (:rewrite fys-ts-comma) (:rewrite kadr-etc) (:rewrite kar-kdr-consp) (:rewrite parts-shape)
   (:rewrite parts-shape-comma) (:rewrite ts-not-comma) (:type-prescription fgs)
   (:type-prescription fps) (:type-prescription fys) (:type-prescription len)
   (:type-prescription member-equal)))

; the statements other than IF, as one
(defthm fps-sound-flat
  (implies (and (member-eq nt '(:s-head :s-end :s-other :s-use :s-else :s-do :s-call :s-print :s-type :s-assign :s-unit :s-select :s-case :s-label :s-goto :s-format :s-write :s-read))
                (mv-nth 0 (fps nt toks)))
           (and (fgs :stmt (mv-nth 1 (fps nt toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps nt toks))) (mv-nth 2 (fps nt toks))) toks)))
  ; each kind is its own lemma above, a rewrite rule once nt is a constant
  :hints (("Goal" :in-theory (union-theories '(member-equal fps-sound-s-head fps-sound-s-end fps-sound-s-other fps-sound-s-use fps-sound-s-else fps-sound-s-do fps-sound-s-call fps-sound-s-print fps-sound-s-type fps-sound-s-assign fps-sound-s-unit fps-sound-s-select fps-sound-s-case fps-sound-s-label fps-sound-s-goto fps-sound-s-format fps-sound-s-write fps-sound-s-read) (theory 'minimal-theory)))))

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
           (member-equal (stmt-nt tk) (quote (:s-head :s-end :s-other :s-use :s-else :s-do :s-call :s-print :s-type :s-assign :s-unit :s-select :s-case :s-label :s-goto :s-format :s-write :s-read))))
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
  :hints (("Goal" :expand ((fps :s-if toks)) :in-theory (union-theories '(member-equal car-cons) (theory 'minimal-theory)))))
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
  :hints (("Goal" :cases ((equal (stmt-nt (kar toks)) :s-if))
           :in-theory (union-theories '(fps-stmt-if-kind fps-sound-stmt-flat) (theory 'minimal-theory)))))

; an IF statement: its condition, then its action statement, of a flat kind
(defthm fps-sound-s-if
  (implies (mv-nth 0 (fps :s-if toks))
           (and (fgs :stmt (mv-nth 1 (fps :s-if toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps :s-if toks))) (mv-nth 2 (fps :s-if toks))) toks)))
  :hints (("Goal" :expand ((fps :s-if toks))
           :in-theory (union-theories
                       '((:definition action-kind-p) (:definition aif-labs-p) (:definition binary-append) (:definition eq)
                        (:definition eql) (:definition kar) (:definition kdr) (:definition kw)
                        (:definition len) (:definition member-equal) (:definition mv-nth) (:definition not)
                        (:definition null) (:definition synp) (:executable-counterpart =)
                        (:executable-counterpart action-kind-p) (:executable-counterpart binary-+)
                        (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart cons)
                        (:executable-counterpart consp) (:executable-counterpart dcolon) (:executable-counterpart eql)
                        (:executable-counterpart equal) (:executable-counterpart fgs) (:executable-counterpart fys)
                        (:executable-counterpart if) (:executable-counterpart kar) (:executable-counterpart kdr)
                        (:executable-counterpart kw) (:executable-counterpart label-digits-p)
                        (:executable-counterpart label-int-p) (:executable-counterpart len)
                        (:executable-counterpart member-equal) (:executable-counterpart not) (:executable-counterpart op)
                        (:executable-counterpart true-listp) (:executable-counterpart zp)
                        (:forward-chaining label-int-p-consp) (:rewrite append-assoc-fp) (:rewrite car-cons)
                        (:rewrite cdr-cons) (:rewrite cons-car-cdr-fp) (:rewrite fgs-cons-open) (:rewrite fold-consts-in-+)
                        (:rewrite fp-sound) (:rewrite fps-sound-stmt-action) (:rewrite fys-cons-open) (:rewrite kadr-etc)
                        (:rewrite kar-kdr-consp) (:rewrite label-int-p-rules) (:type-prescription binary-append)
                        (:type-prescription fgs) (:type-prescription fp) (:type-prescription fps) (:type-prescription fys)
                        (:type-prescription label-int-p) (:type-prescription true-listp-append))
                       (theory 'minimal-theory)))))

(defthm fps-sound-stmt
  (implies (and (member-eq nt '(:stmt :s-if)) (mv-nth 0 (fps nt toks)))
           (and (fgs :stmt (mv-nth 1 (fps nt toks)))
                (equal (append (fys :stmt (mv-nth 1 (fps nt toks))) (mv-nth 2 (fps nt toks))) toks)))
  :hints (("Goal" :in-theory (e/d (member-equal) (stmt-nt)) :cases ((equal nt :s-if)))
          ("Subgoal 2" :cases ((equal (stmt-nt (kar toks)) :s-if)))
          ("Subgoal 2.1" :expand ((fps :stmt toks)))))

(defconst *fps-nts*
  '(:stmt :s-head :s-end :s-other :s-use :s-else :s-if :s-do :s-call :s-print :s-type :s-assign :s-unit :s-select :s-case
    :s-label :s-goto :s-format :s-write :s-read :oitems :ios :kios :io
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

