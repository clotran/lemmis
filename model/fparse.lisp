; fparse: the parser for fgram's grammar, and the theorems that it accepts
; exactly that grammar (Stage A, item 1):
;
;   fp-sound     what fp answers is a tree of the grammar, and spells the
;                tokens it consumed
;   fp-complete  on the tokens any tree of the grammar spells, followed by
;                anything that may follow it (follow-ok), fp answers that
;                tree -- so the grammar is unambiguous, and fp accepts
;                every sentence of it
;
; fp is recursive descent, one token of lookahead (two for a keyword
; argument). Each call answers (mv ok tree rest). Every place it uses
; what an inner call left, it checks that the rest is no longer than the
; tokens it had -- the check that admits it; fp-len proves it always holds.

(in-package "ACL2")

(include-book "fgram")

; a token that can begin an expression
(defun prim-start-p (tk)
  (declare (xargs :guard t))
  (or (xname-tok-p tk) (lit-tok-p tk) (equal tk (op "(")) (equal tk (op "["))))

(defun fp-rank (nt)
  (declare (xargs :guard t))
  (case nt
    (:prim 1) (:mult 2) (:add 3) (:l2 4) (:l4 5) (:and 6) (:or 7) (:equiv 8) (:expr 9)
    ((:arg :elist :tri*) 10) (:args 11)
    (otherwise 1)))

; a keyword argument's head, name =
(defun kw-head-p (toks)
  (declare (xargs :guard t))
  (and (consp toks) (name-tok-p (car toks)) (consp (cdr toks)) (equal (cadr toks) (op "="))))

(defmacro fail () '(mv nil nil toks))

(defun fp (nt toks)
  (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fp-rank nt))
                  :verify-guards nil))
  (let ((tk (kar toks)))
    (case nt
      ((:expr :equiv :or :add)
       (mv-let (ok a r) (fp (lev-sub nt) toks)
         (if (not (and ok (<= (len r) (len toks)))) (fail)
           (mv-let (ok2 rest r2) (fp (lev-rest nt) r)
             (if ok2 (mv t (list a rest) r2) (fail))))))
      ((:expr* :equiv* :or* :l2* :add*)
       (if (and (consp toks) (member-equal tk (lev-ops nt)))
           (mv-let (ok a r) (fp (lev-sub nt) (cdr toks))
             (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
               (mv-let (ok2 rest r2) (fp nt r)
                 (if ok2 (mv t (cons (list tk a) rest) r2) (fail)))))
         (mv t nil toks)))
      (:and (if (and (consp toks) (equal tk (op ".not.")))
                (mv-let (ok a r) (fp :l4 (cdr toks)) (if ok (mv t (list t a) r) (fail)))
              (mv-let (ok a r) (fp :l4 toks) (if ok (mv t (list nil a) r) (fail)))))
      (:l4 (mv-let (ok a r) (fp :l2 toks)
             (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                   ((and (consp r) (member-equal (car r) *rel-ops*))
                    (mv-let (ok2 b r2) (fp :l2 (cdr r))
                      (if ok2 (mv t (list a (car r) b) r2) (fail))))
                   (t (mv t (list a nil nil) r)))))
      (:l2 (let* ((sign (if (and (consp toks) (member-equal tk *add-ops*)) tk nil))
                  (t1 (if sign (cdr toks) toks)))
             (mv-let (ok a r) (fp :add t1)
               (if (not (and ok (<= (len r) (len t1)))) (fail)
                 (mv-let (ok2 rest r2) (fp :l2* r)
                   (if ok2 (mv t (list sign a rest) r2) (fail)))))))
      (:mult (mv-let (ok a r) (fp :prim toks)
               (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                     ((and (consp r) (equal (car r) (op "**")))
                      (mv-let (ok2 b r2) (fp :mult (cdr r))
                        (if ok2 (mv t (list a b) r2) (fail))))
                     (t (mv t (list a nil) r)))))
      (:prim (cond ((not (consp toks)) (fail))
                   ((lit-tok-p tk) (mv t (list :lit tk) (cdr toks)))
                   ((xname-tok-p tk)
                    (if (and (consp (cdr toks)) (equal (cadr toks) (op "(")))
                        (mv-let (ok as r) (fp :args (cddr toks))
                          (if ok (mv t (list :ref tk as) r) (fail)))
                      (mv t (list :name tk) (cdr toks))))
                   ((equal tk (op "("))
                    (mv-let (ok e r) (fp :expr (cdr toks))
                      (if (and ok (consp r) (equal (car r) (op ")"))) (mv t (list :paren e) (cdr r)) (fail))))
                   ((equal tk (op "["))
                    (mv-let (ok es r) (fp :elist (cdr toks))
                      (if ok (mv t (list :acons es) r) (fail))))
                   (t (fail))))
      ((:args :args*)
       (cond ((not (consp toks)) (fail))
             ((equal tk (op ")")) (mv t nil (cdr toks)))
             ((and (eq nt :args*) (not (equal tk (op ",")))) (fail))
             (t (let ((t1 (if (eq nt :args) toks (cdr toks))))
                  (mv-let (ok a r) (fp :arg t1)
                    (if (not (and ok (<= (len r) (len t1)))) (fail)
                      (mv-let (ok2 as r2) (fp :args* r)
                        (if ok2 (mv t (cons a as) r2) (fail)))))))))
      (:arg (cond ((not (consp toks)) (fail))
                  ((kw-head-p toks)
                   (mv-let (ok e r) (fp :expr (cddr toks))
                     (if ok (mv t (list :kw tk e) r) (fail))))
                  ((equal tk (op ":"))
                   (mv-let (ok hs r) (fp :tri* (cdr toks))
                     (if ok (mv t (list* :tri nil hs) r) (fail))))
                  (t (mv-let (ok e r) (fp :expr toks)
                       (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                             ((and (consp r) (equal (car r) (op ":")))
                              (mv-let (ok2 hs r2) (fp :tri* (cdr r))
                                (if ok2 (mv t (list* :tri e hs) r2) (fail))))
                             (t (mv t (list :sub e) r)))))))
      ; after a triplet's first ":": [hi] [: stride], answering (hi st)
      (:tri* (mv-let (ok hi r) (if (or (atom toks) (member-equal tk (list (op ":") (op ",") (op ")")))) (mv t nil toks) (fp :expr toks))
               (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                     ((and (consp r) (equal (car r) (op ":")))
                      (mv-let (ok2 st r2) (fp :expr (cdr r))
                        (if ok2 (mv t (list hi st) r2) (fail))))
                     (t (mv t (list hi nil) r)))))
      (:elist (mv-let (ok e r) (fp :expr toks)
                (if (not (and ok (<= (len r) (len toks)))) (fail)
                  (mv-let (ok2 es r2) (fp :elist* r)
                    (if ok2 (mv t (cons e es) r2) (fail))))))
      (:elist* (cond ((not (consp toks)) (fail))
                     ((equal tk (op "]")) (mv t nil (cdr toks)))
                     ((not (equal tk (op ","))) (fail))
                     (t (mv-let (ok e r) (fp :expr (cdr toks))
                          (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
                            (mv-let (ok2 es r2) (fp :elist* r)
                              (if ok2 (mv t (cons e es) r2) (fail))))))))
      (otherwise (fail)))))

(defthm fp-len
  (<= (len (mv-nth 2 (fp nt toks))) (len toks))
  :rule-classes :linear)

; ---- the tokens' facts, then their recognizers closed

(defthm tok-facts
  (and (implies (name-tok-p x) (and (prim-start-p x) (start-tok-p x) (not (lit-tok-p x))
                                    (consp x) (equal (car x) :name) (xname-tok-p x)))
       (implies (xname-tok-p x) (and (prim-start-p x) (start-tok-p x) (not (lit-tok-p x))
                                     (consp x) (equal (car x) :name)))
       (implies (lit-tok-p x) (and (prim-start-p x) (start-tok-p x) (consp x) (not (equal (car x) :op))))
       (implies (prim-start-p x) (and (start-tok-p x) (not (member-equal x *add-ops*))
                                      (not (equal x '(:op ".not.")))))
       (implies (and (consp x) (eq (car x) :op))
                (and (not (name-tok-p x)) (not (xname-tok-p x)) (not (lit-tok-p x))
                     (equal (prim-start-p x) (or (equal x '(:op "(")) (equal x '(:op "["))))
                     (equal (start-tok-p x)
                            (and (member-equal x '((:op "(") (:op "[") (:op "+") (:op "-") (:op ".not."))) t)))))
  :hints (("Goal" :in-theory (enable name-tok-p xname-tok-p lit-tok-p prim-start-p start-tok-p))))

(in-theory (disable name-tok-p xname-tok-p lit-tok-p prim-start-p start-tok-p))

(defthm append-assoc-fp (equal (append (append a b) c) (append a (append b c))))
(defthm len-append-fp (equal (len (append a b)) (+ (len a) (len b))))
(defthm car-append-fp (equal (car (append a b)) (if (consp a) (car a) (car b))))
(defthm consp-append-fp (equal (consp (append a b)) (or (consp a) (consp b))))
(defthm cons-car-cdr-fp (implies (and (consp r) (equal (car r) a)) (equal (cons a (cdr r)) r)))
(defthm fg-tri*-shape (implies (fg :tri* x) (and (true-listp x) (equal (len x) 2))))

; ---- fp-sound

(defthm fp-sound
  (implies (mv-nth 0 (fp nt toks))
           (and (fg nt (mv-nth 1 (fp nt toks)))
                (equal (append (fy nt (mv-nth 1 (fp nt toks))) (mv-nth 2 (fp nt toks))) toks)))
  :hints (("Goal" :induct (fp nt toks))))

; ---- toward fp-complete: the follow sets

(defun cont-sub-p (b a)           ; every continuer of b continues a
  (declare (xargs :guard t))
  (and (member-equal (list a b)
                     '((:expr :equiv) (:expr :expr*) (:expr* :equiv) (:equiv :or) (:equiv :equiv*)
                       (:equiv* :or) (:or :and) (:or :or*) (:or* :and) (:and :l4) (:l4 :l2)
                       (:l2 :add) (:l2 :l2*) (:l2* :add) (:add :mult) (:add :add*) (:add* :mult)
                       (:mult :prim) (:mult :mult) (:arg :expr) (:tri* :expr) (:arg :tri*)))
       t))

(defthm follow-sub
  (implies (and (follow-ok a r) (cont-sub-p b a)) (follow-ok b r))
  :hints (("Goal" :in-theory (enable follow-ok cont-tok-p))))

(defthm follow-atom (implies (atom r) (follow-ok nt r)) :hints (("Goal" :in-theory (enable follow-ok))))
(defthm follow-cons (equal (follow-ok nt (cons a b)) (not (cont-tok-p nt a)))
  :hints (("Goal" :in-theory (enable follow-ok))))

; a level's operator does not continue its operands
(defthm lev-op-not-cont
  (and (implies (member-equal tk *eqv-ops*) (not (cont-tok-p :equiv tk)))
       (implies (member-equal tk *or-ops*) (not (cont-tok-p :or tk)))
       (implies (member-equal tk *and-ops*) (not (cont-tok-p :and tk)))
       (implies (member-equal tk *rel-ops*) (not (cont-tok-p :l2 tk)))
       (implies (member-equal tk *add-ops*) (not (cont-tok-p :add tk)))
       (implies (member-equal tk *mult-ops*) (not (cont-tok-p :mult tk))))
  :hints (("Goal" :in-theory (enable cont-tok-p))))

; the parser's decisions after a whole tree, when what follows does not continue it
(defthm follow-decisions
  (implies (and (consp r) (follow-ok nt r))
           (and (implies (member-eq nt '(:expr :expr*)) (not (member-equal (car r) *eqv-ops*)))
                (implies (member-eq nt '(:equiv :equiv*)) (not (member-equal (car r) *or-ops*)))
                (implies (member-eq nt '(:or :or*)) (not (member-equal (car r) *and-ops*)))
                (implies (member-eq nt '(:l2 :l2* :l4 :and)) (not (member-equal (car r) *add-ops*)))
                (implies (member-eq nt '(:l4 :and)) (not (member-equal (car r) *rel-ops*)))
                (implies (member-eq nt '(:add :add*)) (not (member-equal (car r) *mult-ops*)))
                (implies (member-eq nt '(:mult :add :add* :l2 :l2* :l4 :and :or :or* :equiv :equiv* :expr :expr*))
                         (not (equal (car r) '(:op "**"))))
                (implies (member-eq nt '(:prim :mult :add :add* :l2 :l2* :l4 :and :or :or* :equiv :equiv* :expr :expr* :arg :tri*))
                         (and (not (equal (car r) '(:op "("))) (not (equal (car r) '(:op "=")))))
                (implies (member-eq nt '(:arg :tri*))
                         (and (not (equal (car r) '(:op ":"))) (not (equal (car r) '(:op "]")))
                              (not (start-tok-p (car r)))))))
  :hints (("Goal" :in-theory (enable follow-ok cont-tok-p))))

; the closing punctuation continues nothing
(defthm closers-not-cont
  (and (implies (member-equal tk '((:op ",") (:op ")"))) (not (cont-tok-p nt tk)))
       (implies (and (equal tk '(:op "]")) (not (member-eq nt '(:arg :tri*)))) (not (cont-tok-p nt tk)))
       (implies (and (member-equal tk '((:op ",") (:op "]"))) (not (member-eq nt '(:arg :tri*))))
                (not (cont-tok-p nt tk))))
  :hints (("Goal" :in-theory (enable cont-tok-p start-tok-p name-tok-p xname-tok-p lit-tok-p))))

; a list closed by its own punctuation is followed by anything
(defthm follow-closed
  (implies (member-eq nt '(:args :args* :elist :elist*)) (follow-ok nt r))
  :hints (("Goal" :in-theory (enable follow-ok cont-tok-p))))

(defthm follow-append
  (equal (follow-ok nt (append a b))
         (if (consp a) (not (cont-tok-p nt (car a))) (follow-ok nt b)))
  :hints (("Goal" :in-theory (enable follow-ok))))

; the closing punctuation continues nothing
(defthm closers-not-cont
  (and (implies (member-equal tk '((:op ",") (:op ")"))) (not (cont-tok-p nt tk)))
       (implies (and (equal tk '(:op "]")) (not (member-eq nt '(:arg :tri*)))) (not (cont-tok-p nt tk)))
       (implies (and (member-equal tk '((:op ",") (:op "]"))) (not (member-eq nt '(:arg :tri*))))
                (not (cont-tok-p nt tk))))
  :hints (("Goal" :in-theory (enable cont-tok-p start-tok-p name-tok-p xname-tok-p lit-tok-p))))

; a list closed by its own punctuation is followed by anything
(defthm follow-closed
  (implies (member-eq nt '(:args :args* :elist :elist*)) (follow-ok nt r))
  :hints (("Goal" :in-theory (enable follow-ok cont-tok-p))))

(defthm follow-append
  (equal (follow-ok nt (append a b))
         (if (consp a) (not (cont-tok-p nt (car a))) (follow-ok nt b)))
  :hints (("Goal" :in-theory (enable follow-ok))))

; an expression's first token is no triplet punctuation
(defthm start-not-closer
  (implies (start-tok-p tk) (not (member-equal tk '((:op ":") (:op ",") (:op ")")))))
  :hints (("Goal" :in-theory (enable start-tok-p name-tok-p xname-tok-p lit-tok-p))))

; an argument is followed by "," or ")"
(defthm follow-arg-closers
  (implies (and (member-eq nt '(:arg :tri*)) (follow-ok nt r) (consp r))
           (and (member-equal (car r) '((:op ",") (:op ")")))
                (member-equal (car r) '((:op ":") (:op ",") (:op ")")))))
  :hints (("Goal" :in-theory (enable follow-ok cont-tok-p))))

(in-theory (disable follow-ok cont-tok-p))

; ---- one level of fy and fg on a variable tree

(defthm kar-kdr-consp
  (implies (consp x) (and (equal (kar x) (car x)) (equal (kdr x) (cdr x)))))
(defthm kadr-etc
  (and (equal (kadr x) (kar (kdr x))) (equal (kaddr x) (kar (kdr (kdr x)))) (equal (kadddr x) (kar (kdr (kdr (kdr x)))))))
(in-theory (disable kadr kaddr kadddr))

(defmacro def-nt-opener (name call)
  `(make-event
    (let ((fn (car ',call)))
      `(defthm ,',name
         (implies (syntaxp (and (quotep nt) (symbolp x))) (equal ,',call ,(body fn nil (w state))))
         :hints (("Goal" :expand (,',call)))))))
(def-nt-opener fy-open (fy nt x))
(def-nt-opener fg-open (fg nt x))

(defthm fg-other
  (implies (and (not (equal nt :expr)) (not (equal nt :equiv)) (not (equal nt :or)) (not (equal nt :add))
                (not (equal nt :expr*)) (not (equal nt :equiv*)) (not (equal nt :or*)) (not (equal nt :l2*))
                (not (equal nt :add*)) (not (equal nt :and)) (not (equal nt :l4)) (not (equal nt :l2))
                (not (equal nt :mult)) (not (equal nt :prim)) (not (equal nt :args)) (not (equal nt :args*))
                (not (equal nt :arg)) (not (equal nt :tri*)) (not (equal nt :elist)) (not (equal nt :elist*)))
           (not (fg nt x)))
  :hints (("Goal" :expand ((fg nt x)))))

(in-theory (disable fp fy fg))

; case with one key per clause: an induction on it fixes nt to a constant
(defun case-each-keys (var ks body)
  (declare (xargs :mode :program))
  (if (atom ks) nil (cons (list (list 'eq var (car ks)) body) (case-each-keys var (cdr ks) body))))
(defun case-each-cls (var cls)
  (declare (xargs :mode :program))
  (cond ((atom cls) nil)
        ((eq (caar cls) 'otherwise) (list (list 't (cadar cls))))
        (t (append (case-each-keys var (if (consp (caar cls)) (caar cls) (list (caar cls))) (cadar cls))
                   (case-each-cls var (cdr cls))))))
(defmacro case-each (var &rest clauses) (cons 'cond (case-each-cls var clauses)))

; fg's recursion, each subtree with the tokens that follow it in the spelling
(defun fg-ind (nt x r)
  (declare (xargs :guard t :measure (fg-measure nt x) :verify-guards nil
                  :hints (("Goal" :in-theory (enable kadr kaddr kadddr)))))
  (if (atom x) (list nt r)
    (case-each nt
      ((:expr :equiv :or :add)
       (list (fg-ind (lev-sub nt) (car x) (append (fy (lev-rest nt) (kadr x)) r))
             (fg-ind (lev-rest nt) (kadr x) r)))
      ((:expr* :equiv* :or* :l2* :add*)
       (list (fg-ind (lev-sub nt) (kadr (car x)) (append (fy nt (cdr x)) r))
             (fg-ind nt (cdr x) r)))
      (:and (fg-ind :l4 (kadr x) r))
      (:l4 (list (fg-ind :l2 (car x) (if (kadr x) (cons (kadr x) (append (fy :l2 (kaddr x)) r)) r))
                 (fg-ind :l2 (kaddr x) r)))
      (:l2 (list (fg-ind :add (kadr x) (append (fy :l2* (kaddr x)) r))
                 (fg-ind :l2* (kaddr x) r)))
      (:mult (list (fg-ind :prim (car x) (if (kadr x) (cons (op "**") (append (fy :mult (kadr x)) r)) r))
                   (fg-ind :mult (kadr x) r)))
      (:prim (case (car x)
               (:ref (fg-ind :args (kaddr x) r))
               (:paren (fg-ind :expr (kadr x) (cons (op ")") r)))
               (:acons (fg-ind :elist (kadr x) r))
               (otherwise nil)))
      ((:args :args*) (list (fg-ind :arg (car x) (append (fy :args* (cdr x)) r))
                            (fg-ind :args* (cdr x) r)))
      (:arg (case (car x)
              ((:kw) (fg-ind :expr (kaddr x) r))
              (:sub (fg-ind :expr (kadr x) r))
              (otherwise (list (fg-ind :expr (kadr x) (cons (op ":") (append (fy :tri* (kdr (kdr x))) r)))
                               (fg-ind :tri* (kdr (kdr x)) r)))))
      (:tri* (list (fg-ind :expr (car x) (if (kadr x) (cons (op ":") (append (fy :expr (kadr x)) r)) r))
                   (fg-ind :expr (kadr x) r)))
      ((:elist :elist*) (list (fg-ind :expr (car x) (append (fy :elist* (cdr x)) r))
                              (fg-ind :elist* (cdr x) r)))
      (otherwise nil))))

; what a tree's spelling begins with
(defun first-ok (nt x ys)
  (declare (xargs :guard t))
  (case nt
    ((:prim :mult :add) (and (consp ys) (prim-start-p (car ys))))
    ((:l2 :l4) (and (consp ys) (or (prim-start-p (car ys)) (and (member-equal (car ys) *add-ops*) t))))
    ((:and :or :equiv :expr) (and (consp ys) (start-tok-p (car ys))))
    ((:expr* :equiv* :or* :l2* :add*)
     (if (consp x) (and (consp ys) (member-equal (car ys) (lev-ops nt)) t) (null ys)))
    (:arg (and (consp ys) (or (start-tok-p (car ys)) (equal (car ys) '(:op ":")))))
    (:args* (and (consp ys) (member-equal (car ys) '((:op ",") (:op ")"))) t))
    (:elist* (and (consp ys) (member-equal (car ys) '((:op ",") (:op "]"))) t))
    (otherwise t)))

(defthm fy-first
  (implies (fg nt x) (first-ok nt x (fy nt x)))
  :hints (("Goal" :induct (fg-ind nt x nil))))

; fy-first's facts, one rule per nt, in the forms the proofs below meet
(defmacro fy-first-at (nt concl)
  `(defthm ,(packn (list 'fy-first- nt))
     (implies (fg ,nt x) ,concl)
     :hints (("Goal" :use ((:instance fy-first (nt ,nt))) :in-theory (disable fy-first)))))
(fy-first-at :prim (and (consp (fy :prim x)) (prim-start-p (car (fy :prim x)))))
(fy-first-at :mult (and (consp (fy :mult x)) (prim-start-p (car (fy :mult x)))))
(fy-first-at :add (and (consp (fy :add x)) (prim-start-p (car (fy :add x)))))
(fy-first-at :l2 (and (consp (fy :l2 x)) (or (prim-start-p (car (fy :l2 x))) (member-equal (car (fy :l2 x)) *add-ops*))))
(fy-first-at :l4 (and (consp (fy :l4 x)) (or (prim-start-p (car (fy :l4 x))) (member-equal (car (fy :l4 x)) *add-ops*))))
(fy-first-at :and (and (consp (fy :and x)) (start-tok-p (car (fy :and x)))))
(fy-first-at :or (and (consp (fy :or x)) (start-tok-p (car (fy :or x)))))
(fy-first-at :equiv (and (consp (fy :equiv x)) (start-tok-p (car (fy :equiv x)))))
(fy-first-at :expr (and (consp (fy :expr x)) (start-tok-p (car (fy :expr x)))))
(fy-first-at :arg (and (consp (fy :arg x)) (or (start-tok-p (car (fy :arg x))) (equal (car (fy :arg x)) '(:op ":")))))
(fy-first-at :args* (and (consp (fy :args* x)) (member-equal (car (fy :args* x)) '((:op ",") (:op ")")))))
(fy-first-at :elist* (and (consp (fy :elist* x)) (member-equal (car (fy :elist* x)) '((:op ",") (:op "]")))))
(defmacro fy-first-lev (nt)
  `(defthm ,(packn (list 'fy-first- nt))
     (implies (fg ,nt x)
              (and (iff (consp (fy ,nt x)) (consp x))
                   (implies (consp x) (member-equal (car (fy ,nt x)) (lev-ops ,nt)))))
     :hints (("Goal" :use ((:instance fy-first (nt ,nt))) :in-theory (disable fy-first)))))
(fy-first-lev :expr*)
(fy-first-lev :equiv*)
(fy-first-lev :or*)
(fy-first-lev :l2*)
(fy-first-lev :add*)


; ---- fp-complete
;
; A level's list of (op operand) after a whole tree: empty, when what
; follows does not continue it.
(defthm fp-rest-empty
  (implies (and (member-eq nt '(:expr* :equiv* :or* :l2* :add*)) (follow-ok nt r))
           (equal (fp nt r) (mv t nil r)))
  :hints (("Goal" :expand ((:free (nt) (fp nt r))) :in-theory (enable member-equal))))

(defthm equal-pair
  (implies (and (consp x) (true-listp (cdr x)) (equal (len (cdr x)) 1))
           (equal (equal x (list a b)) (and (equal (car x) a) (equal (cadr x) b))))
  :hints (("Goal" :expand ((len (cdr x)) (len (cddr x)) (true-listp (cdr x)) (true-listp (cddr x))))))

(defthm equal-triple
  (implies (and (consp x) (consp (cdr x)) (true-listp (cddr x)) (equal (len (cddr x)) 1))
           (equal (equal (list a b c) x) (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c))))
  :hints (("Goal" :expand ((len (cddr x)) (len (cdddr x)) (true-listp (cddr x)) (true-listp (cdddr x))))))

; an argument's spelling does not begin with the ")" that would end the list
(defthm fy-arg-not-close
  (implies (fg :arg x) (not (equal (car (fy :arg x)) '(:op ")"))))
  :hints (("Goal" :use ((:instance fy-first (nt :arg))) :in-theory (e/d (start-tok-p) (fy-first)))))

(defthm fp-tri*-empty
  (implies (follow-ok :tri* r) (equal (fp :tri* r) (mv t (list nil nil) r)))
  :hints (("Goal" :expand ((fp :tri* r)) :use ((:instance follow-arg-closers (nt :tri*)))
           :in-theory (enable member-equal))))

; fp opens on a constant nt and tokens that are a cons, or the spelling
; of a tree of another nt: not on (append (fy 'nt t) r), the calls the
; induction hypotheses answer, nor on unknown tokens.
(make-event
 `(defthm fp-open
    (implies (syntaxp (and (quotep nt) (consp toks)
                           (or (eq (car toks) 'cons)
                               (and (eq (car toks) 'binary-append)
                                    (consp (cadr toks)) (eq (car (cadr toks)) 'fy)
                                    (not (equal (cadr (cadr toks)) nt))))))
             (equal (fp nt toks) ,(body 'fp nil (w state))))
    :hints (("Goal" :expand ((fp nt toks))))))

; where ACL2's heuristics decline fp-open (too many IFs), a stable goal
; expands the same calls by hint
(mutual-recursion
 (defun fp-open-terms (term)
   (declare (xargs :mode :program))
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((and (eq (car term) 'fp) (quotep (cadr term)) (consp (caddr term))
               (or (eq (car (caddr term)) 'cons)
                   (and (eq (car (caddr term)) 'binary-append) (consp (cadr (caddr term)))
                        (eq (car (cadr (caddr term))) 'fy)
                        (not (equal (cadr (cadr (caddr term))) (cadr term))))))
          (cons term (fp-open-terms-lst (cdr term))))
         (t (fp-open-terms-lst (cdr term)))))
 (defun fp-open-terms-lst (ts)
   (declare (xargs :mode :program))
   (if (atom ts) nil (append (fp-open-terms (car ts)) (fp-open-terms-lst (cdr ts))))))

(defun fp-open-hint (clause stable)
  (declare (xargs :mode :program))
  (and stable (let ((ts (fp-open-terms-lst clause))) (and ts `(:expand ,ts)))))

(defthm kw-head-p-cons
  (equal (kw-head-p (cons a b)) (and (name-tok-p a) (consp b) (equal (car b) (op "=")))))

; membership in the operator lists stays closed: each fact the proof needs
; is a hypothesis (the tree's operator) or follow-decisions
(in-theory (disable kw-head-p member-equal))

; the trees that are atoms: the empty lists
(defthm fg-atom
  (implies (and (atom x) (fg nt x))
           (member-equal nt '(:expr* :equiv* :or* :l2* :add* :args :args* :elist*)))
  :rule-classes nil
  :hints (("Goal" :expand ((fg nt x)) :in-theory (enable member-equal))))

(defthm fp-complete-atom
  (implies (and (atom x) (fg nt x) (follow-ok nt r))
           (and (equal (fp nt (append (fy nt x) r)) (mv t x r))
                (not (member-eq nt '(:prim :mult :add :l2 :l4 :and :or :equiv :expr)))))
  :hints (("Goal" :use fg-atom :in-theory (enable member-equal))))

(defthm fp-complete
  (implies (and (fg nt x) (follow-ok nt r))
           (and (equal (fp nt (append (fy nt x) r)) (mv t x r))
                (implies (member-eq nt '(:prim :mult :add :l2 :l4 :and :or :equiv :expr))
                         (not (kw-head-p (append (fy nt x) r))))))
  :hints (("Goal" :induct (fg-ind nt x r)) (fp-open-hint clause stable-under-simplificationp)))

; ---- fp-cost: the parser is linear
;
; fp-steps counts the calls fp makes: fp's own recursion, each answer
; 1 plus the counts of the calls it made, each call let-bound under the
; tests that govern it. It is generated from fp by mksteps.bb (bb
; mksteps.bb fparse.lisp fp fp-steps) and pasted here. A successful parse
; makes at most 32 calls per token it consumes, plus fp-d nt; with
; fp-complete, a sentence of n tokens is read in at most 32n + 17 calls.

(in-theory (enable member-equal))
(defun
 fp-steps
 (nt toks)
 (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fp-rank nt)) :verify-guards nil))
 (let
  ((tk (kar toks)))
  (case
   nt
   ((:expr :equiv :or :add)
    (mv-let
     (ok a r)
     (fp (lev-sub nt) toks)
     (declare (ignorable ok a r))
     (let
      ((c1 (fp-steps (lev-sub nt) toks)))
      (if
       (not (and ok (<= (len r) (len toks))))
       (+ 1 c1)
       (mv-let
        (ok2 rest r2)
        (fp (lev-rest nt) r)
        (declare (ignorable ok2 rest r2))
        (let ((c2 (fp-steps (lev-rest nt) r))) (if ok2 (+ 1 c2 c1) (+ 1 c2 c1))))))))
   ((:expr* :equiv* :or* :l2* :add*)
    (if
     (and (consp toks) (member-equal tk (lev-ops nt)))
     (mv-let
      (ok a r)
      (fp (lev-sub nt) (cdr toks))
      (declare (ignorable ok a r))
      (let
       ((c3 (fp-steps (lev-sub nt) (cdr toks))))
       (if
        (not (and ok (<= (len r) (len (cdr toks)))))
        (+ 1 c3)
        (mv-let
         (ok2 rest r2)
         (fp nt r)
         (declare (ignorable ok2 rest r2))
         (let ((c4 (fp-steps nt r))) (if ok2 (+ 1 c4 c3) (+ 1 c4 c3)))))))
     (+ 1)))
   (:and
    (if
     (and (consp toks) (equal tk (op ".not.")))
     (mv-let
      (ok a r)
      (fp :l4 (cdr toks))
      (declare (ignorable ok a r))
      (let ((c5 (fp-steps :l4 (cdr toks)))) (if ok (+ 1 c5) (+ 1 c5))))
     (mv-let
      (ok a r)
      (fp :l4 toks)
      (declare (ignorable ok a r))
      (let ((c6 (fp-steps :l4 toks))) (if ok (+ 1 c6) (+ 1 c6))))))
   (:l4
    (mv-let
     (ok a r)
     (fp :l2 toks)
     (declare (ignorable ok a r))
     (let
      ((c7 (fp-steps :l2 toks)))
      (cond
       ((not (and ok (<= (len r) (len toks)))) (+ 1 c7))
       ((and (consp r) (member-equal (car r) *rel-ops*))
        (mv-let
         (ok2 b r2)
         (fp :l2 (cdr r))
         (declare (ignorable ok2 b r2))
         (let ((c8 (fp-steps :l2 (cdr r)))) (if ok2 (+ 1 c8 c7) (+ 1 c8 c7)))))
       (t (+ 1 c7))))))
   (:l2
    (let*
     ((sign (if (and (consp toks) (member-equal tk *add-ops*)) tk nil)) (t1 (if sign (cdr toks) toks)))
     (mv-let
      (ok a r)
      (fp :add t1)
      (declare (ignorable ok a r))
      (let
       ((c9 (fp-steps :add t1)))
       (if
        (not (and ok (<= (len r) (len t1))))
        (+ 1 c9)
        (mv-let
         (ok2 rest r2)
         (fp :l2* r)
         (declare (ignorable ok2 rest r2))
         (let ((c10 (fp-steps :l2* r))) (if ok2 (+ 1 c10 c9) (+ 1 c10 c9)))))))))
   (:mult
    (mv-let
     (ok a r)
     (fp :prim toks)
     (declare (ignorable ok a r))
     (let
      ((c11 (fp-steps :prim toks)))
      (cond
       ((not (and ok (<= (len r) (len toks)))) (+ 1 c11))
       ((and (consp r) (equal (car r) (op "**")))
        (mv-let
         (ok2 b r2)
         (fp :mult (cdr r))
         (declare (ignorable ok2 b r2))
         (let ((c12 (fp-steps :mult (cdr r)))) (if ok2 (+ 1 c12 c11) (+ 1 c12 c11)))))
       (t (+ 1 c11))))))
   (:prim
    (cond
     ((not (consp toks)) (+ 1))
     ((lit-tok-p tk) (+ 1))
     ((xname-tok-p tk)
      (if
       (and (consp (cdr toks)) (equal (cadr toks) (op "(")))
       (mv-let
        (ok as r)
        (fp :args (cddr toks))
        (declare (ignorable ok as r))
        (let ((c13 (fp-steps :args (cddr toks)))) (if ok (+ 1 c13) (+ 1 c13))))
       (+ 1)))
     ((equal tk (op "("))
      (mv-let
       (ok e r)
       (fp :expr (cdr toks))
       (declare (ignorable ok e r))
       (let
        ((c14 (fp-steps :expr (cdr toks))))
        (if (and ok (consp r) (equal (car r) (op ")"))) (+ 1 c14) (+ 1 c14)))))
     ((equal tk (op "["))
      (mv-let
       (ok es r)
       (fp :elist (cdr toks))
       (declare (ignorable ok es r))
       (let ((c15 (fp-steps :elist (cdr toks)))) (if ok (+ 1 c15) (+ 1 c15)))))
     (t (+ 1))))
   ((:args :args*)
    (cond
     ((not (consp toks)) (+ 1))
     ((equal tk (op ")")) (+ 1))
     ((and (eq nt :args*) (not (equal tk (op ",")))) (+ 1))
     (t
      (let
       ((t1 (if (eq nt :args) toks (cdr toks))))
       (mv-let
        (ok a r)
        (fp :arg t1)
        (declare (ignorable ok a r))
        (let
         ((c16 (fp-steps :arg t1)))
         (if
          (not (and ok (<= (len r) (len t1))))
          (+ 1 c16)
          (mv-let
           (ok2 as r2)
           (fp :args* r)
           (declare (ignorable ok2 as r2))
           (let ((c17 (fp-steps :args* r))) (if ok2 (+ 1 c17 c16) (+ 1 c17 c16)))))))))))
   (:arg
    (cond
     ((not (consp toks)) (+ 1))
     ((kw-head-p toks)
      (mv-let
       (ok e r)
       (fp :expr (cddr toks))
       (declare (ignorable ok e r))
       (let ((c18 (fp-steps :expr (cddr toks)))) (if ok (+ 1 c18) (+ 1 c18)))))
     ((equal tk (op ":"))
      (mv-let
       (ok hs r)
       (fp :tri* (cdr toks))
       (declare (ignorable ok hs r))
       (let ((c19 (fp-steps :tri* (cdr toks)))) (if ok (+ 1 c19) (+ 1 c19)))))
     (t
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c20 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c20))
         ((and (consp r) (equal (car r) (op ":")))
          (mv-let
           (ok2 hs r2)
           (fp :tri* (cdr r))
           (declare (ignorable ok2 hs r2))
           (let ((c21 (fp-steps :tri* (cdr r)))) (if ok2 (+ 1 c21 c20) (+ 1 c21 c20)))))
         (t (+ 1 c20))))))))
   (:tri*
    (mv-let
     (ok hi r)
     (if
      (or (atom toks) (member-equal tk (list (op ":") (op ",") (op ")"))))
      (mv t nil toks)
      (fp :expr toks))
     (declare (ignorable ok hi r))
     (let
      ((c22
        (if (or (atom toks) (member-equal tk (list (op ":") (op ",") (op ")")))) 0 (fp-steps :expr toks))))
      (cond
       ((not (and ok (<= (len r) (len toks)))) (+ 1 c22))
       ((and (consp r) (equal (car r) (op ":")))
        (mv-let
         (ok2 st r2)
         (fp :expr (cdr r))
         (declare (ignorable ok2 st r2))
         (let ((c23 (fp-steps :expr (cdr r)))) (if ok2 (+ 1 c23 c22) (+ 1 c23 c22)))))
       (t (+ 1 c22))))))
   (:elist
    (mv-let
     (ok e r)
     (fp :expr toks)
     (declare (ignorable ok e r))
     (let
      ((c24 (fp-steps :expr toks)))
      (if
       (not (and ok (<= (len r) (len toks))))
       (+ 1 c24)
       (mv-let
        (ok2 es r2)
        (fp :elist* r)
        (declare (ignorable ok2 es r2))
        (let ((c25 (fp-steps :elist* r))) (if ok2 (+ 1 c25 c24) (+ 1 c25 c24))))))))
   (:elist*
    (cond
     ((not (consp toks)) (+ 1))
     ((equal tk (op "]")) (+ 1))
     ((not (equal tk (op ","))) (+ 1))
     (t
      (mv-let
       (ok e r)
       (fp :expr (cdr toks))
       (declare (ignorable ok e r))
       (let
        ((c26 (fp-steps :expr (cdr toks))))
        (if
         (not (and ok (<= (len r) (len (cdr toks)))))
         (+ 1 c26)
         (mv-let
          (ok2 es r2)
          (fp :elist* r)
          (declare (ignorable ok2 es r2))
          (let ((c27 (fp-steps :elist* r))) (if ok2 (+ 1 c27 c26) (+ 1 c27 c26))))))))))
   (otherwise (+ 1)))))

(in-theory (disable member-equal))

(defun fp-d (nt)
  (declare (xargs :guard t))
  (case nt (:prim 1) (:mult 2) (:add 4) (:l2 6) (:l4 7) (:and 8) (:or 10) (:equiv 12) (:expr 14)
    ((:arg :tri*) 15) (:args 17) (:elist 16) (otherwise 1)))

(defthm fp-steps-natp (natp (fp-steps nt toks)) :rule-classes :type-prescription)

; each induction step expands exactly the calls its conclusion is about,
; (fp nt toks) and (fp-steps nt toks): the calls inside them are the ones
; its hypotheses answer
(defun case-nts (clause)             ; the step's nts: its hypothesis (eql nt c) or (member nt (c ...))
  (declare (xargs :mode :program))
  (cond ((atom clause) nil)
        ((and (consp (car clause)) (eq (caar clause) (quote not)) (consp (cadar clause))
              (eq (cadr (cadar clause)) (quote nt)) (quotep (caddr (cadar clause))))
         (cond ((member-eq (car (cadar clause)) (quote (eql equal))) (list (caddr (cadar clause))))
               ((member-eq (car (cadar clause)) (quote (member-equal member-eql member-eq)))
                (loop$ for c in (unquote (caddr (cadar clause))) collect (list (quote quote) c)))
               (t (case-nts (cdr clause)))))
        (t (case-nts (cdr clause)))))

(defun cost-step-hint (id clause)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :pool-lst) (quote (1)))
       (equal (len (access clause-id id :case-lst)) 1)
       (equal (access clause-id id :primes) 0)
       (let ((cs (case-nts clause)))
         (list :expand (append (quote ((fp nt toks) (fp-steps nt toks)))
                               (loop$ for c in cs append (list (list (quote fp) c (quote toks)) (list (quote fp-steps) c (quote toks)))))))))

; a successful parse makes at most 32 calls per token it consumes, plus
; fp-d nt: every call of a successful run succeeds, on its own tokens
(defthm fp-cost
  (implies (mv-nth 0 (fp nt toks))
           (<= (+ (fp-steps nt toks) (* 32 (len (mv-nth 2 (fp nt toks)))))
               (+ (* 32 (len toks)) (fp-d nt))))
  :hints (("Goal" :induct (fp-steps nt toks) :in-theory (enable member-equal)) (cost-step-hint id clause)))
