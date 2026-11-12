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
    (:base 0) (:part 1) (:parts 2) (:prim 1) (:mult 2) (:add 3) (:l2 4) (:l3 5) (:l4 6) (:and 7) (:or 8) (:equiv 9) (:expr 10)
    ((:arg :acv :tri* :ictl) 11) ((:args :elist :ilist) 12)
    (otherwise 1)))

; a keyword argument's head, name =
(defun kw-head-p (toks)
  (declare (xargs :guard t))
  (and (consp toks) (name-tok-p (car toks)) (consp (cdr toks)) (equal (cadr toks) (op "="))))

; R783's integer-type-spec :: before the variable: ": : name =", and
; "integer : : name =", "integer (", "integer ( kind ="
(defun int-tail-p (ts)
  (declare (xargs :guard t))
  (and (consp ts) (equal (car ts) (op ":")) (consp (cdr ts)) (equal (cadr ts) (op ":")) (kw-head-p (cddr ts))))
(defun int-dc-p (ts) (declare (xargs :guard t)) (and (consp ts) (equal (car ts) '(:name "integer")) (int-tail-p (cdr ts))))
(defun int-paren-p (ts)
  (declare (xargs :guard t))
  (and (consp ts) (equal (car ts) '(:name "integer")) (consp (cdr ts)) (equal (cadr ts) (op "("))))
(defun int-kind-p (ts)
  (declare (xargs :guard t))
  (and (int-paren-p ts) (kw-head-p (cddr ts)) (equal (caddr ts) '(:name "kind"))))

(defmacro fail () '(mv nil nil toks))

(defun fp (nt toks)
  (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fp-rank nt))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable int-tail-p int-dc-p int-paren-p int-kind-p kw-head-p)))))
  (let ((tk (kar toks)))
    (case nt
      ((:expr :equiv :or :l3 :add)
       (mv-let (ok a r) (fp (lev-sub nt) toks)
         (if (not (and ok (<= (len r) (len toks)))) (fail)
           (mv-let (ok2 rest r2) (fp (lev-rest nt) r)
             (if ok2 (mv t (list a rest) r2) (fail))))))
      ((:expr* :equiv* :or* :l3* :l2* :add*)
       (if (and (consp toks) (member-equal tk (lev-ops nt)))
           (mv-let (ok a r) (fp (lev-sub nt) (cdr toks))
             (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
               (mv-let (ok2 rest r2) (fp nt r)
                 (if ok2 (mv t (cons (list tk a) rest) r2) (fail)))))
         (mv t nil toks)))
      (:and (if (and (consp toks) (equal tk (op ".not.")))
                (mv-let (ok a r) (fp :l4 (cdr toks)) (if ok (mv t (list t a) r) (fail)))
              (mv-let (ok a r) (fp :l4 toks) (if ok (mv t (list nil a) r) (fail)))))
      (:l4 (mv-let (ok a r) (fp :l3 toks)
             (cond ((not (and ok (<= (len r) (len toks)))) (fail))
                   ((and (consp r) (member-equal (car r) *rel-ops*))
                    (mv-let (ok2 b r2) (fp :l3 (cdr r))
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
                    (mv-let (ok b r) (fp :base toks)
                      (cond ((not (and ok (< (len r) (len toks)))) (fail))
                            ; R911: a data-ref, part-ref % part-ref ...
                            ((and (consp r) (equal (car r) (op "%")) (member-eq (kar b) '(:name :ref)))
                             (mv-let (ok2 ps r2) (fp :parts r)
                               (if ok2 (mv t (list :dref b ps) r2) (fail))))
                            (t (mv t b r)))))
                   ((equal tk (op "("))
                    (mv-let (ok e r) (fp :expr (cdr toks))
                      (cond ((not (and ok (consp r))) (fail))
                            ((equal (car r) (op ")")) (mv t (list :paren e) (cdr r)))
                            ; R718: ( real-part , imag-part )
                            ((and (equal (car r) (op ",")) (cpart-p e) (<= (len r) (len (cdr toks))))
                             (mv-let (ok2 e2 r2) (fp :expr (cdr r))
                               (if (and ok2 (cpart-p e2) (consp r2) (equal (car r2) (op ")")))
                                   (mv t (list :cplx e e2) (cdr r2))
                                 (fail))))
                            (t (fail)))))
                   ((equal tk (op "["))
                    (mv-let (ok es r) (fp :elist (cdr toks))
                      (if ok (mv t (list :acons es) r) (fail))))
                   (t (fail))))
      ; a name, name ( list ), or an element's substring name ( list ) ( range )
      (:base (cond ((not (and (consp toks) (xname-tok-p tk))) (fail))
                   (t
                    (if (and (consp (cdr toks)) (equal (cadr toks) (op "(")))
                        (mv-let (ok as r) (fp :args (cddr toks))
                          (cond ((not ok) (fail))
                                ; R908: an array element's substring, name ( list ) ( range )
                                ((and (consp r) (equal (car r) (op "(")) (<= (len r) (len (cddr toks))))
                                 (mv-let (ok2 g r2) (fp :arg (cdr r))
                                   (if (and ok2 (eq (kar g) :tri) (null (kadddr g)) (consp r2) (equal (car r2) (op ")")))
                                       (mv t (list :sref tk as g) (cdr r2))
                                     (fail))))
                                (t (mv t (list :ref tk as) r))))
                      (mv t (list :name tk) (cdr toks))))))
      ; % name [( args )]
      (:part (cond ((not (and (consp toks) (equal tk (op "%")) (consp (cdr toks)) (xname-tok-p (cadr toks)))) (fail))
                   ((and (consp (cddr toks)) (equal (caddr toks) (op "(")))
                    (mv-let (ok as r) (fp :args (cdddr toks))
                      (if ok (mv t (list (cadr toks) t as) r) (fail))))
                   (t (mv t (list (cadr toks) nil nil) (cddr toks)))))
      (:parts (mv-let (ok a r) (fp :part toks)
                (cond ((not (and ok (< (len r) (len toks)))) (fail))
                      ((and (consp r) (equal (car r) (op "%")))
                       (mv-let (ok2 ps r2) (fp :parts r)
                         (if ok2 (mv t (cons a ps) r2) (fail))))
                      (t (mv t (list a) r)))))
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
      (:elist (mv-let (ok e r) (fp :acv toks)
                (if (not (and ok (<= (len r) (len toks)))) (fail)
                  (mv-let (ok2 es r2) (fp :elist* r)
                    (if ok2 (mv t (cons e es) r2) (fail))))))
      (:elist* (cond ((not (consp toks)) (fail))
                     ((equal tk (op "]")) (mv t nil (cdr toks)))
                     ((not (equal tk (op ","))) (fail))
                     (t (mv-let (ok e r) (fp :acv (cdr toks))
                          (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
                            (mv-let (ok2 es r2) (fp :elist* r)
                              (if ok2 (mv t (cons e es) r2) (fail))))))))
      ; an ac-value: "(" begins an ac-implied-do, anything else an expression
      (:acv (cond ((not (consp toks)) (fail))
                  ((equal tk (op "("))
                   (mv-let (ok il r) (fp :ilist (cdr toks))
                     (if ok (mv t (cons :ido il) r) (fail))))
                  (t (mv-let (ok e r) (fp :expr toks)
                       (if ok (mv t (list :e e) r) (fail))))))
      (:ilist (mv-let (ok v r) (fp :acv toks)
                (if (not (and ok (<= (len r) (len toks)))) (fail)
                  (mv-let (ok2 vs r2) (fp :ilist* r)
                    (if ok2 (mv t (cons v vs) r2) (fail))))))
      ; ", ac-value" and more, or the control ", [integer-type-spec ::] var = " :ictl
      (:ilist* (cond ((not (and (consp toks) (equal tk (op ",")))) (fail))
                     ((kw-head-p (cdr toks))
                      (mv-let (ok c r) (fp :ictl (cdddr toks))
                        (if ok (mv t (list* :ctl (cadr toks) c) r) (fail))))
                     ((int-dc-p (cdr toks))         ; , integer : : name =
                      (mv-let (ok c r) (fp :ictl (cddr (cddddr toks)))
                        (if ok (mv t (list* :ctl (list :int (car (cddddr toks)) nil) c) r) (fail))))
                     ((int-kind-p (cdr toks))       ; , integer ( kind = k ) : : name =
                      (mv-let (ok k r) (fp :expr (cdr (cddddr toks)))
                        (if (not (and ok (<= (len r) (len (cdr (cddddr toks)))) (consp r) (equal (car r) (op ")")) (int-tail-p (cdr r))))
                            (fail)
                          (mv-let (ok2 c r2) (fp :ictl (cdr (cddddr r)))
                            (if ok2 (mv t (list* :ctl (list :int (cadddr r) (list t k)) c) r2) (fail))))))
                     ((int-paren-p (cdr toks))      ; , integer ( k ) : : name =
                      (mv-let (ok k r) (fp :expr (cdddr toks))
                        (if (not (and ok (<= (len r) (len (cdddr toks))) (consp r) (equal (car r) (op ")")) (int-tail-p (cdr r))))
                            (fail)
                          (mv-let (ok2 c r2) (fp :ictl (cdr (cddddr r)))
                            (if ok2 (mv t (list* :ctl (list :int (cadddr r) (list nil k)) c) r2) (fail))))))
                     (t (mv-let (ok v r) (fp :acv (cdr toks))
                          (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
                            (mv-let (ok2 vs r2) (fp :ilist* r)
                              (if ok2 (mv t (cons v vs) r2) (fail))))))))
      ; an implied-do's limits, "lo , hi [, st] )"
      (:ictl (mv-let (ok lo r) (fp :expr toks)
               (if (not (and ok (<= (len r) (len toks)) (consp r) (equal (car r) (op ",")))) (fail)
                 (mv-let (ok2 hi r2) (fp :expr (cdr r))
                   (cond ((not (and ok2 (<= (len r2) (len (cdr r))) (consp r2))) (fail))
                         ((equal (car r2) (op ")")) (mv t (list lo hi nil) (cdr r2)))
                         ((equal (car r2) (op ","))
                          (mv-let (ok3 st r3) (fp :expr (cdr r2))
                            (if (and ok3 (consp r3) (equal (car r3) (op ")")))
                                (mv t (list lo hi st) (cdr r3))
                              (fail))))
                         (t (fail)))))))
      (otherwise (fail)))))

; R783's heads, closed: what each says of the tokens, and each on a cons
(defthm int-tail-p-fc
  (implies (int-tail-p ts)
           (and (consp ts) (equal (car ts) (op ":")) (consp (cdr ts)) (equal (cadr ts) (op ":"))
                (consp (cddr ts)) (name-tok-p (caddr ts)) (consp (cdddr ts)) (equal (cadddr ts) (op "="))))
  :rule-classes :forward-chaining)
(defthm int-dc-p-fc
  (implies (int-dc-p ts) (and (consp ts) (equal (car ts) '(:name "integer")) (int-tail-p (cdr ts))))
  :rule-classes :forward-chaining)
(defthm int-paren-p-fc
  (implies (int-paren-p ts) (and (consp ts) (equal (car ts) '(:name "integer")) (consp (cdr ts)) (equal (cadr ts) (op "("))))
  :rule-classes :forward-chaining)
(defthm int-kind-p-fc
  (implies (int-kind-p ts)
           (and (int-paren-p ts) (consp (cddr ts)) (equal (caddr ts) '(:name "kind"))
                (consp (cdddr ts)) (equal (cadddr ts) (op "="))))
  :rule-classes :forward-chaining)
(defthm int-heads-cons
  (and (equal (int-tail-p (cons a b)) (and (equal a (op ":")) (consp b) (equal (car b) (op ":")) (kw-head-p (cdr b))))
       (equal (int-dc-p (cons a b)) (and (equal a '(:name "integer")) (int-tail-p b)))
       (equal (int-paren-p (cons a b)) (and (equal a '(:name "integer")) (consp b) (equal (car b) (op "("))))
       (equal (int-kind-p (cons a b))
              (and (equal a '(:name "integer")) (consp b) (equal (car b) (op "(")) (kw-head-p (cdr b))
                   (equal (cadr b) '(:name "kind"))))))
(defthm int-heads-not
  (implies (not (equal (car ts) '(:name "integer")))
           (and (not (int-dc-p ts)) (not (int-paren-p ts)) (not (int-kind-p ts)))))
(in-theory (disable int-tail-p int-dc-p int-paren-p int-kind-p))

(defthm fp-len
  (<= (len (mv-nth 2 (fp nt toks))) (len toks))
  :rule-classes :linear
  :hints (("Goal" :induct (fp nt toks) :in-theory (disable xname-tok-p name-tok-p lit-tok-p kw-head-p cpart-p int-tail-p int-dc-p int-paren-p int-kind-p))
          (and stable-under-simplificationp
               '(:expand ((fp :prim toks) (fp :base toks) (fp :part toks) (fp :parts toks) (fp :ilist* toks) (fp :ictl toks))))))

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

(in-theory (disable name-tok-p xname-tok-p lit-tok-p prim-start-p start-tok-p cpart-p))

; INTEGER, a keyword, begins no expression (R783 decides on it)
(defthm start-not-integer (implies (start-tok-p tk) (not (equal tk (quote (:name "integer")))))
  :hints (("Goal" :in-theory (enable start-tok-p xname-tok-p name-tok-p lit-tok-p))))

(defthm append-assoc-fp (equal (append (append a b) c) (append a (append b c))))
(defthm len-append-fp (equal (len (append a b)) (+ (len a) (len b))))
(defthm car-append-fp (equal (car (append a b)) (if (consp a) (car a) (car b))))
(defthm consp-append-fp (equal (consp (append a b)) (or (consp a) (consp b))))
(defthm cons-car-cdr-fp (implies (and (consp r) (equal (car r) a)) (equal (cons a (cdr r)) r)))
(defthm fg-tri*-shape (implies (fg :tri* x) (and (true-listp x) (equal (len x) 2))))

; ---- fp-sound

; a :base tree is a primary of the same spelling
(defthm fg-prim-of-base
  (implies (fg :base x) (and (fg :prim x) (equal (fy :prim x) (fy :base x))))
  :hints (("Goal" :expand ((fg :base x) (fg :prim x) (fy :prim x)))))

; an ac-value is a cons: never the :ctl that ends an :ilist*
(defthm fg-acv-consp
  (implies (fg :acv x) (consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((fg :acv x)))))

(defthm fp-sound
  (implies (mv-nth 0 (fp nt toks))
           (and (fg nt (mv-nth 1 (fp nt toks)))
                (equal (append (fy nt (mv-nth 1 (fp nt toks))) (mv-nth 2 (fp nt toks))) toks)))
  :hints (("Goal" :induct (fp nt toks))
          (and stable-under-simplificationp '(:expand ((fp :prim toks))))))

; ---- toward fp-complete: the follow sets

(defun cont-sub-p (b a)           ; every continuer of b continues a
  (declare (xargs :guard t))
  (and (member-equal (list a b)
                     '((:expr :equiv) (:expr :expr*) (:expr* :equiv) (:equiv :or) (:equiv :equiv*)
                       (:equiv* :or) (:or :and) (:or :or*) (:or* :and) (:and :l4) (:l4 :l3)
                       (:l3 :l2) (:l3 :l3*) (:l3* :l2) (:l2 :add) (:l2 :l2*) (:l2* :add) (:add :mult) (:add :add*) (:add* :mult)
                       (:mult :prim) (:mult :mult) (:prim :base) (:prim :parts) (:parts :part) (:arg :expr) (:tri* :expr) (:arg :tri*)))
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
       (implies (member-equal tk *rel-ops*) (not (cont-tok-p :l3 tk)))
       (implies (member-equal tk *concat-ops*) (not (cont-tok-p :l2 tk)))
       (implies (member-equal tk *add-ops*) (not (cont-tok-p :add tk)))
       (implies (member-equal tk *mult-ops*) (not (cont-tok-p :mult tk))))
  :hints (("Goal" :in-theory (enable cont-tok-p))))

; the parser's decisions after a whole tree, when what follows does not continue it
(defthm follow-decisions
  (implies (and (consp r) (follow-ok nt r))
           (and (implies (member-eq nt '(:expr :expr*)) (not (member-equal (car r) *eqv-ops*)))
                (implies (member-eq nt '(:equiv :equiv*)) (not (member-equal (car r) *or-ops*)))
                (implies (member-eq nt '(:or :or*)) (not (member-equal (car r) *and-ops*)))
                (implies (member-eq nt '(:l2 :l2* :l3 :l3* :l4 :and)) (not (member-equal (car r) *add-ops*)))
                (implies (member-eq nt '(:l3 :l3* :l4 :and)) (not (member-equal (car r) *concat-ops*)))
                (implies (member-eq nt '(:l4 :and)) (not (member-equal (car r) *rel-ops*)))
                (implies (member-eq nt '(:add :add*)) (not (member-equal (car r) *mult-ops*)))
                (implies (member-eq nt '(:mult :add :add* :l2 :l2* :l3 :l3* :l4 :and :or :or* :equiv :equiv* :expr :expr*))
                         (not (equal (car r) '(:op "**"))))
                (implies (member-eq nt '(:prim :base :mult :add :add* :l2 :l2* :l3 :l3* :l4 :and :or :or* :equiv :equiv* :expr :expr* :arg :tri*))
                         (and (not (equal (car r) '(:op "("))) (not (equal (car r) '(:op "=")))))
                (implies (member-eq nt '(:prim :parts :mult :add :add* :l2 :l2* :l3 :l3* :l4 :and :or :or* :equiv :equiv* :expr :expr*))
                         (not (equal (car r) '(:op "%"))))
                (implies (member-eq nt '(:part :parts)) (not (equal (car r) '(:op "("))))
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
  (implies (member-eq nt '(:args :args* :elist :elist* :ilist :ilist* :ictl)) (follow-ok nt r))
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
  (implies (member-eq nt '(:args :args* :elist :elist* :ilist :ilist* :ictl)) (follow-ok nt r))
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

; an ac-value's expression is followed as an expression is
(defthm follow-acv
  (equal (follow-ok :acv r) (follow-ok :expr r))
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
                (not (equal nt :l3)) (not (equal nt :l3*))
                (not (equal nt :mult)) (not (equal nt :prim)) (not (equal nt :base)) (not (equal nt :part)) (not (equal nt :parts)) (not (equal nt :args)) (not (equal nt :args*))
                (not (equal nt :arg)) (not (equal nt :tri*)) (not (equal nt :elist)) (not (equal nt :elist*))
                (not (equal nt :acv)) (not (equal nt :ilist)) (not (equal nt :ilist*)) (not (equal nt :ictl)))
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
      ((:expr :equiv :or :l3 :add)
       (list (fg-ind (lev-sub nt) (car x) (append (fy (lev-rest nt) (kadr x)) r))
             (fg-ind (lev-rest nt) (kadr x) r)))
      ((:expr* :equiv* :or* :l3* :l2* :add*)
       (list (fg-ind (lev-sub nt) (kadr (car x)) (append (fy nt (cdr x)) r))
             (fg-ind nt (cdr x) r)))
      (:and (fg-ind :l4 (kadr x) r))
      (:l4 (list (fg-ind :l3 (car x) (if (kadr x) (cons (kadr x) (append (fy :l3 (kaddr x)) r)) r))
                 (fg-ind :l3 (kaddr x) r)))
      (:l2 (list (fg-ind :add (kadr x) (append (fy :l2* (kaddr x)) r))
                 (fg-ind :l2* (kaddr x) r)))
      (:mult (list (fg-ind :prim (car x) (if (kadr x) (cons (op "**") (append (fy :mult (kadr x)) r)) r))
                   (fg-ind :mult (kadr x) r)))
      (:prim (case (car x)
               ((:name :ref :sref) (fg-ind :base x r))
               ; cadr, not kadr: the hypotheses then match prim-as-dref's terms
               (:dref (list (fg-ind :base (cadr x) (append (fy :parts (caddr x)) r))
                            (fg-ind :parts (caddr x) r)))
               (:paren (fg-ind :expr (kadr x) (cons (op ")") r)))
               (:cplx (list (fg-ind :expr (kadr x) (cons (op ",") (append (fy :expr (kaddr x)) (cons (op ")") r))))
                            (fg-ind :expr (kaddr x) (cons (op ")") r))))
               (:acons (fg-ind :elist (kadr x) r))
               (otherwise nil)))
      (:part (fg-ind :args (kaddr x) r))
      (:parts (list (fg-ind :part (car x) (append (fy :parts (cdr x)) r))
                    (fg-ind :parts (cdr x) r)))
      (:base (case (car x)
               (:ref (fg-ind :args (kaddr x) r))
               (:sref (list (fg-ind :args (kaddr x) (cons (op "(") (append (fy :arg (kadddr x)) (cons (op ")") r))))
                            (fg-ind :arg (kadddr x) (cons (op ")") r))))
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
      ((:elist :elist*) (list (fg-ind :acv (car x) (append (fy :elist* (cdr x)) r))
                              (fg-ind :elist* (cdr x) r)))
      (:acv (if (eq (car x) :ido) (fg-ind :ilist (cdr x) r) (fg-ind :expr (kadr x) r)))
      (:ilist (list (fg-ind :acv (car x) (append (fy :ilist* (cdr x)) r))
                    (fg-ind :ilist* (cdr x) r)))
      (:ilist* (if (eq (car x) :ctl)
                   (list (fg-ind :ictl (cddr x) r)
                         (fg-ind :expr (kadr (kaddr (cadr x)))
                                 (list* (op ")") (op ":") (op ":") (kadr (cadr x)) (op "=") (append (fy :ictl (cddr x)) r))))
                 (list (fg-ind :acv (car x) (append (fy :ilist* (cdr x)) r))
                       (fg-ind :ilist* (cdr x) r))))
      (:ictl (let ((st (kaddr x)) (cl (cons (op ")") r)))
               (list (fg-ind :expr (car x) (cons (op ",") (append (fy :expr (kadr x)) (if st (cons (op ",") (append (fy :expr st) cl)) cl))))
                     (fg-ind :expr (kadr x) (if st (cons (op ",") (append (fy :expr st) cl)) cl))
                     (fg-ind :expr st cl))))
      (otherwise nil))))

; what a tree's spelling begins with
(defun first-ok (nt x ys)
  (declare (xargs :guard t))
  (case nt
    ((:prim :mult :add) (and (consp ys) (prim-start-p (car ys))))
    (:base (and (consp ys) (xname-tok-p (car ys))))
    ((:part :parts) (and (consp ys) (equal (car ys) '(:op "%"))))
    ((:l2 :l3 :l4) (and (consp ys) (or (prim-start-p (car ys)) (and (member-equal (car ys) *add-ops*) t))))
    ((:and :or :equiv :expr) (and (consp ys) (start-tok-p (car ys))))
    ((:expr* :equiv* :or* :l3* :l2* :add*)
     (if (consp x) (and (consp ys) (member-equal (car ys) (lev-ops nt)) t) (null ys)))
    (:arg (and (consp ys) (or (start-tok-p (car ys)) (equal (car ys) '(:op ":")))))
    (:args* (and (consp ys) (member-equal (car ys) '((:op ",") (:op ")"))) t))
    (:elist* (and (consp ys) (member-equal (car ys) '((:op ",") (:op "]"))) t))
    ((:acv :ilist) (and (consp ys) (start-tok-p (car ys))))
    (:ilist* (and (consp ys) (equal (car ys) '(:op ","))))
    (otherwise t)))

(defthm fy-first
  (implies (fg nt x) (first-ok nt x (fy nt x)))
  :hints (("Goal" :induct (fg-ind nt x nil))))

; fy-first's facts, one rule per nt, in the forms the proofs below meet
(defmacro fy-first-at (nt concl)
  `(defthm ,(packn (list 'fy-first- nt))
     (implies (fg ,nt x) ,concl)
     :hints (("Goal" :use ((:instance fy-first (nt ,nt))) :in-theory (disable fy-first)))))
(fy-first-at :base (and (consp (fy :base x)) (xname-tok-p (car (fy :base x)))))
(fy-first-at :parts (and (consp (fy :parts x)) (equal (car (fy :parts x)) '(:op "%"))))
(fy-first-at :prim (and (consp (fy :prim x)) (prim-start-p (car (fy :prim x)))))
(fy-first-at :mult (and (consp (fy :mult x)) (prim-start-p (car (fy :mult x)))))
(fy-first-at :add (and (consp (fy :add x)) (prim-start-p (car (fy :add x)))))
(fy-first-at :l2 (and (consp (fy :l2 x)) (or (prim-start-p (car (fy :l2 x))) (member-equal (car (fy :l2 x)) *add-ops*))))
(fy-first-at :l3 (and (consp (fy :l3 x)) (or (prim-start-p (car (fy :l3 x))) (member-equal (car (fy :l3 x)) *add-ops*))))
(fy-first-at :l4 (and (consp (fy :l4 x)) (or (prim-start-p (car (fy :l4 x))) (member-equal (car (fy :l4 x)) *add-ops*))))
(fy-first-at :and (and (consp (fy :and x)) (start-tok-p (car (fy :and x)))))
(fy-first-at :or (and (consp (fy :or x)) (start-tok-p (car (fy :or x)))))
(fy-first-at :equiv (and (consp (fy :equiv x)) (start-tok-p (car (fy :equiv x)))))
(fy-first-at :expr (and (consp (fy :expr x)) (start-tok-p (car (fy :expr x)))))
(fy-first-at :arg (and (consp (fy :arg x)) (or (start-tok-p (car (fy :arg x))) (equal (car (fy :arg x)) '(:op ":")))))
(fy-first-at :args* (and (consp (fy :args* x)) (member-equal (car (fy :args* x)) '((:op ",") (:op ")")))))
(fy-first-at :elist* (and (consp (fy :elist* x)) (member-equal (car (fy :elist* x)) '((:op ",") (:op "]")))))
(fy-first-at :acv (and (consp (fy :acv x)) (start-tok-p (car (fy :acv x)))))
(defmacro fy-first-lev (nt)
  `(defthm ,(packn (list 'fy-first- nt))
     (implies (fg ,nt x)
              (and (iff (consp (fy ,nt x)) (consp x))
                   (implies (consp x) (member-equal (car (fy ,nt x)) (lev-ops ,nt)))))
     :hints (("Goal" :use ((:instance fy-first (nt ,nt))) :in-theory (disable fy-first)))))
(fy-first-lev :expr*)
(fy-first-lev :equiv*)
(fy-first-lev :or*)
(fy-first-lev :l3*)
(fy-first-lev :l2*)
(fy-first-lev :add*)


; ---- fp-complete
;
; A level's list of (op operand) after a whole tree: empty, when what
; follows does not continue it.
(defthm fp-rest-empty
  (implies (and (member-eq nt '(:expr* :equiv* :or* :l3* :l2* :add*)) (follow-ok nt r))
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

(defthm equal-quad
  (implies (and (consp x) (consp (cdr x)) (consp (cddr x)) (true-listp (cdddr x)) (equal (len (cdddr x)) 1))
           (and (equal (equal (list a b c d) x)
                       (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d)))
                (equal (equal x (list a b c d))
                       (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d)))))
  :hints (("Goal" :expand ((len (cdddr x)) (len (cddddr x)) (true-listp (cdddr x)) (true-listp (cddddr x))))))

(defthm equal-quint                  ; an implied-do's control, (:ctl var lo hi st)
  (implies (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x)) (true-listp (cddddr x)) (equal (len (cddddr x)) 1))
           (equal (equal x (list a b c d e))
                  (and (equal (car x) a) (equal (cadr x) b) (equal (caddr x) c) (equal (cadddr x) d) (equal (car (cddddr x)) e))))
  :hints (("Goal" :expand ((len (cddddr x)) (len (cdr (cddddr x))) (true-listp (cddddr x)) (true-listp (cdr (cddddr x)))))))

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

; a data-ref is no keyword argument's head: a "%" or "(" follows its name
(defthm kw-head-base-parts
  (implies (and (fg :base b) (fg :parts p))
           (not (kw-head-p (append (fy :base b) (append (fy :parts p) r)))))
  :hints (("Goal" :expand ((fg :base b) (fy :base b)) :in-theory (enable kw-head-p))))

; a name, a part-ref or a substring is a primary as a :base, before
; fy-open and fg-open split the primary's forms
(defthm prim-as-base
  (implies (member-eq (car x) '(:name :ref :sref))
           (and (equal (fy :prim x) (fy :base x)) (equal (fg :prim x) (fg :base x))))
  :hints (("Goal" :expand ((fy :prim x) (fg :prim x)))))

; a data-ref is its base's spelling, then its parts'
(defthm prim-as-dref
  (implies (equal (car x) :dref)
           (equal (fy :prim x) (append (fy :base (cadr x)) (fy :parts (caddr x)))))
  :hints (("Goal" :expand ((fy :prim x)))))

(defthm len-fy-base
  (implies (fg :base x) (< 0 (len (fy :base x))))
  :rule-classes :linear
  :hints (("Goal" :use fy-first-base :in-theory (disable fy-first-base))))

; the trees that are atoms: the empty lists
(defthm fg-atom
  (implies (and (atom x) (fg nt x))
           (member-equal nt '(:expr* :equiv* :or* :l3* :l2* :add* :args :args* :elist*)))
  :rule-classes nil
  :hints (("Goal" :expand ((fg nt x)) :in-theory (enable member-equal))))

(defthm fp-complete-atom
  (implies (and (atom x) (fg nt x) (follow-ok nt r))
           (and (equal (fp nt (append (fy nt x) r)) (mv t x r))
                (not (member-eq nt '(:prim :mult :add :l2 :l3 :l4 :and :or :equiv :expr :acv)))))
  :hints (("Goal" :use fg-atom :in-theory (enable member-equal))))

(defthm fp-complete
  (implies (and (fg nt x) (follow-ok nt r))
           (and (equal (fp nt (append (fy nt x) r)) (mv t x r))
                (implies (member-eq nt '(:prim :mult :add :l2 :l3 :l4 :and :or :equiv :expr :acv))
                         (not (kw-head-p (append (fy nt x) r))))))
  :hints (("Goal" :induct (fg-ind nt x r)) (fp-open-hint clause stable-under-simplificationp)))

