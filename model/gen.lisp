; gen: clotran's ACL2-to-Fortran translation (clotran's scripts/acl2-fortran)
; as an ACL2 function, for its first slice (GEN.md): integer arithmetic,
; comparisons, if, let (lambda), calls among the translated functions, a
; case on an integer (SELECT CASE), and tail recursion as a loop. Its
; input is what ACL2 hands acl2-fortran -- each function's translated body
; (variables, quoted constants, if, lambda, calls) and formals; its output
; is fsyn's syntax, which fprint.clj prints as the generator's text
; (check-gen.bb compares the two). gen-proof.lisp proves the output means,
; under fsem, what the definition means under a-ev below.
;
; The source's meaning, a-ev: ACL2's own on integers and booleans, with an
; integer result outside int64 an error (:range), never a value -- the
; hypothesis "a-ev answers without an error" is what the guard proof (and
; the books' (the (signed-byte 64) ..) declarations) must give.

(in-package "ACL2")

(include-book "fsem")

; the translation runs in the ACL2 loop; its guards are not verified
(set-verify-guards-eagerness 0)

; ---- the source's meaning

(defun a-prim (op vs)
  (declare (xargs :guard t))
  (let ((a (kar vs)) (b (kadr vs)))
    (case op
      ((binary-+ binary-*)
       (if (and (integerp a) (integerp b))
           (let ((r (if (eq op 'binary-+) (+ a b) (* a b))))
             (if (int64p r) (mv nil r) (mv :range nil)))
         (mv :type nil)))
      (unary-- (if (integerp a) (if (int64p (- a)) (mv nil (- a)) (mv :range nil)) (mv :type nil)))
      (< (if (and (integerp a) (integerp b)) (mv nil (< a b)) (mv :type nil)))
      ((equal eql) (mv nil (equal a b)))
      (not (mv nil (not a)))
      (nfix (mv nil (nfix a)))
      (zp (mv nil (if (natp a) (equal a 0) t)))
      (natp (mv nil (natp a)))
      (integerp (mv nil (integerp a)))
      (implies (mv nil (implies a b)))
      (the-check (mv nil (kaddr vs)))
      (hide (mv nil a))
      (otherwise (mv :unknown nil)))))

; defs: ((fn formals body) ...); n: fuel, one per term node
(mutual-recursion
 (defun a-ev (x env defs n)
   (declare (xargs :guard t :measure (nfix n) :verify-guards nil))
   (cond ((zp n) (mv :fuel nil))
         ((symbolp x) (let ((b (lkp x env))) (if (consp b) (mv nil (cdr b)) (mv :unbound nil))))
         ((atom x) (mv :syntax nil))
         ((eq (car x) 'quote) (mv nil (kadr x)))
         ((eq (car x) 'if)
          (mv-let (e c) (a-ev (kadr x) env defs (1- n))
            (cond (e (mv e nil))
                  (c (a-ev (kaddr x) env defs (1- n)))
                  (t (a-ev (kadddr x) env defs (1- n))))))
         (t (mv-let (e vs) (a-ev-list (cdr x) env defs (1- n))
              (cond (e (mv e nil))
                    ((consp (car x))
                     (a-ev (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) defs (1- n)))
                    (t (let ((d (lkp (car x) defs)))
                         (if (consp d)
                             (a-ev (kaddr d) (pairlis$ (true-list-fix (kadr d)) vs) defs (1- n))
                           (a-prim (car x) vs)))))))))
 (defun a-ev-list (xs env defs n)
   (declare (xargs :guard t :measure (nfix n)))
   (cond ((zp n) (mv :fuel nil))
         ((atom xs) (mv nil nil))
         (t (mv-let (e v) (a-ev (car xs) env defs (1- n))
              (if e (mv e nil)
                (mv-let (e vs) (a-ev-list (cdr xs) env defs (1- n))
                  (if e (mv e nil) (mv nil (cons v vs))))))))))

; ---- names, as the generator makes them

(defun g-subst (cs any)
  ; '-' -> '_'; with any, every character but a-z 0-9
  (declare (xargs :guard (character-listp cs)))
  (if (endp cs) nil
    (cons (if (if any (not (or (and (char<= #\a (car cs)) (char<= (car cs) #\z)) (digit-char-p (car cs))))
                (eql (car cs) #\-))
              #\_ (car cs))
          (g-subst (cdr cs) any))))

(defun g-sym (s any)
  (declare (xargs :guard t))
  (coerce (g-subst (coerce (string-downcase (symbol-name (if (symbolp s) s 'x))) 'list) any) 'string))

; a formal x is the dummy x_; a temporary base_n
(defun g-formal (v) (declare (xargs :guard t)) (string-append (g-sym v nil) "_"))
(defun g-tmp (base n)
  (declare (xargs :guard t))
  (string-append (g-sym base t) (string-append "_" (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string))))

; ---- the translation's context and state
;
; em    the variables in scope: var -> (name . type), type :int64 or :logical
; cnt   the temporaries' counter; locs  the temporaries: ((name . type) ...)
; sigs  the functions: fn -> (formals rtype), rtype :int64 or :logical
; self  the function translated

(defun g-used (em-names locs) (declare (xargs :guard t)) (append em-names (strip-cars (true-list-fix locs))))

; -2^63 has no literal
(defun g-lit (k)
  (declare (xargs :guard t))
  (if (eql k *int64-min*) '(:sub (:neg (:huge)) (:int 1)) (list :int k)))

(defun g-quote (c)
  ; (mv err code type)
  (declare (xargs :guard t))
  (cond ((int64p c) (mv nil (g-lit c) :int64))
        ((eq c t) (mv nil '(:true) :logical))
        ((eq c nil) (mv nil '(:false) :logical))
        (t (mv :constant nil nil))))

(defun g-big (x)
  ; a quoted integer outside int64, else nil
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) 'quote) (integerp (kadr x)) (not (int64p (kadr x))) (kadr x)))

(defun g-unop (op c ty)
  ; (mv err code type) for a one-argument primitive of argument code c, type ty
  (declare (xargs :guard t))
  (case op
    (unary-- (if (eq ty :int64) (mv nil (list :neg c) :int64) (mv :type nil nil)))
    (not (if (eq ty :logical) (mv nil (list :not c) :logical) (mv :type nil nil)))
    (nfix (if (eq ty :int64) (mv nil (list :max '(:int 0) c) :int64) (mv :type nil nil)))
    (zp (if (eq ty :int64) (mv nil (list :le c '(:int 0)) :logical) (mv :type nil nil)))
    (natp (if (eq ty :int64) (mv nil (list :ge c '(:int 0)) :logical) (mv :type nil nil)))
    (integerp (if (eq ty :int64) (mv nil '(:true) :logical) (mv :type nil nil)))
    (hide (mv nil c ty))
    (otherwise (mv :unknown nil nil))))

(defun g-binop (op a ta b tb)
  (declare (xargs :guard t))
  (if (not (and (eq ta :int64) (eq tb :int64))) (mv :type nil nil)
    (case op
      (binary-+ (mv nil (list :add a b) :int64))
      (binary-* (mv nil (list :mul a b) :int64))
      ((equal eql) (mv nil (list :eq a b) :logical))
      (< (mv nil (list :lt a b) :logical))
      (otherwise (mv :unknown nil nil)))))

; ---- expressions: (mv err stmts code type cnt locs)
;
; The statements run first (an if's branches, a let's bindings, into
; temporaries), then the code is the value. A temporary's name is checked
; against every name in use; the generator's counter never repeats one.

(defun g-fresh (base ty cnt locs em-names)
  ; (mv err name cnt locs)
  (declare (xargs :guard t))
  (let ((nm (g-tmp base (1+ (nfix cnt)))))
    (if (or (equal nm "r") (member-equal nm (g-used em-names locs))) (mv :name nil cnt locs)
      (mv nil nm (1+ (nfix cnt)) (cons (cons nm ty) (true-list-fix locs))))))

(defun all-int64-types (ts)
  (declare (xargs :guard t))
  (if (atom ts) t (and (eq (car ts) :int64) (all-int64-types (cdr ts)))))

; an if as an expression: its value into a temporary, only the branch taken run
(defun g-if (sc cc tc sa ca ta sb cb tb cnt locs used)
  (declare (xargs :guard t))
  (if (not (and (eq tc :logical) (equal ta tb))) (mv :type nil nil nil cnt locs)
    (mv-let (e tmp cnt locs) (g-fresh 't ta cnt locs used)
      (if e (mv e nil nil nil cnt locs)
        (mv nil (append sc (list (list :if cc
                                       (append sa (list (list :assign (list :var tmp) ca)))
                                       (append sb (list (list :assign (list :var tmp) cb))))))
            (list :var tmp) ta cnt locs)))))

(defun em-names (em) (declare (xargs :guard t)) (if (atom em) nil (cons (kar (kdr (car em))) (em-names (cdr em)))))

(mutual-recursion
 (defun g-expr (x em cnt locs sigs fnames)
   ; fnames: the formals' names, always in use
   (declare (xargs :guard t :measure (acl2-count x) :verify-guards nil))
   (let ((used (append fnames (em-names em))))
     (cond
      ((symbolp x) (let ((b (lkp x em)))
                     (if (and (consp b) (consp (cdr b))) (mv nil nil (list :var (cadr b)) (cddr b) cnt locs)
                       (mv :unbound nil nil nil cnt locs))))
      ((atom x) (mv :syntax nil nil nil cnt locs))
      ((eq (car x) 'quote) (mv-let (e code ty) (g-quote (kadr x)) (mv e nil code ty cnt locs)))
      ((member-eq (car x) '(if implies))
       ; (implies a b) is (if a b t)
       (mv-let (e sc cc tc cnt locs) (g-expr (kadr x) em cnt locs sigs fnames)
         (if e (mv e nil nil nil cnt locs)
           (mv-let (e sa ca ta cnt locs) (g-expr (kaddr x) em cnt locs sigs fnames)
             (if e (mv e nil nil nil cnt locs)
               (mv-let (e sb cb tb cnt locs)
                 (if (eq (car x) 'if) (g-expr (kadddr x) em cnt locs sigs fnames)
                   (mv nil nil '(:true) :logical cnt locs))
                 (if (or e (not (true-listp x)) (not (= (len x) (if (eq (car x) 'if) 4 3))))
                     (mv (or e :syntax) nil nil nil cnt locs)
                   (g-if sc cc tc sa ca ta sb cb tb cnt locs used))))))))
      ; (< x big): known, the guard having made x an int64
      ((and (eq (car x) '<) (true-listp x) (= (len x) 3) (or (g-big (kadr x)) (g-big (kaddr x))))
       (let ((big (g-big (kadr x))))
         (mv-let (e s c ty cnt locs) (g-expr (if big (kaddr x) (kadr x)) em cnt locs sigs fnames)
           (declare (ignore c))
           (if (or e (not (eq ty :int64)) (and big (g-big (kaddr x)))) (mv (or e :type) nil nil nil cnt locs)
             (mv nil s (if (if big (< big *int64-min*) (> (g-big (kaddr x)) *int64-max*)) '(:true) '(:false))
                 :logical cnt locs)))))
      ((consp (car x))
       ; ((lambda vars body) . args): each var bound to a different term gets a temporary
       (let ((vars (kadr (car x))) (body (kaddr (car x))))
         (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                       (true-listp x) (= (len vars) (len (cdr x)))))
             (mv :syntax nil nil nil cnt locs)
           (mv-let (e s binds cnt locs) (g-binds vars (cdr x) em cnt locs sigs fnames)
             (if e (mv e nil nil nil cnt locs)
               (mv-let (e sb cb tb cnt locs) (g-expr body (append binds em) cnt locs sigs fnames)
                 (if e (mv e nil nil nil cnt locs)
                   (mv nil (append s sb) cb tb cnt locs))))))))
      ((eq (car x) 'the-check)
       ; (the-check g x y) is y: the guard proof discharged g
       (if (not (and (true-listp x) (= (len x) 4))) (mv :syntax nil nil nil cnt locs)
         (g-expr (kadddr x) em cnt locs sigs fnames)))
      (t
       (mv-let (e s cs ts cnt locs) (g-args (cdr x) em cnt locs sigs fnames)
         (cond (e (mv e nil nil nil cnt locs))
               ((not (true-listp x)) (mv :syntax nil nil nil cnt locs))
               ((consp (lkp (car x) sigs))
                (let ((sig (cdr (lkp (car x) sigs))))
                  (if (and (equal (len (kar sig)) (len cs)) (all-int64-types ts))
                      (mv nil s (list :fcall (g-sym (car x) nil) cs) (kadr sig) cnt locs)
                    (mv :type nil nil nil cnt locs))))
               ((= (len cs) 1) (mv-let (e c ty) (g-unop (car x) (car cs) (car ts)) (mv e s c ty cnt locs)))
               ((= (len cs) 2) (mv-let (e c ty) (g-binop (car x) (car cs) (car ts) (cadr cs) (cadr ts))
                                 (mv e s c ty cnt locs)))
               (t (mv :unknown nil nil nil cnt locs))))))))
 (defun g-args (xs em cnt locs sigs fnames)
   (declare (xargs :guard t :measure (acl2-count xs)))
   (if (atom xs) (mv nil nil nil nil cnt locs)
     (mv-let (e s c ty cnt locs) (g-expr (car xs) em cnt locs sigs fnames)
       (if e (mv e nil nil nil cnt locs)
         (mv-let (e ss cs ts cnt locs) (g-args (cdr xs) em cnt locs sigs fnames)
           (if e (mv e nil nil nil cnt locs)
             (mv nil (append s ss) (cons c cs) (cons ty ts) cnt locs)))))))
 (defun g-binds (vars xs em cnt locs sigs fnames)
   ; (mv err stmts binds cnt locs), binds the em entries of the new temporaries;
   ; every term read in the outer scope em
   (declare (xargs :guard t :measure (acl2-count xs)))
   (cond ((or (atom vars) (atom xs)) (mv nil nil nil cnt locs))
         ((eq (car vars) (car xs)) (g-binds (cdr vars) (cdr xs) em cnt locs sigs fnames))
         (t (mv-let (e s c ty cnt locs) (g-expr (car xs) em cnt locs sigs fnames)
              (if e (mv e nil nil cnt locs)
                (mv-let (e tmp cnt locs) (g-fresh (car vars) ty cnt locs (append fnames (em-names em)))
                  (if e (mv e nil nil cnt locs)
                    (mv-let (e ss binds cnt locs) (g-binds (cdr vars) (cdr xs) em cnt locs sigs fnames)
                      (if e (mv e nil nil cnt locs)
                        (mv nil (append s (list (list :assign (list :var tmp) c)) ss)
                            (cons (list* (car vars) tmp ty) binds) cnt locs)))))))))))

; ---- the tail call: new values for the formals, then CYCLE
;
; Every argument into a temporary first (a call's arguments are evaluated
; together), then the formals: (mv err stmts assigns cnt locs)
(defun g-tail (vars xs em cnt locs sigs fnames)
  (declare (xargs :guard t :measure (acl2-count xs) :verify-guards nil))
  (if (or (atom vars) (atom xs)) (mv nil nil nil cnt locs)
    (mv-let (e s c ty cnt locs) (g-expr (car xs) em cnt locs sigs fnames)
      (if (or e (not (eq ty :int64))) (mv (or e :type) nil nil cnt locs)
        (mv-let (e tmp cnt locs) (g-fresh (car vars) ty cnt locs (append fnames (em-names em)))
          (if e (mv e nil nil cnt locs)
            (mv-let (e ss as cnt locs) (g-tail (cdr vars) (cdr xs) em cnt locs sigs fnames)
              (if e (mv e nil nil cnt locs)
                (mv nil (append s (list (list :assign (list :var tmp) c)) ss)
                    (cons (list :assign (list :var (g-formal (car vars))) (list :var tmp)) as)
                    cnt locs)))))))))

; ---- a case on an integer: (if (equal v 'k1) a1 (if (equal v 'k2) a2 ... else)),
; one variable, distinct keys; three arms or more are a SELECT CASE

(defun g-intlit (k)
  (declare (xargs :guard t))
  (cond ((integerp k) k)
        ((and (consp k) (eq (car k) 'quote) (integerp (kadr k))) (kadr k))
        (t nil)))

(defun g-case-key (c)
  ; (mv var key), var nil when c is no such test
  (declare (xargs :guard t))
  (if (and (consp c) (member-eq (car c) '(equal eql =)) (true-listp c) (= (len c) 3))
      (let ((a (cadr c)) (b (caddr c)))
        (cond ((and a (symbolp a) (not (eq a t)) (g-intlit b)) (mv a (g-intlit b)))
              ((and b (symbolp b) (not (eq b t)) (g-intlit a)) (mv b (g-intlit a)))
              (t (mv nil nil))))
    (mv nil nil)))

(defun g-chain (x v keys)
  ; how many arms the case takes
  (declare (xargs :guard t))
  (if (and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4))
      (mv-let (kv k) (g-case-key (cadr x))
        (if (and kv (or (null v) (eq v kv)) (not (member-equal k keys)))
            (1+ (g-chain (cadddr x) kv (cons k keys)))
          0))
    0))

(defthm g-count-parts
  (implies (consp x)
           (and (< (acl2-count (cadr x)) (acl2-count x))
                (< (acl2-count (caddr x)) (acl2-count x))
                (< (acl2-count (cadddr x)) (acl2-count x))))
  :rule-classes :linear)

; ---- the body in return position: (mv err stmts cnt locs)

(mutual-recursion
 (defun g-ret (x em cnt locs self sigs fnames)
   (declare (xargs :guard t :measure (* 2 (acl2-count x)) :verify-guards nil
                   :hints (("Goal" :in-theory (disable g-case-key int-lit-p g-chain acl2-count)))))
   (cond
    ((and (consp x) (<= 3 (g-chain x nil nil)))
     (mv-let (v k) (g-case-key (cadr x))
       (let ((b (lkp v em)))
         (if (not (and (consp b) (consp (cdr b)) (eq (cddr b) :int64) (int-lit-p k)))
             (mv :type nil cnt locs)
           (mv-let (e sa cnt locs) (g-ret (caddr x) em cnt locs self sigs fnames)
             (if e (mv e nil cnt locs)
               (mv-let (e arms dflt cnt locs)
                 (g-select (cadddr x) (1- (g-chain x nil nil)) em cnt locs self sigs fnames)
                 (if e (mv e nil cnt locs)
                   (mv nil (list (list :select (list :var (cadr b)) (cons (list k sa) arms) dflt))
                       cnt locs)))))))))
    ((and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4))
     (mv-let (e sc cc tc cnt locs) (g-expr (cadr x) em cnt locs sigs fnames)
       (if (or e (not (eq tc :logical))) (mv (or e :type) nil cnt locs)
         (mv-let (e sa cnt locs) (g-ret (caddr x) em cnt locs self sigs fnames)
           (if e (mv e nil cnt locs)
             (mv-let (e sb cnt locs) (g-ret (cadddr x) em cnt locs self sigs fnames)
               (if e (mv e nil cnt locs)
                 (mv nil (append sc (list (list :if cc sa sb))) cnt locs))))))))
    ((and (consp x) (eq (car x) self))
     (let ((formals (kar (cdr (lkp self sigs)))))
       (if (not (and (true-listp x) (equal (len (cdr x)) (len formals)))) (mv :arity nil cnt locs)
         (mv-let (e s as cnt locs) (g-tail formals (cdr x) em cnt locs sigs fnames)
           (if e (mv e nil cnt locs)
             (mv nil (append s as (list '(:cycle))) cnt locs))))))
    (t (mv-let (e s c ty cnt locs) (g-expr x em cnt locs sigs fnames)
         (if (or e (not (equal ty (kadr (cdr (lkp self sigs)))))) (mv (or e :type) nil cnt locs)
           (mv nil (append s (list (list :assign '(:var "r") c) '(:return))) cnt locs))))))
 (defun g-select (x k em cnt locs self sigs fnames)
   ; (mv err arms default cnt locs): the case's next k arms from x, then its else
   (declare (xargs :guard t :measure (1+ (* 2 (acl2-count x)))))
   (if (zp k)
       (mv-let (e sb cnt locs) (g-ret x em cnt locs self sigs fnames)
         (mv e nil sb cnt locs))
     (if (not (and (consp x) (true-listp x) (= (len x) 4))) (mv :syntax nil nil cnt locs)
       (mv-let (v key) (g-case-key (cadr x))
         (declare (ignore v))
         (if (not (int-lit-p key)) (mv :constant nil nil cnt locs)
           (mv-let (e sa cnt locs) (g-ret (caddr x) em cnt locs self sigs fnames)
             (if e (mv e nil nil cnt locs)
               (mv-let (e arms dflt cnt locs) (g-select (cadddr x) (1- k) em cnt locs self sigs fnames)
                 (mv e (cons (list key sa) arms) dflt cnt locs))))))))))

; ---- a function

(defun g-has (a x)
  ; a occurs in the tree x
  (declare (xargs :guard t))
  (or (equal a x) (and (consp x) (or (g-has a (car x)) (g-has a (cdr x))))))

(defun g-fcalls (x)
  ; the functions an output tree references
  (declare (xargs :guard t))
  (if (atom x) nil
    (if (and (eq (car x) :fcall) (consp (cdr x)))
        (cons (cadr x) (g-fcalls (cddr x)))
      (append (g-fcalls (car x)) (g-fcalls (cdr x))))))

(defun g-calls (x defs)
  ; the defined functions a source term names
  (declare (xargs :guard t))
  (cond ((atom x) (if (and x (symbolp x) (consp (lkp x defs))) (list x) nil))
        ((eq (car x) 'quote) nil)
        (t (append (g-calls (car x) defs) (g-calls (cdr x) defs)))))

(defun g-reaches (fs self defs n)
  ; some f in fs calls self, perhaps through others (the generator's reaches?)
  (declare (xargs :guard t :measure (make-ord 1 (1+ (nfix n)) (acl2-count fs))))
  (if (or (zp n) (atom fs)) nil
    (let ((cs (g-calls (kaddr (lkp (car fs) defs)) defs)))
      (or (member-eq self cs)
          (g-reaches cs self defs (1- n))
          (g-reaches (cdr fs) self defs n)))))

(defun g-called (fns names)
  ; the fns whose Fortran names are among names
  (declare (xargs :guard t))
  (cond ((atom fns) nil)
        ((member-equal (g-sym (car fns) nil) names) (cons (car fns) (g-called (cdr fns) names)))
        (t (g-called (cdr fns) names))))

(defun g-formals (vs) (declare (xargs :guard t)) (if (atom vs) nil (cons (g-formal (car vs)) (g-formals (cdr vs)))))
(defun g-em (vs) (declare (xargs :guard t)) (if (atom vs) nil (cons (list* (car vs) (g-formal (car vs)) :int64) (g-em (cdr vs)))))
(defun g-dummies (vs) (declare (xargs :guard t)) (if (atom vs) nil (cons (list (g-formal (car vs)) :value :int64) (g-dummies (cdr vs)))))
(defun g-locals (locs)
  ; in the order made
  (declare (xargs :guard t))
  (if (atom locs) nil (append (g-locals (cdr locs)) (list (list (kar (car locs)) (kdr (car locs)))))))

; defs ((fn formals body) ...); sigs ((fn formals rtype) ...): (mv err proc)
(defun g-fn (fn defs sigs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((d (lkp fn defs)) (formals (kadr d)) (body (kaddr d))
         (fnames (g-formals formals)) (rtype (kadr (cdr (lkp fn sigs)))))
    (if (not (and (consp d) (symbol-listp formals) (no-duplicatesp-equal (cons "r" fnames))
                  (equal (kar (cdr (lkp fn sigs))) formals)))
        (mv :formals nil)
      (mv-let (e stmts cnt locs) (g-ret body (g-em formals) 0 nil fn sigs fnames)
        (declare (ignore cnt))
        (if e (mv e nil)
          (mv nil (list :function (g-sym fn nil) t
                        (if (g-reaches (g-called (strip-cars sigs) (g-fcalls stmts)) fn defs (1+ (len defs))) t nil)
                        (g-dummies formals) rtype (g-locals locs)
                        (if (g-has '(:cycle) stmts) (list (list :do stmts)) stmts))))))))

; ---- what ACL2 hands over: ((fn formals stobjs-out guards-verified body) ...)

(defun g-defs (raw)
  (declare (xargs :guard t))
  (if (atom raw) nil
    (let ((r (car raw)))
      (cons (list (kar r) (kadr r) (nth 4 (true-list-fix r))) (g-defs (cdr raw))))))

(defun g-sigs (raw bools)
  ; only a function of one result and verified guards is taken
  (declare (xargs :guard t))
  (if (atom raw) nil
    (let ((r (car raw)))
      (if (and (equal (kaddr r) '(nil)) (eq (kadddr r) t))
          (cons (list (kar r) (kadr r) (if (member-eq (kar r) bools) :logical :int64)) (g-sigs (cdr raw) bools))
        (g-sigs (cdr raw) bools)))))

(defun g-procs (fns defs sigs)
  ; (mv err procs), err naming the function refused
  (declare (xargs :guard t :verify-guards nil))
  (if (atom fns) (mv nil nil)
    (mv-let (e p) (if (consp (lkp (car fns) sigs)) (g-fn (car fns) defs sigs) (mv :refused nil))
      (if e (mv (list e (car fns)) nil)
        (mv-let (e ps) (g-procs (cdr fns) defs sigs)
          (mv e (cons p ps)))))))

(defun g-module (raw bools)
  (declare (xargs :guard t :verify-guards nil))
  (let ((defs (g-defs raw)) (sigs (g-sigs raw bools)))
    (g-procs (strip-cars defs) defs sigs)))

; ---- tests: clotran's own functions, as ACL2 hands them over

(defconst *gen-test-raw*
  '((hpg-n40 (x) (nil) t (if (if (natp x) (not (< '1099511627776 x)) 'nil) x '0))
    (anl-odd (n) (nil) t (if (zp n) '0 (if (equal n '1) '1 (anl-odd (binary-+ '-2 n)))))
    (hpg-add (n k) (nil) t ((lambda (s) (if (< s '1099511627776) s '1099511627776)) (binary-+ (nfix n) (nfix k))))
    (sk-more (d) (nil) t (if (equal d '1) (equal d '1) (if (equal d '2) (equal d '2) (equal d '5))))
    (pick (k) (nil) t (if (equal k '1) '10 (if (eql '-1 k) '20 (if (equal k '7) (binary-* k k) '30))))
    (fact (n) (nil) t (if (zp n) '1 (binary-* n (fact (binary-+ '-1 n)))))
    (s64 (x) (nil) t (if (if (integerp x) (if (not (< x '-9223372036854775808)) (< x '9223372036854775808) 'nil) 'nil) x '0))))

(defconst *gen-test*
  (mv-let (e procs) (g-module *gen-test-raw* '(sk-more)) (if e e (list :module "m" procs))))

(assert-event (fmodule-p *gen-test*))

(assert-event
 (equal (cadr (caddr *gen-test*))
        '(:function "anl_odd" t nil (("n_" :value :int64)) :int64 (("n_1" :int64))
          ((:do ((:if (:le (:var "n_") (:int 0))
                      ((:assign (:var "r") (:int 0)) (:return))
                      ((:if (:eq (:var "n_") (:int 1))
                            ((:assign (:var "r") (:int 1)) (:return))
                            ((:assign (:var "n_1") (:add (:int -2) (:var "n_")))
                             (:assign (:var "n_") (:var "n_1"))
                             (:cycle)))))))))))

(defmacro gen-run (&rest probes) `(fsem-run *gen-test* nil nil ',probes 100000))

(defun g-lits (ks) (declare (xargs :guard t)) (if (atom ks) nil (cons (g-lit (car ks)) (g-lits (cdr ks)))))
(defun a-quotes (ks) (declare (xargs :guard t)) (if (atom ks) nil (cons (list 'quote (car ks)) (a-quotes (cdr ks)))))

; fsem on the output answers what a-ev answers on the source
(defun gen-agree (fn args)
  (declare (xargs :mode :program))
  (mv-let (e v) (a-ev (cons fn (a-quotes args))
                      nil (g-defs *gen-test-raw*) 100000)
    (equal (fsem-run *gen-test* nil nil
                     (list (list :print (list :fcall (g-sym fn nil) (g-lits args)))) 100000)
           (if e (list (list :error (if (eq e :range) :overflow e))) (list v)))))

(assert-event (and (gen-agree 'hpg-n40 '(5)) (gen-agree 'hpg-n40 '(-5)) (gen-agree 'hpg-n40 '(1099511627777))
                   (gen-agree 'anl-odd '(7)) (gen-agree 'anl-odd '(10)) (gen-agree 'anl-odd '(-3))
                   (gen-agree 'hpg-add '(3 4)) (gen-agree 'hpg-add '(1099511627776 -2))
                   (gen-agree 'sk-more '(2)) (gen-agree 'sk-more '(3))
                   (gen-agree 'pick '(1)) (gen-agree 'pick '(-1)) (gen-agree 'pick '(7)) (gen-agree 'pick '(8))
                   (gen-agree 'fact '(20)) (gen-agree 'fact '(21)) (gen-agree 'fact '(0))
                   (gen-agree 's64 '(-9223372036854775808)) (gen-agree 's64 '(12))))
