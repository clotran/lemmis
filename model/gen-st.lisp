; gen-st: the stobj slice of clotran's ACL2-to-Fortran translation
; (scripts/acl2-fortran's `stmt`, and `expr`'s stobj reads), GEN.md
; "What remains" 4. A function answering a stobj is a SUBROUTINE on the
; stobj's derived type, updated in place; its value formals are VALUE
; dummies, its value results intent(out) r (r1 .. rk). A function reading a
; stobj and answering a value is a pure FUNCTION, the stobj intent(in).
; Taken today: field and array reads, `-length`, value functions given the
; stobj, if and let reading it; field and array updates, `if`, `let`
; (lambda), calls answering stobjs (CALL), `mv`/`mv-nth`, the tuple of the
; results, tail self-calls (a DO loop). Refused: extern fields and arrays,
; a case (SELECT) in statement or return position, tail self-calls of
; value functions.
;
; The configuration st, one alist from symbol to its role:
;   (hpg :stobj "hs" "heap_state")      a stobj formal: dummy hs, type(heap_state)
;   (h-msp :field "hs" "msp")           (h-msp hpg) is hs%msp
;   (update-h-msp :set "hs" "msp")      hs%msp = v
;   (h-mtagi :elem "hs" "mtag")         hs%mtag(i)
;   (update-h-mtagi :seti "hs" "mtag")  hs%mtag(i) = v
;   (h-mtag-length :size "hs" "mtag")   size(hs%mtag, kind=int64)
;   (hpg-run-pop :sub (c hpg) (nil hpg)) a function answering other than one
;                                        value: formals, stobjs-out (added by
;                                        g-st-module from raw)
; g-st-cfg builds it from the stobjs, fields and arrays, as acl2-fortran's
; config names them.

(in-package "ACL2")

(include-book "gen")

(set-verify-guards-eagerness 0)

(defun g-cat (a b c) (declare (xargs :guard t))
  (intern-in-package-of-symbol (string-append (if (stringp a) a "") (string-append (symbol-name (if (symbolp b) b 'x)) (if (stringp c) c "")))
                               'acl2))

(defun g-st-fields (fs)
  ; fs ((acc obj comp) ...)
  (if (atom fs) nil
    (let ((f (car fs)))
      (list* (list (kar f) :field (kadr f) (kaddr f)) (list (g-cat "UPDATE-" (kar f) nil) :set (kadr f) (kaddr f))
             (g-st-fields (cdr fs))))))

(defun g-st-arrays (as)
  ; as ((name obj comp) ...): name-i, update-name-i, name-length
  (if (atom as) nil
    (let ((a (car as)))
      (list* (list (g-cat nil (kar a) "I") :elem (kadr a) (kaddr a))
             (list (g-cat "UPDATE-" (kar a) "I") :seti (kadr a) (kaddr a))
             (list (g-cat nil (kar a) "-LENGTH") :size (kadr a) (kaddr a))
             (g-st-arrays (cdr as))))))

(defun g-st-stobjs (stobjs)
  ; stobjs ((sym obj type) ...)
  (if (atom stobjs) nil
    (cons (list (kar (car stobjs)) :stobj (kadr (car stobjs)) (kaddr (car stobjs))) (g-st-stobjs (cdr stobjs)))))

(defun g-st-cfg (stobjs fields arrays)
  (append (g-st-stobjs stobjs) (g-st-fields fields) (g-st-arrays arrays)))

(defun g-role (x st) (declare (xargs :guard t)) (if (symbolp x) (kar (cdr (lkp x st))) nil))
(defun g-obj (x st) (declare (xargs :guard t)) (kadr (cdr (lkp x st))))
(defun g-comp (x st) (declare (xargs :guard t)) (kaddr (cdr (lkp x st))))

; x mentions no stobj and no stobj operation: g-expr takes it whole
(mutual-recursion
 (defun g-st-free (x st)
   (declare (xargs :guard t))
   (cond ((atom x) (not (eq (g-role x st) :stobj)))
         ((eq (car x) 'quote) t)
         ((consp (car x)) (and (g-st-free (kaddr (car x)) st) (g-st-free-list (cdr x) st)))
         (t (and (not (g-role (car x) st)) (g-st-free-list (cdr x) st)))))
 (defun g-st-free-list (xs st)
   (declare (xargs :guard t))
   (if (atom xs) t (and (g-st-free (car xs) st) (g-st-free-list (cdr xs) st)))))

; ---- expressions reading a stobj: g-expr's (mv err stmts code type cnt locs)

; (mv-nth 'k mv): k, else nil. An mv call's value results are in em under
; (mv k), its function under (mv) (gen-st's lambda, as acl2-fortran's env)
(defun g-mvnth (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) 'mv-nth) (true-listp x) (= (len x) 3) (eq (caddr x) 'mv)
       (consp (cadr x)) (eq (car (cadr x)) 'quote) (consp (cdr (cadr x))) (natp (cadr (cadr x)))
       (cadr (cadr x))))

; a stobj var of an expression's lambda is bound to itself
(defun g-st-ident (vars xs st)
  (declare (xargs :guard t))
  (if (or (atom vars) (atom xs)) t
    (and (or (not (eq (g-role (car vars) st) :stobj)) (eq (car vars) (car xs)))
         (g-st-ident (cdr vars) (cdr xs) st))))

(mutual-recursion
 (defun g-sexpr (x em cnt locs sigs fnames st)
   (declare (xargs :guard t :measure (acl2-count x)
                   :hints (("Goal" :in-theory (disable g-st-free g-st-free-list g-mvnth g-st-ident g-role g-obj g-comp
                                                       lkp g-expr g-fresh g-if g-unop g-binop em-names g-chain)))))
   (cond
    ((g-mvnth x)
     (let ((b (lkp (list 'mv (g-mvnth x)) em)))
       (if (and (consp b) (consp (cdr b))) (mv nil nil (list :var (cadr b)) (cddr b) cnt locs)
         (mv :mv nil nil nil cnt locs))))
    ((g-st-free x st) (g-expr x em cnt locs sigs fnames))
    ((or (atom x) (not (true-listp x))) (mv :stobj nil nil nil cnt locs))
    ((member-eq (g-role (car x) st) '(:field :size))
     (if (and (= (len x) 2) (eq (g-role (cadr x) st) :stobj) (equal (g-obj (cadr x) st) (g-obj (car x) st)))
         (mv nil nil (list (if (eq (g-role (car x) st) :field) :comp :size) (g-obj (car x) st) (g-comp (car x) st))
             :int64 cnt locs)
       (mv :stobj nil nil nil cnt locs)))
    ((eq (g-role (car x) st) :elem)
     (if (not (and (= (len x) 3) (eq (g-role (caddr x) st) :stobj) (equal (g-obj (caddr x) st) (g-obj (car x) st))))
         (mv :stobj nil nil nil cnt locs)
       (mv-let (e s c ty cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
         (if (or e (not (eq ty :int64))) (mv (or e :type) nil nil nil cnt locs)
           (mv nil s (list :elem (g-obj (car x) st) (g-comp (car x) st) c) :int64 cnt locs)))))
    ((member-eq (car x) '(if implies))
     ; g-expr's if, on terms reading the stobj
     (mv-let (e sc cc tc cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
       (if e (mv e nil nil nil cnt locs)
         (mv-let (e sa ca ta cnt locs) (g-sexpr (caddr x) em cnt locs sigs fnames st)
           (if e (mv e nil nil nil cnt locs)
             (mv-let (e sb cb tb cnt locs)
               (if (eq (car x) 'if) (g-sexpr (cadddr x) em cnt locs sigs fnames st)
                 (mv nil nil '(:true) :logical cnt locs))
               (if (or e (not (= (len x) (if (eq (car x) 'if) 4 3))))
                   (mv (or e :syntax) nil nil nil cnt locs)
                 (g-if sc cc tc sa ca ta sb cb tb cnt locs (append fnames (em-names em))))))))))
    ((eq (car x) 'the-check)
     (if (= (len x) 4) (g-sexpr (cadddr x) em cnt locs sigs fnames st) (mv :syntax nil nil nil cnt locs)))
    ((consp (car x))
     ; g-expr's lambda; a stobj var only bound to itself
     (let ((vars (cadr (car x))) (body (caddr (car x))))
       (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                     (no-duplicatesp-eq vars) (= (len vars) (len (cdr x))) (not (member-eq 'mv vars))
                     (g-st-ident vars (cdr x) st)))
           (mv :stobj nil nil nil cnt locs)
         (mv-let (e s binds cnt locs) (g-svals vars (cdr x) em cnt locs sigs fnames st)
           (if e (mv e nil nil nil cnt locs)
             (mv-let (e sb cb tb cnt locs) (g-sexpr body (append binds em) cnt locs sigs fnames st)
               (if e (mv e nil nil nil cnt locs)
                 (mv nil (append s sb) cb tb cnt locs))))))))
    ((consp (lkp (car x) sigs))
     ; a function answering a value, given the stobj: f(hs, args)
     (let ((sig (cdr (lkp (car x) sigs))))
       (if (not (equal (len (kar sig)) (len (cdr x)))) (mv :type nil nil nil cnt locs)
         (mv-let (e s sc cs cnt locs) (g-scall-args (kar sig) (cdr x) nil em cnt locs sigs fnames st)
           (if e (mv e nil nil nil cnt locs)
             (mv nil s (list :fcall (g-sym (car x) nil) (append sc cs)) (kadr sig) cnt locs))))))
    ((or (g-role (car x) st) (eq (car x) 'quote)) (mv :stobj nil nil nil cnt locs))
    (t ; a primitive on arguments reading the stobj
     (mv-let (e s cs ts cnt locs) (g-sargs (cdr x) em cnt locs sigs fnames st)
       (cond (e (mv e nil nil nil cnt locs))
             ((= (len cs) 1) (mv-let (e c ty) (g-unop (car x) (car cs) (car ts)) (mv e s c ty cnt locs)))
             ((= (len cs) 2) (mv-let (e c ty) (g-binop (car x) (car cs) (car ts) (cadr cs) (cadr ts))
                               (mv e s c ty cnt locs)))
             (t (mv :unknown nil nil nil cnt locs)))))))
 (defun g-sargs (xs em cnt locs sigs fnames st)
   (declare (xargs :guard t :measure (acl2-count xs)))
   (if (atom xs) (mv nil nil nil nil cnt locs)
     (mv-let (e s c ty cnt locs) (g-sexpr (car xs) em cnt locs sigs fnames st)
       (if e (mv e nil nil nil cnt locs)
         (mv-let (e ss cs ts cnt locs) (g-sargs (cdr xs) em cnt locs sigs fnames st)
           (if e (mv e nil nil nil cnt locs)
             (mv nil (append s ss) (cons c cs) (cons ty ts) cnt locs)))))))
 (defun g-scall-args (formals xs upd em cnt locs sigs fnames st)
   ; a call's arguments, as acl2-fortran's call-args: (mv err stmts objs codes cnt locs),
   ; objs the stobj formals' objects, codes the other arguments' (int64). A
   ; stobj argument is its formal; under upd (a CALL statement) it may be an
   ; update, which the caller translates
   (declare (xargs :guard t :measure (acl2-count xs)))
   (cond ((or (atom formals) (atom xs)) (mv nil nil nil nil cnt locs))
         ((eq (g-role (car formals) st) :stobj)
          (if (not (or upd (eq (car xs) (car formals)))) (mv :stobj nil nil nil cnt locs)
            (mv-let (e s sc cs cnt locs) (g-scall-args (cdr formals) (cdr xs) upd em cnt locs sigs fnames st)
              (mv e s (cons (list :var (g-obj (car formals) st)) sc) cs cnt locs))))
         (t (mv-let (e s c ty cnt locs) (g-sexpr (car xs) em cnt locs sigs fnames st)
              (if (or e (not (eq ty :int64))) (mv (or e :type) nil nil nil cnt locs)
                (mv-let (e ss sc cs cnt locs) (g-scall-args (cdr formals) (cdr xs) upd em cnt locs sigs fnames st)
                  (if e (mv e nil nil nil cnt locs)
                    (mv nil (append s ss) sc (cons c cs) cnt locs))))))))
 (defun g-svals (vars xs em cnt locs sigs fnames st)
   ; a let's value bindings: each var bound to a different term, in the outer
   ; scope, into a temporary named after it: (mv err stmts binds cnt locs).
   ; Stobj vars and mv are the statements' (g-stmt)
   (declare (xargs :guard t :measure (acl2-count xs)))
   (cond ((or (atom vars) (atom xs)) (mv nil nil nil cnt locs))
         ((or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv))
          (g-svals (cdr vars) (cdr xs) em cnt locs sigs fnames st))
         (t (mv-let (e s c ty cnt locs) (g-sexpr (car xs) em cnt locs sigs fnames st)
              (if e (mv e nil nil cnt locs)
                (mv-let (e tmp cnt locs) (g-fresh (car vars) ty cnt locs (append fnames (em-names em)))
                  (if e (mv e nil nil cnt locs)
                    (mv-let (e ss binds cnt locs) (g-svals (cdr vars) (cdr xs) em cnt locs sigs fnames st)
                      (if e (mv e nil nil cnt locs)
                        (mv nil (append s (list (list :assign (list :var tmp) c)) ss)
                            (cons (list* (car vars) tmp ty) binds) cnt locs)))))))))))

; ---- statements: a term answering the results outs (stobjs-out: a stobj,
; or nil for a value, which goes to the next of dests), (mv err stmts cnt locs).
; tself is the function when x is in tail position (a self-call is then new
; values for the formals and CYCLE), else nil.

; the arg bound to var v
(defun g-arg-of (v vars xs)
  (declare (xargs :guard t))
  (cond ((or (atom vars) (atom xs)) nil)
        ((eq (car vars) v) (car xs))
        (t (g-arg-of v (cdr vars) (cdr xs)))))

(defthm g-arg-of-count
  (<= (acl2-count (g-arg-of v vars xs)) (acl2-count xs))
  :rule-classes :linear)

; (cons a (cons b ... 'nil)): the components
(defun g-conses (x)
  (declare (xargs :guard t))
  (if (and (consp x) (eq (car x) 'cons) (consp (cdr x)) (consp (cddr x)))
      (cons (cadr x) (g-conses (caddr x)))
    nil))

(defthm g-conses-count
  (implies (consp x) (< (acl2-count (g-conses x)) (acl2-count x)))
  :rule-classes :linear)

; every stobj var bound to a different term is bound to an mv-nth
(defun g-acts-mv (vars xs st)
  (declare (xargs :guard t))
  (if (or (atom vars) (atom xs)) t
    (and (or (not (eq (g-role (car vars) st) :stobj)) (eq (car vars) (car xs)) (g-mvnth (car xs)))
         (g-acts-mv (cdr vars) (cdr xs) st))))

; a stobj var bound to (mv-nth 'k mv) is the k-th result of mv's function
(defun g-acts-place (vars xs em st)
  (declare (xargs :guard t))
  (if (or (atom vars) (atom xs)) t
    (and (or (not (and (eq (g-role (car vars) st) :stobj) (g-mvnth (car xs))))
             (eq (car vars) (nth (g-mvnth (car xs)) (true-list-fix (g-comp (kadr (lkp '(mv) em)) st)))))
         (g-acts-place (cdr vars) (cdr xs) em st))))

; the temporaries of an mv call's value results: (mv err mvbinds dests cnt locs)
(defun g-mvtmps (outs k cnt locs used)
  (declare (xargs :guard t))
  (cond ((atom outs) (mv nil nil nil cnt locs))
        ((car outs) (g-mvtmps (cdr outs) (1+ (nfix k)) cnt locs used))
        (t (mv-let (e tmp cnt locs) (g-fresh 'mv :int64 cnt locs used)
             (if e (mv e nil nil cnt locs)
               (mv-let (e bs ds cnt locs) (g-mvtmps (cdr outs) (1+ (nfix k)) cnt locs used)
                 (mv e (cons (list* (list 'mv (nfix k)) tmp :int64) bs) (cons (list :var tmp) ds) cnt locs)))))))

; a tuple's value components: (mv err stmts assigns cnt locs), each to the
; next dest -- through a temporary "r" when tmp (the stobjs' moves between)
(defun g-tvals (outs comps dests tmp em cnt locs sigs fnames st)
  (declare (xargs :guard t :measure (acl2-count comps)))
  (cond ((or (atom outs) (atom comps)) (mv nil nil nil cnt locs))
        ((car outs) (g-tvals (cdr outs) (cdr comps) dests tmp em cnt locs sigs fnames st))
        ((atom dests) (mv :arity nil nil cnt locs))
        (t (mv-let (e s c ty cnt locs) (g-sexpr (car comps) em cnt locs sigs fnames st)
             (if (or e (not (eq ty :int64))) (mv (or e :type) nil nil cnt locs)
               (mv-let (e tm cnt locs) (if tmp (g-fresh 'r :int64 cnt locs (append fnames (em-names em)))
                                         (mv nil nil cnt locs))
                 (if e (mv e nil nil cnt locs)
                   (mv-let (e ss as cnt locs) (g-tvals (cdr outs) (cdr comps) (cdr dests) tmp em cnt locs sigs fnames st)
                     (if e (mv e nil nil cnt locs)
                       (if tmp
                           (mv nil (append s (list (list :assign (list :var tm) c)) ss)
                               (cons (list :assign (car dests) (list :var tm)) as) cnt locs)
                         (mv nil (append s (list (list :assign (car dests) c)) ss) nil cnt locs)))))))))))

; the stobj results moved: some out o bound to a term other than o
(defun g-moves (outs comps)
  (declare (xargs :guard t))
  (if (or (atom outs) (atom comps)) nil
    (or (and (car outs) (not (eq (car outs) (car comps)))) (g-moves (cdr outs) (cdr comps)))))

; a tail self-call's value formals: each new value into a temporary named
; after it, then the formals (g-tail, on terms reading the stobj):
; (mv err stmts assigns cnt locs)
(defun g-stail (vars xs em cnt locs sigs fnames st)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (cond ((or (atom vars) (atom xs)) (mv nil nil nil cnt locs))
        ((eq (g-role (car vars) st) :stobj) (g-stail (cdr vars) (cdr xs) em cnt locs sigs fnames st))
        (t (mv-let (e s c ty cnt locs) (g-sexpr (car xs) em cnt locs sigs fnames st)
             (if (or e (not (eq ty :int64))) (mv (or e :type) nil nil cnt locs)
               (mv-let (e tmp cnt locs) (g-fresh (car vars) ty cnt locs (append fnames (em-names em)))
                 (if e (mv e nil nil cnt locs)
                   (mv-let (e ss as cnt locs) (g-stail (cdr vars) (cdr xs) em cnt locs sigs fnames st)
                     (if e (mv e nil nil cnt locs)
                       (mv nil (append s (list (list :assign (list :var tmp) c)) ss)
                           (cons (list :assign (list :var (g-formal (car vars))) (list :var tmp)) as)
                           cnt locs))))))))))

(mutual-recursion
 (defun g-stmt (x em cnt locs sigs fnames st outs dests tself)
   (declare (xargs :guard t :measure (+ 2 (* 3 (acl2-count x)))
                   :hints (("Goal" :in-theory (disable g-st-free g-st-free-list g-mvnth g-role g-obj g-comp lkp
                                                       g-sexpr g-svals g-stail g-tvals g-mvtmps g-moves g-acts-mv
                                                       g-acts-place g-arg-of g-conses g-fresh em-names g-chain
                                                       member-equal no-duplicatesp-equal symbol-listp len)))))
   (cond
    ((symbolp x) (if (equal (list x) outs) (mv nil nil cnt locs) (mv :stobj nil cnt locs)))
    ((or (atom x) (not (true-listp x))) (mv :stobj nil cnt locs))
    ((and tself (eq (car x) tself))
     ; the tail self-call: the values into temporaries, the stobjs' updates, the formals, CYCLE
     (let ((formals (g-obj tself st)))
       (if (not (= (len formals) (len (cdr x)))) (mv :arity nil cnt locs)
         (mv-let (e s as cnt locs) (g-stail formals (cdr x) em cnt locs sigs fnames st)
           (if e (mv e nil cnt locs)
             (mv-let (e sa cnt locs) (g-sacts formals (cdr x) em cnt locs sigs fnames st)
               (if e (mv e nil cnt locs)
                 (mv nil (append s sa as (list '(:cycle))) cnt locs))))))))
    ((eq (car x) 'cons)
     ; the mv of the results: the values to dests; when a stobj result is
     ; moved, the values first, into temporaries, read from the stobjs as they were
     (let ((comps (g-conses x)))
       (if (not (= (len comps) (len outs))) (mv :arity nil cnt locs)
         (mv-let (e s as cnt locs) (g-tvals outs comps dests (g-moves outs comps) em cnt locs sigs fnames st)
           (if e (mv e nil cnt locs)
             (mv-let (e sm cnt locs) (g-sacts outs comps em cnt locs sigs fnames st)
               (if e (mv e nil cnt locs)
                 (mv nil (append s sm as) cnt locs))))))))
    ((eq (g-role (car x) st) :set)
     ; (update-f v s): s's statements, then v read (after them, as acl2-fortran writes it)
     (if (not (and (= (len x) 3) (equal outs (list (caddr x))) (equal (g-obj (car x) st) (g-obj (caddr x) st)))) (mv :stobj nil cnt locs)
       (mv-let (e s c ty cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
         (if (or e (not (eq ty :int64))) (mv (or e :type) nil cnt locs)
           (mv-let (e si cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs dests nil)
             (if e (mv e nil cnt locs)
               (mv nil (append si s (list (list :assign (list :comp (g-obj (car x) st) (g-comp (car x) st)) c)))
                   cnt locs)))))))
    ((eq (g-role (car x) st) :seti)
     ; (update-fi i v s): i and v into temporaries, read before s's statements run
     (if (not (and (= (len x) 4) (equal outs (list (cadddr x))) (equal (g-obj (car x) st) (g-obj (cadddr x) st)))) (mv :stobj nil cnt locs)
       (mv-let (e si ci ti cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
         (if (or e (not (eq ti :int64))) (mv (or e :type) nil cnt locs)
           (mv-let (e sv cv tv cnt locs) (g-sexpr (caddr x) em cnt locs sigs fnames st)
             (if (or e (not (eq tv :int64))) (mv (or e :type) nil cnt locs)
               (mv-let (e tmi cnt locs) (g-fresh 'i :int64 cnt locs (append fnames (em-names em)))
                 (if e (mv e nil cnt locs)
                   (mv-let (e tmv cnt locs) (g-fresh 'v :int64 cnt locs (append fnames (em-names em)))
                     (if e (mv e nil cnt locs)
                       (mv-let (e ss cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs dests nil)
                         (if e (mv e nil cnt locs)
                           (mv nil (append si (list (list :assign (list :var tmi) ci)) sv
                                           (list (list :assign (list :var tmv) cv)) ss
                                           (list (list :assign (list :elem (g-obj (car x) st) (g-comp (car x) st) (list :var tmi))
                                                       (list :var tmv))))
                               cnt locs)))))))))))))
    ((eq (car x) 'if)
     (if (or (not (= (len x) 4)) (<= 3 (g-chain x nil nil))) (mv :stobj nil cnt locs)
       (mv-let (e sc cc tc cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
         (if (or e (not (eq tc :logical))) (mv (or e :type) nil cnt locs)
           (mv-let (e sa cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs dests tself)
             (if e (mv e nil cnt locs)
               (mv-let (e sb cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs dests tself)
                 (if e (mv e nil cnt locs)
                   (mv nil (append sc (list (list :if cc sa sb))) cnt locs)))))))))
    ((consp (car x))
     ; ((lambda vars body) . args): the values first, read in the outer scope;
     ; then an mv call (mv bound to it), its value results into temporaries;
     ; then the stobjs' updates -- translated, as acl2-fortran does, with the
     ; new values in scope (GEN.md's finding) -- then the body
     (let* ((vars (kadr (car x))) (body (kaddr (car x))) (mvc (g-arg-of 'mv vars (cdr x))))
       (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                     (no-duplicatesp-eq vars) (= (len vars) (len (cdr x)))
                     (or (not (member-eq 'mv vars)) (and (consp mvc) (eq (g-role (car mvc) st) :sub) (g-acts-mv vars (cdr x) st)))))
           (mv :stobj nil cnt locs)
         (mv-let (e s binds cnt locs) (g-svals vars (cdr x) em cnt locs sigs fnames st)
           (if e (mv e nil cnt locs)
             (let ((em (append binds em)))
               (mv-let (e mbinds mdests cnt locs)
                 (if (member-eq 'mv vars) (g-mvtmps (g-comp (car mvc) st) 0 cnt locs (append fnames (em-names em)))
                   (mv nil nil nil cnt locs))
                 (if e (mv e nil cnt locs)
                   (mv-let (e sm cnt locs)
                     (if (member-eq 'mv vars) (g-callst mvc em cnt locs sigs fnames st mdests) (mv nil nil cnt locs))
                     (if e (mv e nil cnt locs)
                       (let ((em (if (member-eq 'mv vars) (append (cons (list* '(mv) (car mvc) :mv) mbinds) em) em)))
                         (if (not (g-acts-place vars (cdr x) em st)) (mv :mv nil cnt locs)
                           (mv-let (e sa cnt locs) (g-sacts vars (cdr x) em cnt locs sigs fnames st)
                             (if e (mv e nil cnt locs)
                               (mv-let (e sb cnt locs) (g-stmt body em cnt locs sigs fnames st outs dests tself)
                                 (if e (mv e nil cnt locs)
                                   (mv nil (append s sm sa sb) cnt locs)))))))))))))))))
    ((eq (g-role (car x) st) :sub)
     ; a call answering the results wanted: CALL f(stobjs, args, dests)
     (if (not (equal (g-comp (car x) st) outs)) (mv :stobj nil cnt locs)
       (g-callst x em cnt locs sigs fnames st dests)))
    (t (mv :stobj nil cnt locs))))
 (defun g-callst (x em cnt locs sigs fnames st dests)
   ; acl2-fortran's call-stmt: the value arguments' statements, the stobj
   ; arguments' updates, then CALL f(stobjs, values, dests)
   (declare (xargs :guard t :measure (+ 1 (* 3 (acl2-count x)))))
   (if (not (and (consp x) (true-listp x) (= (len (g-obj (car x) st)) (len (cdr x))))) (mv :arity nil cnt locs)
     (mv-let (e s sc cs cnt locs) (g-scall-args (g-obj (car x) st) (cdr x) t em cnt locs sigs fnames st)
       (if e (mv e nil cnt locs)
         (mv-let (e sa cnt locs) (g-sacts (g-obj (car x) st) (cdr x) em cnt locs sigs fnames st)
           (if e (mv e nil cnt locs)
             (mv nil (append s sa (list (list :call (g-sym (car x) nil) (append sc cs (true-list-fix dests)))))
                 cnt locs)))))))
 (defun g-sacts (vars xs em cnt locs sigs fnames st)
   ; each stobj var bound to a different term (not an mv-nth): that term's statements
   (declare (xargs :guard t :measure (+ 2 (* 3 (acl2-count xs)))))
   (cond ((or (atom vars) (atom xs)) (mv nil nil cnt locs))
         ((and (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs))))
          (mv-let (e s cnt locs) (g-stmt (car xs) em cnt locs sigs fnames st (list (car vars)) nil nil)
            (if e (mv e nil cnt locs)
              (mv-let (e ss cnt locs) (g-sacts (cdr vars) (cdr xs) em cnt locs sigs fnames st)
                (mv e (append s ss) cnt locs)))))
         (t (g-sacts (cdr vars) (cdr xs) em cnt locs sigs fnames st)))))

; ---- a function reading a stobj, answering a value: g-ret on g-sexpr
; (a case of three arms or more, and a tail self-call, refused for now)
(defun g-sret (x em cnt locs self sigs fnames st)
  (declare (xargs :guard t :measure (acl2-count x)))
  (cond
   ((and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4) (< (g-chain x nil nil) 3))
    (mv-let (e sc cc tc cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
      (if (or e (not (eq tc :logical))) (mv (or e :type) nil cnt locs)
        (mv-let (e sa cnt locs) (g-sret (caddr x) em cnt locs self sigs fnames st)
          (if e (mv e nil cnt locs)
            (mv-let (e sb cnt locs) (g-sret (cadddr x) em cnt locs self sigs fnames st)
              (if e (mv e nil cnt locs)
                (mv nil (append sc (list (list :if cc sa sb))) cnt locs))))))))
   ((and (consp x) (or (eq (car x) self) (eq (car x) 'if))) (mv :stobj nil cnt locs))
   (t (mv-let (e s c ty cnt locs) (g-sexpr x em cnt locs sigs fnames st)
        (if (or e (not (equal ty (kadr (cdr (lkp self sigs)))))) (mv (or e :type) nil cnt locs)
          (mv nil (append s (list (list :assign '(:var "r") c) '(:return))) cnt locs))))))

; ---- a procedure: raw is ACL2's hand-over (fn formals stobjs-out guards-verified body)

(defun g-st-dummies (formals outs st)
  ; the stobjs first, in the formals' order
  (cond ((atom formals) nil)
        ((eq (g-role (car formals) st) :stobj)
         (cons (list (g-obj (car formals) st) (if (member-eq (car formals) outs) :inout :in) (g-comp (car formals) st))
               (g-st-dummies (cdr formals) outs st)))
        (t (g-st-dummies (cdr formals) outs st))))

(defun g-st-vals (formals st)
  (cond ((atom formals) nil)
        ((eq (g-role (car formals) st) :stobj) (g-st-vals (cdr formals) st))
        (t (cons (car formals) (g-st-vals (cdr formals) st)))))

(defun g-st-outs-ok (outs st)
  ; every result a stobj or a value (nil)
  (if (atom outs) (null outs) (and (or (null (car outs)) (eq (g-role (car outs) st) :stobj)) (g-st-outs-ok (cdr outs) st))))

; the intent(out) results: r, or r1 .. rk
(defun g-rnames (i k)
  (declare (xargs :measure (nfix (- (nfix k) (nfix i)))))
  (if (zp (- (nfix k) (nfix i))) nil
    (cons (if (= (nfix k) 1) "r" (string-append "r" (coerce (explode-nonnegative-integer (1+ (nfix i)) 10 nil) 'string)))
          (g-rnames (1+ (nfix i)) k))))
(defun g-rvars (rs) (if (atom rs) nil (cons (list :var (car rs)) (g-rvars (cdr rs)))))
(defun g-rdummies (rs) (if (atom rs) nil (cons (list (car rs) :out :int64) (g-rdummies (cdr rs)))))

(defun g-ccalls (x)
  ; the subroutines an output tree CALLs
  (if (atom x) nil
    (if (and (eq (car x) :call) (consp (cdr x)))
        (cons (cadr x) (g-ccalls (cddr x)))
      (append (g-ccalls (car x)) (g-ccalls (cdr x))))))

(defun g-st-fn (r defs sigs st)
  (let* ((fn (kar r)) (formals (kadr r)) (outs (kaddr r)) (body (nth 4 (true-list-fix r)))
         (vals (g-st-vals formals st)) (fnames (g-formals vals))
         (rs (g-rnames 0 (- (len outs) (len (remove nil outs))))))
    (cond
     ((not (and (symbol-listp formals) (no-duplicatesp-equal formals) (eq (kadddr r) t)
                (consp outs) (g-st-outs-ok outs st) (no-duplicatesp-equal fnames)))
      (mv :formals nil))
     ((equal outs '(nil))
      ; reads a stobj, answers a value: a pure FUNCTION, the stobj intent(in)
      (mv-let (e stmts cnt locs) (g-sret body (g-em vals) 0 nil fn sigs fnames st)
        (declare (ignore cnt))
        (if (or e (not (consp (lkp fn sigs)))) (mv (or e :sig) nil)
          (mv nil (list :function (g-sym fn nil) t
                        (if (g-reaches (g-called (strip-cars sigs) (g-fcalls stmts)) fn defs (1+ (len defs))) t nil)
                        (append (g-st-dummies formals outs st) (g-dummies vals))
                        (kadr (cdr (lkp fn sigs))) (g-locals locs) stmts)))))
     (t
      (mv-let (e stmts cnt locs) (g-stmt body (g-em vals) 0 nil sigs fnames st outs (g-rvars rs) fn)
        (declare (ignore cnt))
        (if e (mv e nil)
          (mv nil (list :subroutine (g-sym fn nil)
                        (if (g-reaches (g-called (strip-cars defs) (append (g-fcalls stmts) (g-ccalls stmts)))
                                       fn defs (1+ (len defs)))
                            t nil)
                        (append (g-st-dummies formals outs st) (g-dummies vals) (g-rdummies rs))
                        (g-locals locs)
                        (if (g-has '(:cycle) stmts) (list (list :do (append stmts '((:exit))))) stmts)))))))))

(defun g-st-procs (raw fns defs sigs st)
  ; (mv err procs) for the fns of raw, in fns' order
  (if (atom fns) (mv nil nil)
    (mv-let (e p) (g-st-fn (assoc-eq (car fns) raw) defs sigs st)
      (if e (mv (list e (car fns)) nil)
        (mv-let (e ps) (g-st-procs raw (cdr fns) defs sigs st)
          (mv e (cons p ps)))))))

; every function of raw answering other than one value: (fn :sub formals outs)
(defun g-st-subs (raw)
  (if (atom raw) nil
    (let ((r (car raw)))
      (if (equal (kaddr r) '(nil)) (g-st-subs (cdr raw))
        (cons (list (kar r) :sub (kadr r) (kaddr r)) (g-st-subs (cdr raw)))))))

(defun g-st-module (raw bools fns st)
  (g-st-procs raw fns (g-defs raw) (g-sigs raw bools) (append st (g-st-subs raw))))

; ---- clotran's hpg-spush, as ACL2 hands it over

(defconst *heapg-st*
  (g-st-cfg '((hpg "hs" "heap_state"))
            '((h-err "hs" "err") (h-msp "hs" "msp") (h-nobj "hs" "nobj") (h-nvec "hs" "nvec") (h-nstr "hs" "nstr")
              (h-alive "hs" "alive") (h-nswo "hs" "nswo") (h-nswv "hs" "nswv") (h-nsws "hs" "nsws") (h-afree "hs" "afree"))
            '((h-mtag "hs" "mtag") (h-mref "hs" "mref"))))

(defconst *spush-raw*
  '((hpg-spush (tag ref hpg) (hpg) t
               ((lambda (sp ref tag hpg)
                  (if (< sp (h-mtag-length hpg))
                      ((lambda (hpg ref sp) ((lambda (hpg sp) (update-h-msp (binary-+ '1 sp) hpg)) (update-h-mrefi sp ref hpg) sp))
                       (update-h-mtagi sp tag hpg) ref sp)
                    (update-h-err '1 hpg)))
                (h-msp hpg) ref tag hpg))))

(assert-event
 (equal (mv-list 2 (g-st-module *spush-raw* nil '(hpg-spush) *heapg-st*))
        '(nil ((:subroutine "hpg_spush" nil (("hs" :inout "heap_state") ("tag_" :value :int64) ("ref_" :value :int64))
                (("sp_1" :int64) ("i_2" :int64) ("v_3" :int64) ("i_4" :int64) ("v_5" :int64))
                ((:assign (:var "sp_1") (:comp "hs" "msp"))
                 (:if (:lt (:var "sp_1") (:size "hs" "mtag"))
                      ((:assign (:var "i_2") (:var "sp_1")) (:assign (:var "v_3") (:var "tag_"))
                       (:assign (:elem "hs" "mtag" (:var "i_2")) (:var "v_3"))
                       (:assign (:var "i_4") (:var "sp_1")) (:assign (:var "v_5") (:var "ref_"))
                       (:assign (:elem "hs" "mref" (:var "i_4")) (:var "v_5"))
                       (:assign (:comp "hs" "msp") (:add (:int 1) (:var "sp_1"))))
                      ((:assign (:comp "hs" "err") (:int 1))))))))))
