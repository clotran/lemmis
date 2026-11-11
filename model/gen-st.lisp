; gen-st: the stobj slice of clotran's ACL2-to-Fortran translation
; (scripts/acl2-fortran's `stmt`, and `expr`'s stobj reads), GEN.md
; "What remains" 4. A function answering a stobj is a SUBROUTINE on the
; stobj's derived type, updated in place; its value formals are VALUE
; dummies. Taken today: field and array reads, `-length`, field and array
; updates, `if` and `let` (lambda) over them. Refused: calls answering
; stobjs, `mv` and the intent(out) results, tail self-calls, extern fields
; and arrays, a case (SELECT) in statement position.
;
; The configuration st, one alist from symbol to its role:
;   (hpg :stobj "hs" "heap_state")      a stobj formal: dummy hs, type(heap_state)
;   (h-msp :field "hs" "msp")           (h-msp hpg) is hs%msp
;   (update-h-msp :set "hs" "msp")      hs%msp = v
;   (h-mtagi :elem "hs" "mtag")         hs%mtag(i)
;   (update-h-mtagi :seti "hs" "mtag")  hs%mtag(i) = v
;   (h-mtag-length :size "hs" "mtag")   size(hs%mtag, kind=int64)
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

(mutual-recursion
 (defun g-sexpr (x em cnt locs sigs fnames st)
   (declare (xargs :guard t :measure (acl2-count x)))
   (cond
    ((g-st-free x st) (g-expr x em cnt locs sigs fnames))
    ((or (atom x) (not (true-listp x)) (consp (car x))) (mv :stobj nil nil nil cnt locs))
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
    ((or (g-role (car x) st) (member-eq (car x) '(quote if implies the-check)) (consp (lkp (car x) sigs)))
     (mv :stobj nil nil nil cnt locs))
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
             (mv nil (append s ss) (cons c cs) (cons ty ts) cnt locs))))))))

; a let's value bindings: each var bound to a different term, in the outer
; scope, into a temporary named after it: (mv err stmts binds cnt locs)
(defun g-svals (vars xs em cnt locs sigs fnames st)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (cond ((or (atom vars) (atom xs)) (mv nil nil nil cnt locs))
        ((or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj))
         (g-svals (cdr vars) (cdr xs) em cnt locs sigs fnames st))
        (t (mv-let (e s c ty cnt locs) (g-sexpr (car xs) em cnt locs sigs fnames st)
             (if e (mv e nil nil cnt locs)
               (mv-let (e tmp cnt locs) (g-fresh (car vars) ty cnt locs (append fnames (em-names em)))
                 (if e (mv e nil nil cnt locs)
                   (mv-let (e ss binds cnt locs) (g-svals (cdr vars) (cdr xs) em cnt locs sigs fnames st)
                     (if e (mv e nil nil cnt locs)
                       (mv nil (append s (list (list :assign (list :var tmp) c)) ss)
                           (cons (list* (car vars) tmp ty) binds) cnt locs))))))))))

; ---- statements: a term answering the stobjs outs, (mv err stmts cnt locs)

(mutual-recursion
 (defun g-stmt (x em cnt locs sigs fnames st outs)
   (declare (xargs :guard t :measure (acl2-count x)))
   (cond
    ((symbolp x) (if (equal (list x) outs) (mv nil nil cnt locs) (mv :stobj nil cnt locs)))
    ((or (atom x) (not (true-listp x))) (mv :stobj nil cnt locs))
    ((eq (g-role (car x) st) :set)
     ; (update-f v s): s's statements, then v read (after them, as acl2-fortran writes it)
     (if (not (and (= (len x) 3) (equal outs (list (caddr x))) (equal (g-obj (car x) st) (g-obj (caddr x) st)))) (mv :stobj nil cnt locs)
       (mv-let (e s c ty cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
         (if (or e (not (eq ty :int64))) (mv (or e :type) nil cnt locs)
           (mv-let (e si cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs)
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
                       (mv-let (e ss cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs)
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
           (mv-let (e sa cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs)
             (if e (mv e nil cnt locs)
               (mv-let (e sb cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs)
                 (if e (mv e nil cnt locs)
                   (mv nil (append sc (list (list :if cc sa sb))) cnt locs)))))))))
    ((consp (car x))
     ; ((lambda vars body) . args): the values first, read in the outer scope,
     ; then the stobjs' updates -- translated, as acl2-fortran does, with the
     ; new values in scope (GEN.md's finding) -- then the body
     (let ((vars (kadr (car x))) (body (kaddr (car x))))
       (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                     (no-duplicatesp-eq vars) (= (len vars) (len (cdr x))) (not (member-eq 'mv vars))))
           (mv :stobj nil cnt locs)
         (mv-let (e s binds cnt locs) (g-svals vars (cdr x) em cnt locs sigs fnames st)
           (if e (mv e nil cnt locs)
             (mv-let (e sa cnt locs) (g-sacts vars (cdr x) (append binds em) cnt locs sigs fnames st)
               (if e (mv e nil cnt locs)
                 (mv-let (e sb cnt locs) (g-stmt body (append binds em) cnt locs sigs fnames st outs)
                   (if e (mv e nil cnt locs)
                     (mv nil (append s sa sb) cnt locs))))))))))
    (t (mv :stobj nil cnt locs))))
 (defun g-sacts (vars xs em cnt locs sigs fnames st)
   ; each stobj var bound to a different term: that term's statements
   (declare (xargs :guard t :measure (acl2-count xs)))
   (cond ((or (atom vars) (atom xs)) (mv nil nil cnt locs))
         ((and (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))))
          (mv-let (e s cnt locs) (g-stmt (car xs) em cnt locs sigs fnames st (list (car vars)))
            (if e (mv e nil cnt locs)
              (mv-let (e ss cnt locs) (g-sacts (cdr vars) (cdr xs) em cnt locs sigs fnames st)
                (mv e (append s ss) cnt locs)))))
         (t (g-sacts (cdr vars) (cdr xs) em cnt locs sigs fnames st)))))

; ---- a subroutine: raw is ACL2's hand-over (fn formals stobjs-out guards-verified body)

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
  ; every result a stobj (mv and intent(out) results: not yet)
  (if (atom outs) (null outs) (and (eq (g-role (car outs) st) :stobj) (g-st-outs-ok (cdr outs) st))))

(defun g-st-fn (r defs sigs st)
  (let* ((fn (kar r)) (formals (kadr r)) (outs (kaddr r)) (body (nth 4 (true-list-fix r)))
         (vals (g-st-vals formals st)) (fnames (g-formals vals)))
    (if (not (and (symbol-listp formals) (no-duplicatesp-equal formals) (eq (kadddr r) t)
                  (consp outs) (g-st-outs-ok outs st) (no-duplicatesp-equal fnames)))
        (mv :formals nil)
      (mv-let (e stmts cnt locs) (g-stmt body (g-em vals) 0 nil sigs fnames st outs)
        (declare (ignore cnt))
        (if e (mv e nil)
          (mv nil (list :subroutine (g-sym fn nil)
                        (if (g-reaches (g-called (strip-cars sigs) (g-fcalls stmts)) fn defs (1+ (len defs))) t nil)
                        (append (g-st-dummies formals outs st) (g-dummies vals))
                        (g-locals locs) stmts)))))))

(defun g-st-procs (raw fns defs sigs st)
  ; (mv err procs) for the fns of raw, in fns' order
  (if (atom fns) (mv nil nil)
    (mv-let (e p) (g-st-fn (assoc-eq (car fns) raw) defs sigs st)
      (if e (mv (list e (car fns)) nil)
        (mv-let (e ps) (g-st-procs raw (cdr fns) defs sigs st)
          (mv e (cons p ps)))))))

(defun g-st-module (raw bools fns st)
  (g-st-procs raw fns (g-defs raw) (g-sigs raw bools) st))

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
