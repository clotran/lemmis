; fprog: program units over statements (Stage A, item 1, the outer layer):
; the grammar (fgu, fyu) over the statement trees fstmt.lisp's fps
; answers, and its parser fpu, proved to accept exactly it. A unit's
; spelling is its list of statements.
;
;   fpu-sound     on statement trees (stmts-p), what fpu answers is a tree
;                 of the grammar, and spells the statements it consumed
;   fpu-complete  on the statements any tree spells, followed by what
;                 may follow it (ufollow-ok), fpu answers that tree
;   fpu-cost      a successful parse makes at most 32 calls per statement
;                 it consumes, plus fpu-d nt
;
;  :program (unit ...) nonempty      R501 program: program-unit [program-unit]...
;  :unit  (:main hd spec exec int end)   R1401 main-program (the subset
;                                    requires the program-stmt hd), R502
;         (:module hd spec int end)  R1404 module: module-stmt
;                                    [specification-part]
;                                    [module-subprogram-part] end-module-stmt
;         (:proc hd spec exec int end)   R1532 function-subprogram, R1537
;                                    subroutine-subprogram (R503
;                                    external-subprogram): hd a function-
;                                    or subroutine-stmt
;  :spec  (uses imp decls)           R504 specification-part: [use-stmt]...
;                                    [implicit-part] [declaration-construct]...
;                                    (R505 implicit-part, here IMPLICIT NONE or
;                                    nothing; R507 declaration-construct, here
;                                    type-declaration-stmt)
;  :exec  (c ...)                    R509 execution-part, R1101 block: each c
;                                    an executable-construct (R514)
;  :c     (:act s)                   an action-stmt (R515)
;         (:ifc e blk eifs els)      R1136 if-construct: if-then-stmt block
;                                    [else-if-stmt block]... [else-stmt block]
;                                    end-if-stmt; eifs ((e blk) ...), els nil
;                                    or (blk)
;         (:doc ctl blk)             R1119 do-construct: do-stmt block end-do
;                                    (R1133 end-do: end-do-stmt)
;         (:casec e arms)           R1142 case-construct: select-case-stmt
;                                   [case-stmt block]... end-select-stmt;
;                                   arms ((cs blk) ...), cs a CASE statement,
;                                   at most one CASE DEFAULT (C1151)
;  :int   nil or (:has (sub ...))    R511 internal-subprogram-part,
;                                    R1407 module-subprogram-part:
;                                    contains-stmt [subprogram]...; nil when
;                                    there is no CONTAINS
;
; The end statement's name, when written, is the unit's (C1402, C1404,
; C1567, C1571); its kind word is the unit's.

(in-package "ACL2")

(include-book "fstmt")

(defun stmt-tag (s) (declare (xargs :guard t)) (kar s))

(defun hd-name (hd) (declare (xargs :guard t))
  (case (kar hd) ((:program :module) (kadr hd)) (otherwise (kaddr hd))))

(defun unit-kind (hd) (declare (xargs :guard t))
  (case (kar hd) (:program "program") (:module "module") (:function "function") (otherwise "subroutine")))

(defun end-ok (end hd)             ; END [kind [name]] matching the unit
  (declare (xargs :guard t))
  (and (true-listp end) (= (len end) 3) (eq (car end) :end)
       (or (null (cadr end))
           (and (equal (cadr end) (unit-kind hd))
                (or (null (caddr end)) (equal (caddr end) (hd-name hd)))))))

(defun action-stmt-p (s)          ; R515 action-stmt, the logical IF one of them
  (declare (xargs :guard t))
  (and (fgs :stmt s) (member-eq (kar s) (quote (:assign :simple :call :print :if))) t))

(defun count-defaults (arms)
  (declare (xargs :guard t))
  (if (atom arms) 0 (+ (if (equal (kar (car arms)) '(:case-default)) 1 0) (count-defaults (cdr arms)))))

(defun fgu-measure (nt x)
  (declare (xargs :guard t))
  (+ (* 4 (acl2-count x)) (case nt (:program 2) (:unit 1) (otherwise 0))))

(defun fgu (nt x)
  (declare (xargs :guard t :measure (fgu-measure nt x)))
  (case nt
    (:program (and (consp x) (fgu :units x)))
    (:units (if (atom x) (null x) (and (fgu :unit (car x)) (fgu :units (cdr x)))))
    (:unit (and (true-listp x)
                (case (car x)
                  (:main (and (= (len x) 6) (equal (kar (cadr x)) :program) (fgs :stmt (cadr x))
                              (fgu :spec (caddr x)) (fgu :exec (cadddr x)) (fgu :int (car (cddddr x)))
                              (end-ok (cadr (cddddr x)) (cadr x))))
                  (:module (and (= (len x) 5) (equal (kar (cadr x)) :module) (fgs :stmt (cadr x))
                                (fgu :spec (caddr x)) (fgu :int (cadddr x))
                                (end-ok (car (cddddr x)) (cadr x))))
                  (:proc (and (= (len x) 6) (fgu :sub x)))
                  (otherwise nil))))
    (:sub (and (true-listp x) (= (len x) 6) (eq (car x) :proc)
               (member-eq (kar (cadr x)) '(:function :subroutine)) (fgs :stmt (cadr x))
               (fgu :spec (caddr x)) (fgu :exec (cadddr x)) (fgu :int (car (cddddr x)))
               (end-ok (cadr (cddddr x)) (cadr x))))
    (:spec (and (true-listp x) (= (len x) 3)
                (fgu :uses (car x))
                (or (null (cadr x)) (equal (cadr x) '(:implicit-none)))
                (fgu :decls (caddr x))))
    (:uses (if (atom x) (null x) (and (equal (kar (car x)) :use) (fgs :stmt (car x)) (fgu :uses (cdr x)))))
    (:decls (if (atom x) (null x) (and (equal (kar (car x)) :decl) (fgs :stmt (car x)) (fgu :decls (cdr x)))))
    (:exec (if (atom x) (null x) (and (fgu :c (car x)) (fgu :exec (cdr x)))))
    (:c (and (true-listp x)
             (case (car x)
               (:act (and (= (len x) 2) (action-stmt-p (cadr x))))
               (:ifc (and (= (len x) 5) (fg :expr (cadr x)) (fgu :exec (caddr x))
                          (fgu :eifs (cadddr x))
                          (or (null (car (cddddr x)))
                              (and (true-listp (car (cddddr x))) (= (len (car (cddddr x))) 1)
                                   (fgu :exec (car (car (cddddr x))))))))
               (:doc (and (= (len x) 3) (fgs :ctl (cadr x)) (fgu :exec (caddr x))))
               (:casec (and (= (len x) 3) (fg :expr (cadr x)) (fgu :arms (caddr x)) (<= (count-defaults (caddr x)) 1)))
               (otherwise nil))))
    (:arms (if (atom x) (null x)
             (and (true-listp (car x)) (= (len (car x)) 2) (member-eq (kar (caar x)) '(:case :case-default))
                  (fgs :stmt (caar x)) (fgu :exec (cadar x)) (fgu :arms (cdr x)))))
    (:eifs (if (atom x) (null x)
             (and (true-listp (car x)) (= (len (car x)) 2) (fg :expr (caar x)) (fgu :exec (cadar x))
                  (fgu :eifs (cdr x)))))
    (:int (or (null x) (and (true-listp x) (= (len x) 2) (eq (car x) :has) (fgu :subs (cadr x)))))
    (:subs (if (atom x) (null x) (and (fgu :sub (car x)) (fgu :subs (cdr x)))))
    (otherwise nil)))

; the statements a tree spells
(defun fyu (nt x)
  (declare (xargs :guard t :measure (fgu-measure nt x)))
  (case nt
    ((:program :units :exec :uses :decls :subs)
     (if (atom x) nil
       (append (case nt ((:program :units) (fyu :unit (car x))) (:exec (fyu :c (car x)))
                 (:subs (fyu :sub (car x))) (otherwise (list (car x))))
               (fyu nt (cdr x)))))
    ((:unit :sub)
     (if (atom x) nil
       (if (eq (car x) :module)
           (append (list (kadr x)) (fyu :spec (kaddr x)) (fyu :int (kadddr x)) (list (kar (kdr (kdr (kdr (kdr x)))))))
         (append (list (kadr x)) (fyu :spec (kaddr x)) (fyu :exec (kadddr x))
                 (fyu :int (kar (kdr (kdr (kdr (kdr x)))))) (list (kadr (kdr (kdr (kdr (kdr x))))))))))
    (:spec (if (atom x) nil
             (append (fyu :uses (car x)) (if (kadr x) (list (kadr x)) nil) (fyu :decls (kaddr x)))))
    (:c (if (atom x) nil
          (case (car x)
            (:act (list (kadr x)))
            (:ifc (append (list (list :if-then (kadr x))) (fyu :exec (kaddr x)) (fyu :eifs (kadddr x))
                          (if (kar (kdr (kdr (kdr (kdr x)))))
                              (cons '(:else) (fyu :exec (kar (kar (kdr (kdr (kdr (kdr x)))))))) nil)
                          (list '(:end "if" nil))))
            (:casec (append (list (list :select (kadr x))) (fyu :arms (kaddr x)) (list '(:end "select" nil))))
            (otherwise (append (list (list :do (kadr x))) (fyu :exec (kaddr x)) (list '(:end "do" nil)))))))
    (:arms (if (atom x) nil (append (list (kar (car x))) (fyu :exec (kadr (car x))) (fyu :arms (cdr x)))))
    (:eifs (if (atom x) nil
             (append (list (list :else-if (kar (car x)))) (fyu :exec (kadr (car x))) (fyu :eifs (cdr x)))))
    (:int (if (atom x) nil (cons '(:contains) (fyu :subs (kadr x)))))
    (otherwise nil)))

; ---- the parser, over statement trees

(defun c-start-p (s)               ; a statement that begins an executable construct
  (declare (xargs :guard t))
  (and (member-eq (kar s) '(:assign :simple :call :print :if :if-then :do :select)) t))

(defun fpu-rank (nt)
  (declare (xargs :guard t))
  (case nt (:program 7) (:units 6) (:unit 5) (:subs 4) (:sub 3) ((:spec :exec) 2) (otherwise 1)))

(defun fpu (nt toks)
  (declare (xargs :guard t :measure (+ (* 8 (len toks)) (fpu-rank nt)) :verify-guards nil))
  (let ((s (kar toks)))
    (case nt
      (:program (mv-let (ok us r) (fpu :units toks) (if (and ok (consp us)) (mv t us r) (fail))))
      (:units (if (atom toks) (mv t nil toks)
                (mv-let (ok u r) (fpu :unit toks)
                  (if (not (and ok (< (len r) (len toks)))) (fail)
                    (mv-let (ok2 us r2) (fpu :units r) (if ok2 (mv t (cons u us) r2) (fail)))))))
      ((:unit :sub)
       (if (not (if (eq nt :unit) (member-eq (kar s) '(:program :module :function :subroutine))
                  (member-eq (kar s) '(:function :subroutine))))
           (fail)
         (mv-let (ok sp r) (fpu :spec (cdr toks))
           (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
             (mv-let (ok2 ex r2) (if (eq (kar s) :module) (mv t nil r) (fpu :exec r))
               (if (not (and ok2 (<= (len r2) (len r)))) (fail)
                 (mv-let (ok3 in r3) (fpu :int r2)
                   (if (not (and ok3 (consp r3) (end-ok (car r3) s))) (fail)
                     (mv t (case (kar s)
                             (:program (list :main s sp ex in (car r3)))
                             (:module (list :module s sp in (car r3)))
                             (otherwise (list :proc s sp ex in (car r3))))
                         (cdr r3))))))))))
      (:spec (mv-let (ok us r) (fpu :uses toks)
               (if (not (and ok (<= (len r) (len toks)))) (fail)
                 (let* ((imp (if (equal (kar r) '(:implicit-none)) (car r) nil))
                        (r1 (if imp (cdr r) r)))
                   (mv-let (ok2 ds r2) (fpu :decls r1)
                     (if ok2 (mv t (list us imp ds) r2) (fail)))))))
      ((:uses :decls)
       (if (and (consp toks) (eq (kar s) (if (eq nt :uses) :use :decl)))
           (mv-let (ok xs r) (fpu nt (cdr toks)) (if ok (mv t (cons s xs) r) (fail)))
         (mv t nil toks)))
      (:exec (if (c-start-p s)
                 (mv-let (ok c r) (fpu :c toks)
                   (if (not (and ok (< (len r) (len toks)))) (fail)
                     (mv-let (ok2 cs r2) (fpu :exec r) (if ok2 (mv t (cons c cs) r2) (fail)))))
               (mv t nil toks)))
      (:c (case (kar s)
            (:if-then
             (mv-let (ok blk r) (fpu :exec (cdr toks))
               (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
                 (mv-let (ok2 eifs r2) (fpu :eifs r)
                   (if (not (and ok2 (<= (len r2) (len r)))) (fail)
                     (mv-let (ok3 els r3)
                       (if (equal (kar r2) '(:else))
                           (mv-let (ok4 b r4) (fpu :exec (cdr r2)) (mv ok4 (list b) r4))
                         (mv t nil r2))
                       (if (and ok3 (equal (kar r3) '(:end "if" nil)))
                           (mv t (list :ifc (kadr s) blk eifs els) (cdr r3))
                         (fail))))))))
            (:do (mv-let (ok blk r) (fpu :exec (cdr toks))
                   (if (and ok (equal (kar r) '(:end "do" nil)))
                       (mv t (list :doc (kadr s) blk) (cdr r))
                     (fail))))
            (:select (mv-let (ok arms r) (fpu :arms (cdr toks))
                       (if (and ok (equal (kar r) '(:end "select" nil)) (<= (count-defaults arms) 1))
                           (mv t (list :casec (kadr s) arms) (cdr r))
                         (fail))))
            (otherwise (if (c-start-p s) (mv t (list :act s) (cdr toks)) (fail)))))
      (:arms (if (member-eq (kar s) '(:case :case-default))
                 (mv-let (ok blk r) (fpu :exec (cdr toks))
                   (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
                     (mv-let (ok2 as r2) (fpu :arms r)
                       (if ok2 (mv t (cons (list s blk) as) r2) (fail)))))
               (mv t nil toks)))
      (:eifs (if (eq (kar s) :else-if)
                 (mv-let (ok blk r) (fpu :exec (cdr toks))
                   (if (not (and ok (<= (len r) (len (cdr toks))))) (fail)
                     (mv-let (ok2 es r2) (fpu :eifs r)
                       (if ok2 (mv t (cons (list (kadr s) blk) es) r2) (fail)))))
               (mv t nil toks)))
      (:int (if (equal s '(:contains))
                (mv-let (ok ss r) (fpu :subs (cdr toks)) (if ok (mv t (list :has ss) r) (fail)))
              (mv t nil toks)))
      (:subs (if (member-eq (kar s) '(:function :subroutine))
                 (mv-let (ok u r) (fpu :sub toks)
                   (if (not (and ok (< (len r) (len toks)))) (fail)
                     (mv-let (ok2 us r2) (fpu :subs r) (if ok2 (mv t (cons u us) r2) (fail)))))
               (mv t nil toks)))
      (otherwise (fail)))))

; ---- soundness: what fpu reads, from statement trees, is a tree of its nt,
;      and spells what it read

(defun stmts-p (xs)                ; each a statement tree, as fps answers
  (declare (xargs :guard t))
  (if (atom xs) t (and (fgs :stmt (car xs)) (stmts-p (cdr xs)))))

(defthm stmts-p-cdr (implies (stmts-p xs) (stmts-p (cdr xs))))
(defthm stmts-p-car (implies (and (stmts-p xs) (consp xs)) (fgs :stmt (car xs))))

(defthm fgs-construct-heads
  (implies (fgs :stmt s)
           (and (implies (equal (car s) :if-then) (and (consp (cdr s)) (fg :expr (cadr s)) (equal (list :if-then (cadr s)) s)))
                (implies (equal (car s) :else-if) (and (consp (cdr s)) (fg :expr (cadr s)) (equal (list :else-if (cadr s)) s)))
                (implies (equal (car s) :do) (and (consp (cdr s)) (fgs :ctl (cadr s)) (equal (list :do (cadr s)) s)))
                (implies (equal (car s) :select) (and (consp (cdr s)) (fg :expr (cadr s)) (equal (list :select (cadr s)) s)))))
  :hints (("Goal" :expand ((fgs :stmt s)))))

; the statement layer is opaque here: its trees are tokens
(in-theory (disable parts-shape fgs-cons-open fys-cons-open fgs-var-open fys-var-open sfollow-facts nonempty-parts
                    tok-facts fg-expr-consp fg-args-true-listp names-p len-cdr-consp fgs-fys-aliases end-ok))

; fgu, fyu and fpu open only on a tree or tokens being built, or where a
; proof step names them
(defmacro def-ucons-opener (name call v)
  `(make-event
    (let ((fn (car ',call)))
      `(defthm ,',name
         (implies (syntaxp (and (quotep nt) (consp ,',v) (member-eq (car ,',v) '(cons quote))))
                  (equal ,',call ,(body fn nil (w state))))
         :hints (("Goal" :expand (,',call)))))))
(def-ucons-opener fgu-cons-open (fgu nt x) x)
(def-ucons-opener fyu-cons-open (fyu nt x) x)
; fpu opens on tokens being built: a cons, or the spelling of a tree of
; another nt; never on (append (fyu 'nt y) r), which an induction answers
(make-event
 `(defthm fpu-open
    (implies (syntaxp (and (quotep nt) (consp toks)
                           (or (member-eq (car toks) '(cons quote))
                               (and (eq (car toks) 'binary-append) (consp (cadr toks)) (eq (car (cadr toks)) 'fyu)
                                    (not (equal (cadr (cadr toks)) nt))))))
             (equal (fpu nt toks) ,(body 'fpu nil (w state))))
    :hints (("Goal" :expand ((fpu nt toks))))))
(in-theory (disable (:definition fgu) (:definition fyu) (:definition fpu)))

; each induction step expands the calls its conclusion is about, at its nts
(defun fpu-step-hint (id clause calls)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :pool-lst) '(1))
       (equal (len (access clause-id id :case-lst)) 1)
       (equal (access clause-id id :primes) 0)
       (let* ((cs (case-nts clause))
              (cs (if (member-equal '':unit cs) (cons '':sub cs) cs)))
         (list :expand (if cs (loop$ for c in cs append
                                    (loop$ for call in calls collect (cons (car call) (cons c (cddr call)))))
                         calls)))))

; a program is its units
(defthm fgu-program (equal (fgu :program x) (and (consp x) (fgu :units x))) :hints (("Goal" :expand ((fgu :program x)))))
(defthm fyu-program (equal (fyu :program x) (fyu :units x))
  :hints (("Goal" :induct (len x) :expand ((fyu :program x) (fyu :units x)))))

(defthm fpu-rest-stmts
  (implies (stmts-p toks) (stmts-p (mv-nth 2 (fpu nt toks))))
  :hints (("Goal" :induct (fpu nt toks) :in-theory (enable member-equal))
          (fpu-step-hint id clause '((fpu nt toks)))))

(defthm fpu-sound
  (implies (and (stmts-p toks) (mv-nth 0 (fpu nt toks)))
           (and (fgu nt (mv-nth 1 (fpu nt toks)))
                (equal (append (fyu nt (mv-nth 1 (fpu nt toks))) (mv-nth 2 (fpu nt toks))) toks)))
  :hints (("Goal" :induct (fpu nt toks) :in-theory (enable member-equal))
          (fpu-step-hint id clause '((fpu nt toks)))))

; ---- completeness: a tree's statements, followed by what may follow its
;      nt, parse back to it

(defun ucont-p (nt s)              ; s would continue a phrase of nt
  (declare (xargs :guard t))
  (case nt
    (:exec (c-start-p s))
    (:uses (eq (kar s) :use))
    (:decls (eq (kar s) :decl))
    (:spec (or (member-eq (kar s) '(:use :decl)) (equal s '(:implicit-none))))
    (:eifs (or (eq (kar s) :else-if) (c-start-p s)))   ; its last block's statements too
    (:arms (or (member-eq (kar s) '(:case :case-default)) (c-start-p s)))
    (:int (or (equal s '(:contains)) (member-eq (kar s) '(:function :subroutine))))
    (:subs (member-eq (kar s) '(:function :subroutine)))
    (otherwise nil)))

(defun ufollow-ok (nt r)
  (declare (xargs :guard t))
  (if (member-eq nt '(:program :units)) (atom r) (not (ucont-p nt (kar r)))))

(defun fgu-ind (nt x r)
  (declare (xargs :guard t :measure (fgu-measure nt x) :verify-guards nil))
  (if (atom x) r
  (case nt
    (:program (fgu-ind :units x r))
    ((:units :exec :subs)
     (if (atom x) r
       (list (fgu-ind (case nt (:units :unit) (:exec :c) (otherwise :sub)) (car x) (append (fyu nt (cdr x)) r))
             (fgu-ind nt (cdr x) r))))
    ((:uses :decls) (if (atom x) r (fgu-ind nt (cdr x) r)))
    ((:unit :sub)
     (if (eq (kar x) :module)
         (let ((tl (cons (kar (kdr (kdr (kdr (kdr x))))) r)))
           (list (fgu-ind :spec (kaddr x) (append (fyu :int (kadddr x)) tl))
                 (fgu-ind :int (kadddr x) tl)))
       (let ((tl (cons (kadr (kdr (kdr (kdr (kdr x))))) r)) (in (kar (kdr (kdr (kdr (kdr x)))))))
         (list (fgu-ind :spec (kaddr x) (append (fyu :exec (kadddr x)) (append (fyu :int in) tl)))
               (fgu-ind :exec (kadddr x) (append (fyu :int in) tl))
               (fgu-ind :int in tl)))))
    (:spec (list (fgu-ind :uses (kar x) (append (if (kadr x) (list (kadr x)) nil) (append (fyu :decls (kaddr x)) r)))
                 (fgu-ind :decls (kaddr x) r)))
    (:c (case (kar x)
          (:ifc (let* ((els (kar (kdr (kdr (kdr (kdr x))))))
                       (tl (cons '(:end "if" nil) r))
                       (ep (if els (cons '(:else) (append (fyu :exec (kar els)) tl)) tl)))
                  (list (fgu-ind :exec (kaddr x) (append (fyu :eifs (kadddr x)) ep))
                        (fgu-ind :eifs (kadddr x) ep)
                        (fgu-ind :exec (kar els) tl))))
          (:doc (fgu-ind :exec (kaddr x) (cons '(:end "do" nil) r)))
          (:casec (fgu-ind :arms (kaddr x) (cons '(:end "select" nil) r)))
          (otherwise r)))
    (:arms (if (atom x) r
             (list (fgu-ind :exec (kadr (car x)) (append (fyu :arms (cdr x)) r))
                   (fgu-ind :arms (cdr x) r))))
    (:eifs (if (atom x) r
             (list (fgu-ind :exec (kadr (car x)) (append (fyu :eifs (cdr x)) r))
                   (fgu-ind :eifs (cdr x) r))))
    (:int (fgu-ind :subs (kadr x) r))
    (otherwise r))))

(local (in-theory (enable member-equal)))
; nothing is spelled by an atom, and an atom is an empty list's tree
(defthm fyu-atom (implies (atom x) (equal (fyu nt x) nil)) :hints (("Goal" :expand ((fyu nt x)))))
(defthm fgu-atom
  (implies (atom x) (equal (fgu nt x) (and (null x) (member-eq nt '(:units :exec :uses :decls :eifs :int :subs :arms)) t)))
  :hints (("Goal" :expand ((fgu nt x)))))

; on no statements
(defthm fpu-atom
  (implies (atom toks)
           (equal (fpu nt toks)
                  (cond ((member-eq nt '(:units :uses :decls :exec :eifs :int :subs :arms)) (mv t nil toks))
                        ((eq nt :spec) (mv t (list nil nil nil) toks))
                        (t (mv nil nil toks)))))
  :hints (("Goal" :expand ((fpu nt toks) (fpu :units toks) (fpu :uses toks) (fpu :decls toks)))))

; what fpu leaves is no longer than what it was given, and shorter after
; a unit, a subprogram or a construct
(defthm fpu-len
  (<= (len (mv-nth 2 (fpu nt toks))) (len toks))
  :rule-classes :linear
  :hints (("Goal" :induct (fpu nt toks)) (fpu-step-hint id clause '((fpu nt toks)))))
(defthm fpu-len-strict
  (implies (and (mv-nth 0 (fpu nt toks)) (member-eq nt '(:c :unit :sub)))
           (< (len (mv-nth 2 (fpu nt toks))) (len toks)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable len-cdr-consp) :cases ((equal nt :c) (equal nt :unit) (equal nt :sub)))
          ("Subgoal 3" :expand ((fpu :c toks)))
          ("Subgoal 2" :expand ((fpu :unit toks)))
          ("Subgoal 1" :expand ((fpu :sub toks)))))

; an end statement is one
(defthm end-ok-end (implies (end-ok e hd) (and (consp e) (equal (car e) :end)))
  :rule-classes (:rewrite :forward-chaining) :hints (("Goal" :in-theory (enable end-ok))))

(defthm car-append-u (equal (car (append a b)) (if (consp a) (car a) (car b))))
(defthm len-append-u (equal (len (append a b)) (+ (len a) (len b))))

(defthm fyu-uses-first
  (implies (fgu :uses x)
           (and (equal (consp (fyu :uses x)) (consp x))
                (implies (consp x) (and (consp (car (fyu :uses x))) (equal (car (car (fyu :uses x))) :use)))))
  :hints (("Goal" :expand ((fgu :uses x) (fyu :uses x)))))
(defthm fyu-decls-first
  (implies (fgu :decls x)
           (and (equal (consp (fyu :decls x)) (consp x))
                (implies (consp x) (and (consp (car (fyu :decls x))) (equal (car (car (fyu :decls x))) :decl)))))
  :hints (("Goal" :expand ((fgu :decls x) (fyu :decls x)))))

(defthm fyu-c-first
  (implies (fgu :c x) (and (consp (fyu :c x)) (c-start-p (car (fyu :c x)))))
  :hints (("Goal" :expand ((fgu :c x) (fyu :c x)))))

(defthm fyu-exec-first
  (implies (fgu :exec x)
           (and (equal (consp (fyu :exec x)) (consp x))
                (implies (consp x) (c-start-p (car (fyu :exec x))))))
  :hints (("Goal" :expand ((fgu :exec x) (fyu :exec x)))))

(defthm fyu-unit-first
  (implies (or (fgu :unit x) (fgu :sub x))
           (and (consp (fyu :unit x)) (consp (fyu :sub x))
                (equal (car (fyu :unit x)) (cadr x)) (equal (car (fyu :sub x)) (cadr x))))
  :hints (("Goal" :expand ((fgu :unit x) (fgu :sub x) (fyu :unit x) (fyu :sub x)))))

(defthm fyu-subs-first
  (implies (fgu :subs x)
           (and (equal (consp (fyu :subs x)) (consp x))
                (implies (consp x) (member-equal (kar (car (fyu :subs x))) '(:function :subroutine)))))
  :hints (("Goal" :expand ((fgu :subs x) (fyu :subs x) (fgu :sub (car x))) :in-theory (enable member-equal))))

(defthm fyu-int-first
  (implies (fgu :int x)
           (and (equal (consp (fyu :int x)) (consp x))
                (implies (consp x) (equal (car (fyu :int x)) '(:contains)))))
  :hints (("Goal" :expand ((fgu :int x) (fyu :int x)))))

(defthm fyu-arms-first
  (implies (fgu :arms x)
           (and (equal (consp (fyu :arms x)) (consp x))
                (implies (consp x) (and (consp (car (fyu :arms x))) (member-equal (car (car (fyu :arms x))) '(:case :case-default))))))
  :hints (("Goal" :expand ((fgu :arms x) (fyu :arms x)))))

(defthm fyu-eifs-first
  (implies (fgu :eifs x)
           (and (equal (consp (fyu :eifs x)) (consp x))
                (implies (consp x) (equal (car (fyu :eifs x)) (list :else-if (caar x))))))
  :hints (("Goal" :expand ((fgu :eifs x) (fyu :eifs x)))))

; a construct, a unit and a subprogram each spell a statement at least
(defthm fyu-len-pos
  (and (implies (fgu :c x) (< 0 (len (fyu :c x))))
       (implies (or (fgu :unit x) (fgu :sub x)) (and (< 0 (len (fyu :unit x))) (< 0 (len (fyu :sub x))))))
  :rule-classes :linear
  :hints (("Goal" :use (fyu-c-first fyu-unit-first) :in-theory (disable fyu-c-first fyu-unit-first)
           :expand ((len (fyu :c x)) (len (fyu :unit x)) (len (fyu :sub x))))))

; an induction hypothesis (equal (fpu c T) (mv t y R)) says how long fpu's
; rest is, and that it succeeded: stated where linear arithmetic sees it
(defthm fpu-ih-facts
  (implies (equal a v)
           (and (equal (len (mv-nth 2 a)) (len (mv-nth 2 v)))
                (iff (mv-nth 0 a) (mv-nth 0 v))))
  :rule-classes nil)

(defun ih-uses (clause)
  (declare (xargs :mode :program))
  (cond ((atom clause) nil)
        ((and (consp (car clause)) (eq (caar clause) 'not)
              (consp (cadar clause)) (eq (car (cadar clause)) 'equal)
              (consp (cadr (cadar clause))) (eq (car (cadr (cadar clause))) 'fpu))
         (cons (list :instance 'fpu-ih-facts (list 'a (cadr (cadar clause))) (list 'v (caddr (cadar clause))))
               (ih-uses (cdr clause))))
        (t (ih-uses (cdr clause)))))

(defun ih-use-hint (clause stable)
  (declare (xargs :mode :program))
  (and stable (let ((us (ih-uses clause))) (and us (list :use us)))))

; on the statements any tree spells, followed by what may follow it, fpu
; answers that tree: the grammar is unambiguous, and fpu accepts all of it
(defthm fpu-complete
  (implies (and (fgu nt x) (ufollow-ok nt r))
           (equal (fpu nt (append (fyu nt x) r)) (mv t x r)))
  :hints (("Goal" :induct (fgu-ind nt x r) :in-theory (enable member-equal))
          (fpu-step-hint id clause '((fgu nt x) (fyu nt x)))
          (ih-use-hint clause stable-under-simplificationp)))

; ---- cost: fpu-steps counts fpu's calls (generated: bb mksteps.bb fprog.lisp fpu fpu-steps)

(defun
 fpu-steps
 (nt toks)
 (declare (xargs :guard t :measure (+ (* 8 (len toks)) (fpu-rank nt)) :verify-guards nil))
 (let
  ((s (kar toks)))
  (case
   nt
   (:program
    (mv-let
     (ok us r)
     (fpu :units toks)
     (declare (ignorable ok us r))
     (let ((c1 (fpu-steps :units toks))) (if (and ok (consp us)) (+ 1 c1) (+ 1 c1)))))
   (:units
    (if
     (atom toks)
     (+ 1)
     (mv-let
      (ok u r)
      (fpu :unit toks)
      (declare (ignorable ok u r))
      (let
       ((c2 (fpu-steps :unit toks)))
       (if
        (not (and ok (< (len r) (len toks))))
        (+ 1 c2)
        (mv-let
         (ok2 us r2)
         (fpu :units r)
         (declare (ignorable ok2 us r2))
         (let ((c3 (fpu-steps :units r))) (if ok2 (+ 1 c3 c2) (+ 1 c3 c2)))))))))
   ((:unit :sub)
    (if
     (not
      (if
       (eq nt :unit)
       (member-eq (kar s) ' (:program :module :function :subroutine))
       (member-eq (kar s) ' (:function :subroutine))))
     (+ 1)
     (mv-let
      (ok sp r)
      (fpu :spec (cdr toks))
      (declare (ignorable ok sp r))
      (let
       ((c4 (fpu-steps :spec (cdr toks))))
       (if
        (not (and ok (<= (len r) (len (cdr toks)))))
        (+ 1 c4)
        (mv-let
         (ok2 ex r2)
         (if (eq (kar s) :module) (mv t nil r) (fpu :exec r))
         (declare (ignorable ok2 ex r2))
         (let
          ((c5 (if (eq (kar s) :module) 0 (fpu-steps :exec r))))
          (if
           (not (and ok2 (<= (len r2) (len r))))
           (+ 1 c5 c4)
           (mv-let
            (ok3 in r3)
            (fpu :int r2)
            (declare (ignorable ok3 in r3))
            (let
             ((c6 (fpu-steps :int r2)))
             (if (not (and ok3 (consp r3) (end-ok (car r3) s))) (+ 1 c6 c5 c4) (+ 1 c6 c5 c4))))))))))))
   (:spec
    (mv-let
     (ok us r)
     (fpu :uses toks)
     (declare (ignorable ok us r))
     (let
      ((c7 (fpu-steps :uses toks)))
      (if
       (not (and ok (<= (len r) (len toks))))
       (+ 1 c7)
       (let*
        ((imp (if (equal (kar r) ' (:implicit-none)) (car r) nil)) (r1 (if imp (cdr r) r)))
        (mv-let
         (ok2 ds r2)
         (fpu :decls r1)
         (declare (ignorable ok2 ds r2))
         (let ((c8 (fpu-steps :decls r1))) (if ok2 (+ 1 c8 c7) (+ 1 c8 c7)))))))))
   ((:uses :decls)
    (if
     (and (consp toks) (eq (kar s) (if (eq nt :uses) :use :decl)))
     (mv-let
      (ok xs r)
      (fpu nt (cdr toks))
      (declare (ignorable ok xs r))
      (let ((c9 (fpu-steps nt (cdr toks)))) (if ok (+ 1 c9) (+ 1 c9))))
     (+ 1)))
   (:exec
    (if
     (c-start-p s)
     (mv-let
      (ok c r)
      (fpu :c toks)
      (declare (ignorable ok c r))
      (let
       ((c10 (fpu-steps :c toks)))
       (if
        (not (and ok (< (len r) (len toks))))
        (+ 1 c10)
        (mv-let
         (ok2 cs r2)
         (fpu :exec r)
         (declare (ignorable ok2 cs r2))
         (let ((c11 (fpu-steps :exec r))) (if ok2 (+ 1 c11 c10) (+ 1 c11 c10)))))))
     (+ 1)))
   (:c
    (case
     (kar s)
     (:if-then
      (mv-let
       (ok blk r)
       (fpu :exec (cdr toks))
       (declare (ignorable ok blk r))
       (let
        ((c12 (fpu-steps :exec (cdr toks))))
        (if
         (not (and ok (<= (len r) (len (cdr toks)))))
         (+ 1 c12)
         (mv-let
          (ok2 eifs r2)
          (fpu :eifs r)
          (declare (ignorable ok2 eifs r2))
          (let
           ((c13 (fpu-steps :eifs r)))
           (if
            (not (and ok2 (<= (len r2) (len r))))
            (+ 1 c13 c12)
            (mv-let
             (ok3 els r3)
             (if
              (equal (kar r2) ' (:else))
              (mv-let (ok4 b r4) (fpu :exec (cdr r2)) (mv ok4 (list b) r4))
              (mv t nil r2))
             (declare (ignorable ok3 els r3))
             (let
              ((c14 (if (equal (kar r2) ' (:else)) (fpu-steps :exec (cdr r2)) 0)))
              (if (and ok3 (equal (kar r3) ' (:end "if" nil))) (+ 1 c14 c13 c12) (+ 1 c14 c13 c12)))))))))))
     (:do
      (mv-let
       (ok blk r)
       (fpu :exec (cdr toks))
       (declare (ignorable ok blk r))
       (let
        ((c15 (fpu-steps :exec (cdr toks))))
        (if (and ok (equal (kar r) ' (:end "do" nil))) (+ 1 c15) (+ 1 c15)))))
     (:select
      (mv-let
       (ok arms r)
       (fpu :arms (cdr toks))
       (declare (ignorable ok arms r))
       (let
        ((c16 (fpu-steps :arms (cdr toks))))
        (if
         (and ok (equal (kar r) ' (:end "select" nil)) (<= (count-defaults arms) 1))
         (+ 1 c16)
         (+ 1 c16)))))
     (otherwise (if (c-start-p s) (+ 1) (+ 1)))))
   (:arms
    (if
     (member-eq (kar s) ' (:case :case-default))
     (mv-let
      (ok blk r)
      (fpu :exec (cdr toks))
      (declare (ignorable ok blk r))
      (let
       ((c17 (fpu-steps :exec (cdr toks))))
       (if
        (not (and ok (<= (len r) (len (cdr toks)))))
        (+ 1 c17)
        (mv-let
         (ok2 as r2)
         (fpu :arms r)
         (declare (ignorable ok2 as r2))
         (let ((c18 (fpu-steps :arms r))) (if ok2 (+ 1 c18 c17) (+ 1 c18 c17)))))))
     (+ 1)))
   (:eifs
    (if
     (eq (kar s) :else-if)
     (mv-let
      (ok blk r)
      (fpu :exec (cdr toks))
      (declare (ignorable ok blk r))
      (let
       ((c19 (fpu-steps :exec (cdr toks))))
       (if
        (not (and ok (<= (len r) (len (cdr toks)))))
        (+ 1 c19)
        (mv-let
         (ok2 es r2)
         (fpu :eifs r)
         (declare (ignorable ok2 es r2))
         (let ((c20 (fpu-steps :eifs r))) (if ok2 (+ 1 c20 c19) (+ 1 c20 c19)))))))
     (+ 1)))
   (:int
    (if
     (equal s ' (:contains))
     (mv-let
      (ok ss r)
      (fpu :subs (cdr toks))
      (declare (ignorable ok ss r))
      (let ((c21 (fpu-steps :subs (cdr toks)))) (if ok (+ 1 c21) (+ 1 c21))))
     (+ 1)))
   (:subs
    (if
     (member-eq (kar s) ' (:function :subroutine))
     (mv-let
      (ok u r)
      (fpu :sub toks)
      (declare (ignorable ok u r))
      (let
       ((c22 (fpu-steps :sub toks)))
       (if
        (not (and ok (< (len r) (len toks))))
        (+ 1 c22)
        (mv-let
         (ok2 us r2)
         (fpu :subs r)
         (declare (ignorable ok2 us r2))
         (let ((c23 (fpu-steps :subs r))) (if ok2 (+ 1 c23 c22) (+ 1 c23 c22)))))))
     (+ 1)))
   (otherwise (+ 1)))))

(defthm fpu-steps-natp (natp (fpu-steps nt toks)) :rule-classes :type-prescription)

; the constant each nt adds; a unit, a subprogram and an executable
; construct always read their own first and last statements, so they owe
; less than nothing
(defun fpu-d (nt)
  (declare (xargs :guard t))
  (case nt (:program 8) (:spec 12) ((:unit :sub :c) -15) (otherwise 4)))

; a successful parse makes at most 32 calls per statement it consumes,
; plus fpu-d nt
(defthm fpu-cost
  (implies (mv-nth 0 (fpu nt toks))
           (<= (+ (fpu-steps nt toks) (* 32 (len (mv-nth 2 (fpu nt toks)))))
               (+ (* 32 (len toks)) (fpu-d nt))))
  :hints (("Goal" :induct (fpu-steps nt toks) :in-theory (enable member-equal len-cdr-consp))
          (fpu-step-hint id clause '((fpu nt toks) (fpu-steps nt toks)))))
