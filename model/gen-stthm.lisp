; gen-stthm: g-sexpr against a-sx on sx/sv, the whole theorem (GEN.md
; "What remains" 4 (a)): the-check and implies cases, then gs-sem for every
; call-free term by sn-ind, dispatching to the case lemmas of gen-stexp and
; gen-stlam.

(in-package "ACL2")

(include-book "gen-stlam")

; ---- the-check: its code is its last argument's, its value too

(defthm a-sx-the-check
  (implies (and (not-leaf) (eq (car x) 'the-check) (= (len x) 4) (not (car (a-sx x env s st defs n))))
           (and (not (car (a-sx (cadddr x) env s st defs (- n 4))))
                (equal (mv-nth 1 (a-sx x env s st defs n)) (mv-nth 1 (a-sx (cadddr x) env s st defs (- n 4))))))
  :hints (("Goal" :in-theory (e/d (kaddr kdr kar) (g-st-free g-role a-ev a-sx g-mvnth))
           :expand ((a-sx x env s st defs n) (a-sx-list (cdr x) env s st defs (1- n))
                    (a-sx-list (cddr x) env s st defs (+ -2 n)) (a-sx-list (cdddr x) env s st defs (+ -3 n))
                    (a-sx-list (cddddr x) env s st defs (+ -4 n)) (len x) (len (cdr x)) (len (cddr x))
                    (len (cdddr x)) (len (cddddr x))))))

(defthm no-calls-the-check
  (implies (and (consp x) (eq (car x) 'the-check) (= (len x) 4) (no-calls :term x sigs cs))
           (no-calls :term (cadddr x) sigs cs))
  :hints (("Goal" :expand ((no-calls :term x sigs cs) (no-calls :list (cdr x) sigs cs)
                           (no-calls :list (cddr x) sigs cs) (no-calls :list (cdddr x) sigs cs)))))

(defthm gsx-the-check
  (implies (and (not-leaf) (eq (car x) 'the-check)
                (gs-sem (cadddr x) em cnt locs sigs fnames st env s defs (- n 4) fr heap o))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((= (len x) 4))
           :expand ((gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
           :in-theory (disable g-sexpr a-sx sx-list sv no-calls em-ok decl-ok scalar-ok st-ok obj-is g-st-free
                               g-mvnth g-role gs-sem-use)
           :use ((:instance gs-sem-use (x (cadddr x)) (n (- n 4)))))))

; ---- implies: the if with else (:true)

(defthm a-sx-imp
  (implies (and (gs-impp x st) (not (car (a-sx x env s st defs n))))
           (and (not (car (a-sx (cadr x) env s st defs (- n 2))))
                (not (car (a-sx (caddr x) env s st defs (- n 3))))
                (equal (mv-nth 1 (a-sx x env s st defs n))
                       (implies (mv-nth 1 (a-sx (cadr x) env s st defs (- n 2)))
                                (mv-nth 1 (a-sx (caddr x) env s st defs (- n 3)))))))
  :hints (("Goal" :in-theory (e/d (kaddr kdr kar) (g-st-free g-role a-ev a-sx g-mvnth))
           :expand ((a-sx x env s st defs n) (a-sx-list (cdr x) env s st defs (1- n))
                    (a-sx-list (cddr x) env s st defs (+ -2 n)) (a-sx-list (cdddr x) env s st defs (+ -3 n))
                    (len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))))))

(defthm no-calls-imp
  (implies (and (gs-impp x st) (no-calls :term x sigs cs))
           (and (no-calls :term (cadr x) sigs cs) (no-calls :term (caddr x) sigs cs)))
  :hints (("Goal" :in-theory (disable g-st-free) :expand ((no-calls :term x sigs cs) (no-calls :list (cdr x) sigs cs)
                           (no-calls :list (cddr x) sigs cs) (no-calls :list (cdddr x) sigs cs)))))

(defthm sx-list-nil (equal (sx-list nil fr heap) (mv :normal fr heap)) :hints (("Goal" :expand ((sx-list nil fr heap)))))
(defthm sv-true (equal (sv '(:true) fr heap) (mv nil t)))


(defthm gsx-implies
  (implies (and (gs-impp x st)
                (gs-sem (cadr x) em cnt locs sigs fnames st env s defs (- n 2) fr heap o)
                (gs-sem (caddr x) em (j1 4) (j1 5) sigs fnames st env s defs (- n 3) (fr1) heap o)
                (sn-ok (cadr x) em cnt locs sigs fnames st)
                (sn-ok (caddr x) em (j1 4) (j1 5) sigs fnames st))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
           :cases ((and (mv-nth 1 (a-sx (cadr x) env s st defs (- n 2))) (booleanp (mv-nth 1 (a-sx (caddr x) env s st defs (- n 3)))))
                   (not (mv-nth 1 (a-sx (cadr x) env s st defs (- n 2)))))
           :in-theory (disable g-sexpr a-sx sx-list sx sv no-calls em-ok scalar-ok st-ok obj-is gs-impp
                               g-sexpr-imp if-stmts g-tmp nfix dty decl-ok-subset sif-glue sv-is-fv fv
                               sx-list-is-fx-list fx-list)
           :do-not (quote (eliminate-destructors generalize))
           :use ((:instance decl-ok-subset (a (j1 5)) (b (j2 5)))))))

; ---- the binds of a lambda bind no stobj var (g-svals skips them)

(set-irrelevant-formals-ok t)

(defun gsv-ind (vars xs em cnt locs sigs fnames st)
  (declare (xargs :measure (acl2-count xs) :hints (("Goal" :in-theory (disable g-role g-sexpr g-fresh)))))
  (cond ((or (atom vars) (atom xs)) nil)
        ((or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv))
         (gsv-ind (cdr vars) (cdr xs) em cnt locs sigs fnames st))
        (t (mv-let (e s1 c ty cnt1 locs1) (g-sexpr (car xs) em cnt locs sigs fnames st)
             (declare (ignore e s1 c))
             (mv-let (e tmp cnt2 locs2) (g-fresh (car vars) ty cnt1 locs1 (append fnames (em-names em)))
               (declare (ignore e tmp))
               (gsv-ind (cdr vars) (cdr xs) em cnt2 locs2 sigs fnames st))))))

(defthm em-nostobj-g-svals
  (em-nostobj (mv-nth 2 (g-svals vars xs em cnt locs sigs fnames st)) st)
  :hints (("Goal" :induct (gsv-ind vars xs em cnt locs sigs fnames st)
           :in-theory (disable g-role g-sexpr g-fresh))))

; ---- the cases the induction dispatches to, no-calls split inside

(defthm gs-err
  (implies (gsx 0) (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gs-sem) (g-sexpr a-sx sx-list sv)))))

(defthm gs-nocalls
  (implies (not (no-calls :term x sigs nil)) (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gs-sem) (g-sexpr a-sx sx-list sv no-calls)))))

(defthm gsa-nocalls
  (implies (not (no-calls :list xs sigs nil)) (gsa-sem xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gsa-sem) (g-sargs a-sx-list sx-list svs-ok no-calls)))))

(defthm gsb-nocalls
  (implies (not (no-calls :list xs sigs nil)) (gsb-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gsb-sem) (g-svals a-sx-list sx-list no-calls em-ok)))))

(defthm gs-free-any
  (implies (g-st-free x st) (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :cases ((g-mvnth x)) :in-theory (disable gs-sem g-sexpr g-st-free g-mvnth))))

(defthm gs-bad
  (implies (and (or (atom x) (not (true-listp x))) (not (g-mvnth x)))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((g-st-free x st))
           :in-theory (disable gs-sem g-sexpr g-st-free g-mvnth gs-free gs-err g-sexpr-bad)
           :use (gs-free gs-err g-sexpr-bad))))

(defthm gs-if-any
  (implies (and (consp x) (eq (car x) 'if) (true-listp x) (not (g-st-free x st)) (sn-hyps)
                (gs-sem (cadr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gs-sem (caddr x) em (j1 4) (j1 5) sigs fnames st env s defs (1- n) (fr1) heap o)
                (gs-sem (cadddr x) em (j2 4) (j2 5) sigs fnames st env s defs (1- n) (fr1) heap o))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((and (= (len x) 4) (no-calls :term x sigs nil)) (not (= (len x) 4)))
           :in-theory (e/d (gs-ifp) (gs-sem sn-ok g-sexpr g-st-free g-role gsx-if gs-err g-sexpr-if-badlen no-calls))
           :use (gsx-if gs-err g-sexpr-if-badlen))))

(defthm gs-imp-any
  (implies (and (consp x) (eq (car x) 'implies) (true-listp x) (not (g-st-free x st)) (sn-hyps)
                (gs-sem (cadr x) em cnt locs sigs fnames st env s defs (- n 2) fr heap o)
                (gs-sem (caddr x) em (j1 4) (j1 5) sigs fnames st env s defs (- n 3) (fr1) heap o))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((and (= (len x) 3) (no-calls :term x sigs nil)) (not (= (len x) 3)))
           :in-theory (e/d (gs-impp) (gs-sem sn-ok g-sexpr g-st-free g-role gsx-implies gs-err g-sexpr-if-badlen no-calls))
           :use (gsx-implies gs-err g-sexpr-if-badlen))))

(defthm g-sexpr-role-err
  (implies (and (not-leaf) (not (member-eq (car x) '(if implies the-check))) (not (consp (car x)))
                (not (consp (lkp (car x) sigs))) (or (g-role (car x) st) (eq (car x) 'quote)))
           (gsx 0))
  :hints (("Goal" :in-theory (disable g-st-free g-if g-mvnth g-expr g-sargs g-scall-args g-svals g-unop g-binop
                                      g-st-ident g-role g-obj g-comp em-names)
           :expand ((g-sexpr x em cnt locs sigs fnames st)))))

(defthm gs-rest
  (implies (and (not-leaf) (not (member-eq (car x) '(if implies the-check))) (not (consp (car x)))
                (gsa-sem (cdr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((consp (lkp (car x) sigs)) (g-role (car x) st) (eq (car x) 'quote))
           :in-theory (e/d (gs-primp) (gs-sem gsa-sem g-sexpr g-st-free g-mvnth g-role gs-prim gs-err g-sexpr-role-err
                                      no-calls-call-nil gs-nocalls))
           :use (gs-prim gs-err g-sexpr-role-err no-calls-call-nil gs-nocalls))))

(defthm gsa-cons-any
  (implies (and (consp xs) (sn-hyps)
                (gs-sem (car xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gsa-sem (cdr xs) em (sa1 4) (sa1 5) sigs fnames st env s defs (1- n)
                         (mv-nth 1 (sx-list (sa1 1) fr heap)) heap o))
           (gsa-sem xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((no-calls :list xs sigs nil))
           :in-theory (disable gs-sem gsa-sem sn-ok sna-ok g-sexpr g-sargs no-calls gsa-cons)
           :use (gsa-cons))))

(defthm gs-lam-any
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (g-st-free x st)) (sn-hyps) (em-nostobj em st)
                (gsb-sem (cadr (car x)) (cdr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gs-sem (caddr (car x)) (append (gl1 2) em) (gl1 3) (gl1 4) sigs fnames st
                        (pairlis$ (true-list-fix (cadr (car x))) (mv-nth 1 (a-sx-list (cdr x) env s st defs (1- n))))
                        s defs (1- n) (mv-nth 1 (sx-list (gl1 1) fr heap)) heap o))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (gs-lamp) (gs-sem gsb-sem g-sexpr g-svals g-st-free gsx-lambda))
           :use (gsx-lambda))))

; ---- the theorem: g-sexpr is a-sx, for every call-free term

(defthm gs-sem-thm
  (implies (and (sn-hyps) (em-nostobj em st))
           (if (eq flag :args) (gsa-sem x em cnt locs sigs fnames st env s defs n fr heap o)
             (if (eq flag :vals) (gsb-sem vars x em cnt locs sigs fnames st env s defs n fr heap o)
               (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))))
  :rule-classes nil
  :hints (("Goal" :induct (sn-ind flag x vars em cnt locs sigs fnames st env s defs n fr heap) :do-not-induct t
           :in-theory (union-theories
                       '((:induction sn-ind) sx-fr a-sv a-svs em-nostobj-append em-nostobj-g-svals
                         gs-err gs-nocalls gsa-nocalls gsb-nocalls gs-bad gs-mvnth gs-free gs-free-any gs-field gs-size gs-elem
                         gs-if-any gs-imp-any gsx-the-check gs-rest gsa-nil gsa-cons-any gsb-nil gsb-skip gsb-cons
                         gs-lam-any)
                       (theory 'minimal-theory)))
          (and stable-under-simplificationp '(:in-theory (e/d (sx-fr a-sv a-svs) (g-sexpr g-sargs g-svals no-calls a-sx
                                                                a-sx-list sx-list gs-sem gsa-sem gsb-sem g-role g-st-free g-mvnth))))))

(defthm gs-sem-holds
  (implies (and (sn-hyps) (em-nostobj em st)) (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :use (:instance gs-sem-thm (flag :expr)))))
