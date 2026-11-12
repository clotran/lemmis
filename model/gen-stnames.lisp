; gen-stnames: the names g-sexpr uses (sn-ok, sna-ok of gen-stexp, and
; snv-ok for a lambda's value bindings), by an induction over g-sexpr, as
; gen-names' gs-ok-thm is for g-expr: its statements assign only new
; temporaries, and its code reads em's variables, its temporaries and names
; of fnames, the stobjs' objects among them (st-objs st within fnames).
; Call-free source (no-calls ... nil), so g-sexpr's call case does not arise.

(in-package "ACL2")

(include-book "gen-stexp")

(defun sx-fr (ss fr heap) (mv-let (st fr2 h2) (sx-list ss fr heap) (declare (ignore st h2)) fr2))
(defun a-svs (xs env s st defs n) (mv-let (e vs) (a-sx-list xs env s st defs n) (declare (ignore e)) vs))

(set-irrelevant-formals-ok t)

; g-sexpr's recursion (flag :expr, :args, :vals), carrying what gs-sem's
; proof needs too: a-sx's env and fuel, and the frame each part starts from
(defun sn-ind (flag x vars em cnt locs sigs fnames st env s defs n fr heap)
  (declare (xargs :measure (acl2-count x) :verify-guards nil
                  :hints (("Goal" :in-theory (disable g-st-free g-mvnth g-role)))))
  (cond
   ((eq flag :args)
    (if (atom x) nil
      (mv-let (e s1 c ty cnt1 locs1) (g-sexpr (car x) em cnt locs sigs fnames st)
        (declare (ignore e c ty))
        (list (sn-ind :expr (car x) nil em cnt locs sigs fnames st env s defs (1- n) fr heap)
              (sn-ind :args (cdr x) nil em cnt1 locs1 sigs fnames st env s defs (1- n)
                      (sx-fr s1 fr heap) heap)))))
   ((eq flag :vals)
    (cond ((or (atom vars) (atom x)) nil)
          ((or (eq (car vars) (car x)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv))
           (sn-ind :vals (cdr x) (cdr vars) em cnt locs sigs fnames st env s defs (1- n) fr heap))
          (t (mv-let (e s1 c ty cnt1 locs1) (g-sexpr (car x) em cnt locs sigs fnames st)
               (declare (ignore e))
               (mv-let (e tmp cnt2 locs2) (g-fresh (car vars) ty cnt1 locs1 (append fnames (em-names em)))
                 (declare (ignore e))
                 (list (sn-ind :expr (car x) nil em cnt locs sigs fnames st env s defs (1- n) fr heap)
                       (sn-ind :vals (cdr x) (cdr vars) em cnt2 locs2 sigs fnames st env s defs (1- n)
                               (sx-fr (append s1 (list (list :assign (list :var tmp) c))) fr heap)
                               heap)))))))
   ((or (g-mvnth x) (g-st-free x st) (atom x) (not (true-listp x))) nil)
   ((member-eq (g-role (car x) st) '(:field :size)) nil)
   ((eq (g-role (car x) st) :elem) (sn-ind :expr (cadr x) nil em cnt locs sigs fnames st env s defs (1- n) fr heap))
   ((member-eq (car x) '(if implies))
    (let ((imp (eq (car x) 'implies)))
      (mv-let (e sc cc tc cnt1 locs1) (g-sexpr (cadr x) em cnt locs sigs fnames st)
        (declare (ignore e cc tc))
        (mv-let (e sa ca ta cnt2 locs2) (g-sexpr (caddr x) em cnt1 locs1 sigs fnames st)
          (declare (ignore e sa ca ta))
          (let ((fr1 (sx-fr sc fr heap)))
            (list (sn-ind :expr (cadr x) nil em cnt locs sigs fnames st env s defs (if imp (- n 2) (1- n)) fr heap)
                  (sn-ind :expr (caddr x) nil em cnt1 locs1 sigs fnames st env s defs (if imp (- n 3) (1- n)) fr1 heap)
                  (sn-ind :expr (cadddr x) nil em cnt2 locs2 sigs fnames st env s defs (1- n) fr1 heap)))))))
   ((eq (car x) 'the-check)
    (sn-ind :expr (cadddr x) nil em cnt locs sigs fnames st env s defs (- n 4) fr heap))
   ((consp (car x))
    (mv-let (e s1 binds cnt1 locs1) (g-svals (cadr (car x)) (cdr x) em cnt locs sigs fnames st)
      (declare (ignore e))
      (list (sn-ind :vals (cdr x) (cadr (car x)) em cnt locs sigs fnames st env s defs (1- n) fr heap)
            (sn-ind :expr (caddr (car x)) nil (append binds em) cnt1 locs1 sigs fnames st
                    (pairlis$ (true-list-fix (cadr (car x))) (a-svs (cdr x) env s st defs (1- n)))
                    s defs (1- n) (sx-fr s1 fr heap) heap))))
   (t (sn-ind :args (cdr x) nil em cnt locs sigs fnames st env s defs (1- n) fr heap))))

(defun snv-ok (vars xs em cnt locs sigs fnames st)
  (mv-let (e ss binds cnt2 locs2) (g-svals vars xs em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (implies (not e)
             (and (subsetp-equal locs locs2)
                  (subsetp-equal (asg :list ss) (strip-cars locs2))
                  (not (intersectp-equal (asg :list ss) (append fnames (em-names em) (strip-cars locs))))
                  (subsetp-equal (em-names binds) (strip-cars locs2))))))

(defun st-objs (st) (if (atom st) nil (cons (kadr (cdar st)) (st-objs (cdr st)))))

(defthm g-obj-st-objs
  (implies (g-role x st) (member-equal (g-obj x st) (st-objs st))))

(defthm g-obj-fnames
  (implies (and (g-role x st) (subsetp-equal (st-objs st) fnames)) (member-equal (g-obj x st) fnames))
  :hints (("Goal" :in-theory (disable g-role g-obj member-subsetp)
           :use (g-obj-st-objs (:instance member-subsetp (x (g-obj x st)) (b (st-objs st)) (c fnames))))))

(in-theory (disable sn-ok sna-ok snv-ok))

(defmacro sobjs () '(subsetp-equal (st-objs st) fnames))

; ---- the leaves

(defthm sn-mvnth
  (implies (g-mvnth x) (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (enable sn-ok) :expand ((g-sexpr x em cnt locs sigs fnames st)))))

(defthm sn-free
  (implies (and (g-st-free x st) (not (g-mvnth x)) (no-calls :term x sigs nil))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (sn-ok) (g-expr g-st-free g-mvnth sx-list-is-fx-list))
           :expand ((g-sexpr x em cnt locs sigs fnames st))
           :use ((:instance g-expr-cf)))))

(defthm sn-field-size
  (implies (and (consp x) (member-eq (g-role (car x) st) '(:field :size)) (sobjs))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (sn-ok) (g-obj g-comp g-role))
           :expand ((g-sexpr x em cnt locs sigs fnames st) (g-st-free x st)))))

(defmacro not-leaf ()
  '(and (consp x) (true-listp x) (not (g-mvnth x)) (not (g-st-free x st))
        (not (member-eq (g-role (car x) st) '(:field :size :elem)))))

(defthm g-sexpr-elem
  (implies (and (consp x) (eq (g-role (car x) st) :elem) (not (g-mvnth x)) (not (g-st-free x st)))
           (equal (g-sexpr x em cnt locs sigs fnames st)
                  (if (not (and (true-listp x) (= (len x) 3) (eq (g-role (caddr x) st) :stobj)
                                (equal (g-obj (caddr x) st) (g-obj (car x) st))))
                      (mv :stobj nil nil nil cnt locs)
                    (mv-let (e s c ty cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                      (if (or e (not (eq ty :int64))) (mv (or e :type) nil nil nil cnt locs)
                        (mv nil s (list :elem (g-obj (car x) st) (g-comp (car x) st) c) :int64 cnt locs))))))
  :hints (("Goal" :in-theory (disable g-st-free g-if g-mvnth g-expr g-sargs g-scall-args g-svals g-unop g-binop
                                g-st-ident g-role g-obj g-comp em-names)
           :expand ((g-sexpr x em cnt locs sigs fnames st)))
          (and stable-under-simplificationp '(:in-theory (e/d (g-mvnth) (g-st-free g-if g-expr g-sargs g-scall-args g-svals
                                                                g-unop g-binop g-st-ident g-role g-obj g-comp em-names))))))

(defthm g-sexpr-the-check
  (implies (and (not-leaf) (eq (car x) 'the-check))
           (equal (g-sexpr x em cnt locs sigs fnames st)
                  (if (= (len x) 4) (g-sexpr (cadddr x) em cnt locs sigs fnames st) (mv :syntax nil nil nil cnt locs))))
  :hints (("Goal" :in-theory (disable g-st-free g-if g-mvnth g-expr g-sargs g-scall-args g-svals g-unop g-binop
                                g-st-ident g-role g-obj g-comp em-names)
           :expand ((g-sexpr x em cnt locs sigs fnames st)))
          (and stable-under-simplificationp '(:in-theory (e/d (g-mvnth) (g-st-free g-if g-expr g-sargs g-scall-args g-svals
                                                                g-unop g-binop g-st-ident g-role g-obj g-comp em-names))))))

(defthm sn-elem
  (implies (and (consp x) (eq (g-role (car x) st) :elem) (not (g-mvnth x)) (not (g-st-free x st)) (sobjs) (sn-ok (cadr x) em cnt locs sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok x em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-obj g-comp g-role g-st-free g-mvnth sn-ok-use)
           :use ((:instance sn-ok-use (x (cadr x)))))))

(defthm sn-the-check
  (implies (and (not-leaf) (eq (car x) 'the-check) (sn-ok (cadddr x) em cnt locs sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok x em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-st-free g-mvnth g-role sn-ok-use)
           :use ((:instance sn-ok-use (x (cadddr x)))))))

(defthm sn-quote-role
  (implies (and (not-leaf) (not (member-eq (car x) '(if implies the-check))) (not (consp (car x)))
                (not (consp (lkp (car x) sigs))) (or (g-role (car x) st) (eq (car x) 'quote)))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (sn-ok) (g-sexpr g-st-free g-mvnth g-role))
           :expand ((g-sexpr x em cnt locs sigs fnames st)))))

(defthm no-calls-call-nil
  (implies (and (consp x) (not (consp (car x))) (not (eq (car x) 'quote)) (consp (lkp (car x) sigs)))
           (not (no-calls :term x sigs nil)))
  :hints (("Goal" :expand ((no-calls :term x sigs nil)))))

(defthm asg-if-stmts
  (equal (asg :list (if-stmts sc cc sa ca sb cb tmp))
         (append (asg :list sc) (asg :list sa) (list tmp) (asg :list sb) (list tmp)))
  :hints (("Goal" :in-theory (enable if-stmts))))

(defthm g-if-fresh
  (implies (not (car (gif)))
           (and (not (member-equal (g-tmp 't (1+ (nfix cnt))) used))
                (not (member-equal (g-tmp 't (1+ (nfix cnt))) (strip-cars locs)))))
  :hints (("Goal" :in-theory (enable g-if g-fresh g-used))))

(defthm g-sexpr-if-fresh
  (implies (and (gs-ifp x st) (not (gsx 0)))
           (let ((tmp (g-tmp 't (1+ (nfix (j3 4))))))
             (and (not (member-equal tmp fnames)) (not (member-equal tmp (em-names em)))
                  (not (member-equal tmp (strip-cars (j3 5)))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-if g-sexpr gs-ifp g-tmp g-if-fresh g-sexpr-if-out)
           :use (g-sexpr-if
                 (:instance g-if-fresh (sc (j1 1)) (cc (j1 2)) (tc (j1 3)) (sa (j2 1)) (ca (j2 2)) (ta (j2 3))
                            (sb (j3 1)) (cb (j3 2)) (tb (j3 3)) (cnt (j3 4)) (locs (j3 5)) (used (append fnames (em-names em))))))))

; the if's names from its parts', abstractly
(defmacro snf (s c la lb)
  `(and (subsetp-equal ,la ,lb) (subsetp-equal (asg :list ,s) (strip-cars ,lb))
        (not (intersectp-equal (asg :list ,s) f)) (not (intersectp-equal (asg :list ,s) e))
        (not (intersectp-equal (asg :list ,s) (strip-cars ,la)))
        (subsetp-equal (sv-names ,c) (append f e (strip-cars ,lb)))))

(defthm sn-if-abs
  (implies (and (snf sc cc l0 l1) (snf sa ca l1 l2) (snf sb cb l2 l3)
                (not (member-equal tmp f)) (not (member-equal tmp e)) (not (member-equal tmp (strip-cars l3))))
           (let ((l4 (cons (cons tmp ty) (true-list-fix l3))))
             (and (subsetp-equal l0 l4)
                  (subsetp-equal (asg :list (if-stmts sc cc sa ca sb cb tmp)) (strip-cars l4))
                  (not (intersectp-equal (asg :list (if-stmts sc cc sa ca sb cb tmp)) (append f e (strip-cars l0))))
                  (subsetp-equal (sv-names (list :var tmp)) (append f e (strip-cars l4))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable if-stmts)
           :use ((:instance subsetp-trans (a l0) (b l1) (c l2))
                 (:instance subsetp-trans (a l0) (b l2) (c l3))
                 (:instance subsetp-trans (a l1) (b l2) (c l3))))))

(defthm sn-if
  (implies (and (gs-ifp x st)
                (sn-ok (cadr x) em cnt locs sigs fnames st)
                (sn-ok (caddr x) em (j1 4) (j1 5) sigs fnames st)
                (sn-ok (cadddr x) em (j2 4) (j2 5) sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok x em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-sexpr-if gs-ifp g-tmp if-stmts asg-if-stmts sv-names nfix)
           :use ((:instance sn-if-abs (sc (j1 1)) (cc (j1 2)) (sa (j2 1)) (ca (j2 2)) (sb (j3 1)) (cb (j3 2))
                            (l0 locs) (l1 (j1 5)) (l2 (j2 5)) (l3 (j3 5)) (f fnames) (e (em-names em))
                            (tmp (g-tmp 't (1+ (nfix (j3 4))))) (ty (j2 3)))))))

; ---- implies: g-sexpr's if with else (:true)

(defun gs-impp (x st)
  (and (consp x) (eq (car x) 'implies) (true-listp x) (= (len x) 3) (not (g-st-free x st)) (not (g-role 'implies st))))

(defthm g-sexpr-imp
  (implies (gs-impp x st)
           (equal (g-sexpr x em cnt locs sigs fnames st)
                  (if (j1 0) (mv (j1 0) nil nil nil (j1 4) (j1 5))
                    (if (j2 0) (mv (j2 0) nil nil nil (j2 4) (j2 5))
                      (g-if (j1 1) (j1 2) (j1 3) (j2 1) (j2 2) (j2 3) nil '(:true) :logical (j2 4) (j2 5)
                            (append fnames (em-names em)))))))
  :hints (("Goal" :in-theory (disable g-st-free g-if g-mvnth g-expr g-sargs g-scall-args g-svals g-unop g-binop
                                      g-st-ident g-role g-obj g-comp em-names)
           :expand ((g-sexpr x em cnt locs sigs fnames st)))
          (and stable-under-simplificationp '(:in-theory (e/d (g-mvnth) (g-st-free g-if g-expr g-sargs g-scall-args g-svals
                                                                      g-unop g-binop g-st-ident g-role g-obj g-comp em-names))))))

(defthm g-sexpr-imp-out
  (implies (and (gs-impp x st) (not (gsx 0)))
           (let ((tmp (g-tmp 't (1+ (nfix (j2 4))))))
             (and (not (j1 0)) (not (j2 0)) (equal (j1 3) :logical) (equal (j2 3) :logical)
                  (equal (gsx 1) (if-stmts (j1 1) (j1 2) (j2 1) (j2 2) nil '(:true) tmp))
                  (equal (gsx 2) (list :var tmp))
                  (equal (gsx 3) :logical)
                  (equal (gsx 5) (cons (cons tmp :logical) (true-list-fix (j2 5))))
                  (not (member-equal tmp fnames)) (not (member-equal tmp (em-names em)))
                  (not (member-equal tmp (strip-cars (j2 5)))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-if g-sexpr gs-impp if-stmts g-tmp g-if-out g-if-types g-if-fresh)
           :use (g-sexpr-imp
                 (:instance g-if-out (sc (j1 1)) (cc (j1 2)) (tc (j1 3)) (sa (j2 1)) (ca (j2 2)) (ta (j2 3))
                            (sb nil) (cb '(:true)) (tb :logical) (cnt (j2 4)) (locs (j2 5)) (used (append fnames (em-names em))))
                 (:instance g-if-types (sc (j1 1)) (cc (j1 2)) (tc (j1 3)) (sa (j2 1)) (ca (j2 2)) (ta (j2 3))
                            (sb nil) (cb '(:true)) (tb :logical) (cnt (j2 4)) (locs (j2 5)) (used (append fnames (em-names em))))
                 (:instance g-if-fresh (sc (j1 1)) (cc (j1 2)) (tc (j1 3)) (sa (j2 1)) (ca (j2 2)) (ta (j2 3))
                            (sb nil) (cb '(:true)) (tb :logical) (cnt (j2 4)) (locs (j2 5)) (used (append fnames (em-names em))))))))

(defthm sn-imp
  (implies (and (gs-impp x st)
                (sn-ok (cadr x) em cnt locs sigs fnames st)
                (sn-ok (caddr x) em (j1 4) (j1 5) sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok x em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-sexpr-imp gs-impp g-tmp if-stmts asg-if-stmts sv-names nfix)
           :use ((:instance sn-if-abs (sc (j1 1)) (cc (j1 2)) (sa (j2 1)) (ca (j2 2)) (sb nil) (cb '(:true))
                            (l0 locs) (l1 (j1 5)) (l2 (j2 5)) (l3 (j2 5)) (f fnames) (e (em-names em))
                            (tmp (g-tmp 't (1+ (nfix (j2 4))))) (ty :logical))))))

; ---- a primitive on its arguments

(defthm sv-names-g-unop
  (implies (subsetp-equal (sv-names c) tgt) (subsetp-equal (sv-names (mv-nth 1 (g-unop op c ty))) tgt)))

(defthm sv-names-g-binop
  (implies (and (subsetp-equal (sv-names a) tgt) (subsetp-equal (sv-names b) tgt))
           (subsetp-equal (sv-names (mv-nth 1 (g-binop op a ta b tb))) tgt)))

(defthm svs-names-parts
  (implies (subsetp-equal (svs-names cs) tgt)
           (and (subsetp-equal (sv-names (car cs)) tgt) (subsetp-equal (sv-names (cadr cs)) tgt)))
  :hints (("Goal" :expand ((svs-names cs) (svs-names (cdr cs))))))

(defthm sn-prim
  (implies (and (gs-primp x sigs st) (sna-ok (cdr x) em cnt locs sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (sn-ok sna-ok) (g-sargs g-unop g-binop gs-primp sv-names svs-names)))))

(defthm sna-nil
  (implies (atom xs) (sna-ok xs em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (enable sna-ok) :expand ((g-sargs xs em cnt locs sigs fnames st)))))

(defmacro snl (s rd la lb)
  `(and (subsetp-equal ,la ,lb) (subsetp-equal (asg :list ,s) (strip-cars ,lb))
        (not (intersectp-equal (asg :list ,s) f)) (not (intersectp-equal (asg :list ,s) e))
        (not (intersectp-equal (asg :list ,s) (strip-cars ,la)))
        (subsetp-equal ,rd (append f e (strip-cars ,lb)))))

(defthm sna-abs
  (implies (and (snl s1 (sv-names c) l0 l1) (snl s2 (svs-names cs) l1 l2))
           (and (subsetp-equal l0 l2)
                (subsetp-equal (asg :list (append s1 s2)) (strip-cars l2))
                (not (intersectp-equal (asg :list (append s1 s2)) (append f e (strip-cars l0))))
                (subsetp-equal (svs-names (cons c cs)) (append f e (strip-cars l2)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance subsetp-trans (a l0) (b l1) (c l2))
                 (:instance subsetp-strip-cars (a l1) (b l2))
                 (:instance subsetp-trans (a (sv-names c)) (b (append f e (strip-cars l1)))
                            (c (append f e (strip-cars l2))))))))

(defthm sna-cons
  (implies (and (consp xs) (sn-ok (car xs) em cnt locs sigs fnames st)
                (sna-ok (cdr xs) em (sa1 4) (sa1 5) sigs fnames st))
           (sna-ok xs em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sna-ok xs em cnt locs sigs fnames st) (g-sargs xs em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-sargs svs-names)
           :use ((:instance sna-abs (s1 (sa1 1)) (c (sa1 2)) (s2 (sa2 1)) (cs (sa2 2))
                            (l0 locs) (l1 (sa1 5)) (l2 (sa2 5)) (f fnames) (e (em-names em)))))))

; ---- a lambda's value bindings

(defthm g-fresh-out
  (implies (not (car (g-fresh b ty cnt locs used)))
           (let ((tmp (g-tmp b (1+ (nfix cnt)))))
             (and (equal (mv-nth 1 (g-fresh b ty cnt locs used)) tmp)
                  (equal (mv-nth 3 (g-fresh b ty cnt locs used)) (cons (cons tmp ty) (true-list-fix locs)))
                  (not (member-equal tmp used)) (not (member-equal tmp (strip-cars locs))))))
  :hints (("Goal" :in-theory (e/d (g-fresh g-used) (g-tmp)))))

(defthm snv-nil
  (implies (or (atom vars) (atom xs)) (snv-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (enable snv-ok) :expand ((g-svals vars xs em cnt locs sigs fnames st)))))

(defthm snv-skip
  (implies (and (consp vars) (consp xs)
                (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv))
                (snv-ok (cdr vars) (cdr xs) em cnt locs sigs fnames st))
           (snv-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (snv-ok) (g-sexpr g-svals g-role)) :expand ((g-svals vars xs em cnt locs sigs fnames st)))))

(defthm snv-abs
  (let ((l1t (cons (cons tmp ty) (true-list-fix l1))))
    (implies (and (snl s1 (sv-names c) l0 l1)
                  (not (member-equal tmp f)) (not (member-equal tmp e)) (not (member-equal tmp (strip-cars l1)))
                  (subsetp-equal l1t l2) (subsetp-equal (asg :list ss) (strip-cars l2))
                  (not (intersectp-equal (asg :list ss) f)) (not (intersectp-equal (asg :list ss) e))
                  (not (intersectp-equal (asg :list ss) (strip-cars l1t)))
                  (subsetp-equal (em-names bs) (strip-cars l2)))
             (and (subsetp-equal l0 l2)
                  (subsetp-equal (asg :list (append s1 (cons (list :assign (list :var tmp) c) ss))) (strip-cars l2))
                  (not (intersectp-equal (asg :list (append s1 (cons (list :assign (list :var tmp) c) ss)))
                                         (append f e (strip-cars l0))))
                  (subsetp-equal (em-names (cons (list* v tmp ty) bs)) (strip-cars l2)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance subsetp-trans (a l0) (b l1) (c l1t))
                 (:instance subsetp-trans (a l0) (b (cons (cons tmp ty) (true-list-fix l1))) (c l2))
                 (:instance subsetp-trans (a l1) (b (cons (cons tmp ty) (true-list-fix l1))) (c l2))
                 (:instance subsetp-strip-cars (a l1) (b l2))
                 (:instance subsetp-strip-cars (a (cons (cons tmp ty) (true-list-fix l1))) (b l2))
                 (:instance subsetp-strip-cars (a l0) (b l1))))))

(defmacro sv1 (k) `(mv-nth ,k (g-sexpr (car xs) em cnt locs sigs fnames st)))
(defmacro gfv (k) `(mv-nth ,k (g-fresh (car vars) (sv1 3) (sv1 4) (sv1 5) (append fnames (em-names em)))))
(defmacro svr (k) `(mv-nth ,k (g-svals (cdr vars) (cdr xs) em (gfv 2) (gfv 3) sigs fnames st)))

(defthm snv-cons
  (implies (and (consp vars) (consp xs)
                (not (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv)))
                (sn-ok (car xs) em cnt locs sigs fnames st)
                (snv-ok (cdr vars) (cdr xs) em (gfv 2) (gfv 3) sigs fnames st))
           (snv-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((snv-ok vars xs em cnt locs sigs fnames st)
                                            (g-svals vars xs em cnt locs sigs fnames st))
           :in-theory (e/d (snv-ok) (g-sexpr g-svals g-role g-fresh g-tmp em-names nfix))
           :use ((:instance snv-abs (s1 (sv1 1)) (c (sv1 2)) (tmp (gfv 1)) (ty (sv1 3)) (ss (svr 1)) (bs (svr 2))
                            (v (car vars)) (l0 locs) (l1 (sv1 5)) (l2 (svr 4)) (f fnames) (e (em-names em)))
                 (:instance g-fresh-out (b (car vars)) (ty (sv1 3)) (cnt (sv1 4)) (locs (sv1 5))
                            (used (append fnames (em-names em))))))))

; ---- a lambda: the value bindings, then the body in the new scope

(defun gs-lamp (x st) (and (consp x) (consp (car x)) (true-listp x) (not (g-st-free x st))))

(defthm g-sexpr-lambda
  (implies (gs-lamp x st)
           (equal (g-sexpr x em cnt locs sigs fnames st)
                  (let ((vars (cadr (car x))) (body (caddr (car x))))
                    (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                                  (no-duplicatesp-eq vars) (= (len vars) (len (cdr x))) (not (member-eq 'mv vars))
                                  (g-st-ident vars (cdr x) st)))
                        (mv :stobj nil nil nil cnt locs)
                      (mv-let (e s binds cnt locs) (g-svals vars (cdr x) em cnt locs sigs fnames st)
                        (if e (mv e nil nil nil cnt locs)
                          (mv-let (e sb cb tb cnt locs) (g-sexpr body (append binds em) cnt locs sigs fnames st)
                            (if e (mv e nil nil nil cnt locs)
                              (mv nil (append s sb) cb tb cnt locs)))))))))
  :hints (("Goal" :in-theory (disable g-st-free g-if g-mvnth g-expr g-sargs g-scall-args g-svals g-unop g-binop
                                      g-st-ident g-role g-obj g-comp em-names)
           :expand ((g-sexpr x em cnt locs sigs fnames st)))
          (and stable-under-simplificationp '(:in-theory (e/d (g-mvnth) (g-st-free g-if g-expr g-sargs g-scall-args g-svals
                                                                      g-unop g-binop g-st-ident g-role g-obj g-comp em-names))))))

(defthm subsetp-app-drop-mid
  (implies (and (subsetp-equal a (append f b e c)) (subsetp-equal b c)) (subsetp-equal a (append f e c)))
  :hints (("Goal" :induct (len a))))

(defthm sn-lam-abs
  (implies (and (subsetp-equal l0 l1) (subsetp-equal (asg :list s) (strip-cars l1))
                (not (intersectp-equal (asg :list s) f)) (not (intersectp-equal (asg :list s) e))
                (not (intersectp-equal (asg :list s) (strip-cars l0)))
                (subsetp-equal eb (strip-cars l1))
                (subsetp-equal l1 l2) (subsetp-equal (asg :list sb) (strip-cars l2))
                (not (intersectp-equal (asg :list sb) f)) (not (intersectp-equal (asg :list sb) (append eb e)))
                (not (intersectp-equal (asg :list sb) (strip-cars l1)))
                (subsetp-equal (sv-names cb) (append f (append eb e) (strip-cars l2))))
           (and (subsetp-equal l0 l2)
                (subsetp-equal (asg :list (append s sb)) (strip-cars l2))
                (not (intersectp-equal (asg :list (append s sb)) (append f e (strip-cars l0))))
                (subsetp-equal (sv-names cb) (append f e (strip-cars l2)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable subsetp-app-drop-mid)
           :use ((:instance subsetp-trans (a l0) (b l1) (c l2))
                 (:instance subsetp-strip-cars (a l1) (b l2))
                 (:instance subsetp-strip-cars (a l0) (b l1))
                 (:instance subsetp-trans (a eb) (b (strip-cars l1)) (c (strip-cars l2)))
                 (:instance subsetp-app-drop-mid (a (sv-names cb)) (b eb) (c (strip-cars l2)))))))

(defmacro gl1 (k) `(mv-nth ,k (g-svals (cadr (car x)) (cdr x) em cnt locs sigs fnames st)))
(defmacro gl2 (k) `(mv-nth ,k (g-sexpr (caddr (car x)) (append (gl1 2) em) (gl1 3) (gl1 4) sigs fnames st)))

(defthm sn-lambda
  (implies (and (gs-lamp x st)
                (snv-ok (cadr (car x)) (cdr x) em cnt locs sigs fnames st)
                (sn-ok (caddr (car x)) (append (gl1 2) em) (gl1 3) (gl1 4) sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok x em cnt locs sigs fnames st))
           :in-theory (e/d (snv-ok) (g-sexpr g-svals gs-lamp sv-names g-st-ident sn-ok-use))
           :use ((:instance sn-lam-abs (s (gl1 1)) (sb (gl2 1)) (cb (gl2 2)) (eb (em-names (gl1 2)))
                            (l0 locs) (l1 (gl1 4)) (l2 (gl2 5)) (f fnames) (e (em-names em)))
                 (:instance sn-ok-use (x (caddr (car x))) (em (append (gl1 2) em)) (cnt (gl1 3)) (locs (gl1 4)))))))

; ---- the induction: it only dispatches to the cases

(defthm no-calls-list-parts
  (implies (no-calls :list xs sigs cs)
           (and (no-calls :term (car xs) sigs cs) (no-calls :list (cdr xs) sigs cs)))
  :hints (("Goal" :expand ((no-calls :list xs sigs cs) (no-calls :term nil sigs cs)))))

(defthm no-calls-sym-args
  (implies (and (consp x) (not (eq (car x) 'quote)) (not (consp (car x))) (no-calls :term x sigs cs))
           (no-calls :list (cdr x) sigs cs))
  :hints (("Goal" :expand ((no-calls :term x sigs cs)))))

(defthm no-calls-lambda-parts
  (implies (and (consp x) (consp (car x)) (no-calls :term x sigs cs))
           (and (no-calls :term (caddr (car x)) sigs cs) (no-calls :list (cdr x) sigs cs)))
  :hints (("Goal" :expand ((no-calls :term x sigs cs)))))

(defthm sn-err
  (implies (gsx 0) (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (sn-ok) (g-sexpr)))))

(defthm g-sexpr-bad
  (implies (and (or (atom x) (not (true-listp x))) (not (g-mvnth x)) (not (g-st-free x st)))
           (gsx 0))
  :hints (("Goal" :in-theory (disable g-st-free g-mvnth g-expr) :expand ((g-sexpr x em cnt locs sigs fnames st)))))

(defthm g-sexpr-if-badlen
  (implies (and (consp x) (member-eq (car x) '(if implies)) (true-listp x)
                (not (= (len x) (if (eq (car x) 'if) 4 3))) (not (g-st-free x st)) (not (g-role (car x) st)))
           (gsx 0))
  :hints (("Goal" :in-theory (disable g-st-free g-if g-mvnth g-expr g-sargs g-scall-args g-svals g-unop g-binop
                                      g-st-ident g-role g-obj g-comp em-names)
           :expand ((g-sexpr x em cnt locs sigs fnames st)))
          (and stable-under-simplificationp '(:in-theory (e/d (g-mvnth) (g-st-free g-if g-expr g-sargs g-scall-args g-svals
                                                                      g-unop g-binop g-st-ident g-role g-obj g-comp em-names))))))

(defthm g-st-free-quote
  (implies (and (consp x) (eq (car x) 'quote)) (g-st-free x st))
  :hints (("Goal" :expand ((g-st-free x st)))))

(defthm not-free-not-quote
  (implies (and (not (g-st-free x st)) (consp x)) (not (equal (car x) 'quote)))
  :rule-classes :forward-chaining)

(defthm sn-rest
  (implies (and (not-leaf) (not (member-eq (car x) '(if implies the-check))) (not (consp (car x)))
                (not (consp (lkp (car x) sigs))) (sna-ok (cdr x) em cnt locs sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :cases ((g-role (car x) st))
           :in-theory (e/d (gs-primp) (sn-ok sna-ok g-sexpr g-st-free g-mvnth g-role sn-quote-role sn-prim))
           :use (sn-quote-role sn-prim))))

(defthm sn-if-any
  (implies (and (consp x) (eq (car x) 'if) (true-listp x) (not (g-st-free x st)) (not (g-role 'if st))
                (sn-ok (cadr x) em cnt locs sigs fnames st)
                (sn-ok (caddr x) em (j1 4) (j1 5) sigs fnames st)
                (sn-ok (cadddr x) em (j2 4) (j2 5) sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :cases ((= (len x) 4))
           :in-theory (e/d (gs-ifp) (sn-ok g-sexpr g-st-free g-role sn-if sn-err g-sexpr-if-badlen))
           :use (sn-if sn-err g-sexpr-if-badlen))))

(defthm sn-imp-any
  (implies (and (consp x) (eq (car x) 'implies) (true-listp x) (not (g-st-free x st)) (not (g-role 'implies st))
                (sn-ok (cadr x) em cnt locs sigs fnames st)
                (sn-ok (caddr x) em (j1 4) (j1 5) sigs fnames st))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :cases ((= (len x) 3))
           :in-theory (e/d (gs-impp) (sn-ok g-sexpr g-st-free g-role sn-imp sn-err g-sexpr-if-badlen))
           :use (sn-imp sn-err g-sexpr-if-badlen))))

(defthm sn-free-any
  (implies (and (g-st-free x st) (no-calls :term x sigs nil)) (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :cases ((g-mvnth x)) :in-theory (disable sn-ok g-sexpr g-st-free g-mvnth no-calls))))

(defthm g-mvnth-atom (implies (or (atom x) (not (true-listp x))) (not (g-mvnth x))))

(defthm sn-bad
  (implies (and (or (atom x) (not (true-listp x))) (not (g-mvnth x)) (no-calls :term x sigs nil))
           (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :cases ((g-st-free x st))
           :in-theory (disable sn-ok g-sexpr g-st-free g-mvnth sn-free sn-err g-sexpr-bad no-calls)
           :use (sn-free sn-err g-sexpr-bad))))

(defthm sn-ok-thm
  (implies (and (sobjs) (not (g-role 'if st)) (not (g-role 'implies st)))
           (if (eq flag :args) (implies (no-calls :list x sigs nil) (sna-ok x em cnt locs sigs fnames st))
             (if (eq flag :vals) (implies (no-calls :list x sigs nil) (snv-ok vars x em cnt locs sigs fnames st))
               (implies (no-calls :term x sigs nil) (sn-ok x em cnt locs sigs fnames st)))))
  :rule-classes nil
  :hints (("Goal" :induct (sn-ind flag x vars em cnt locs sigs fnames st env s defs n fr heap) :do-not-induct t
           :in-theory (disable sn-ok sna-ok snv-ok g-sexpr g-sargs g-svals no-calls g-st-free g-mvnth g-role
                               gs-ifp gs-impp gs-lamp gs-primp sn-ok-use sna-ok-use g-fresh sx-fr a-svs))
          (and stable-under-simplificationp '(:in-theory (e/d (gs-ifp gs-impp gs-lamp gs-primp)
                                                              (sn-ok sna-ok snv-ok g-sexpr g-sargs g-svals no-calls g-st-free
                                                               g-mvnth g-role sn-ok-use sna-ok-use g-fresh sx-fr a-svs))))))

(defmacro sn-hyps () '(and (sobjs) (not (g-role 'if st)) (not (g-role 'implies st))))

(defthm sn-ok-holds
  (implies (and (sn-hyps) (no-calls :term x sigs nil)) (sn-ok x em cnt locs sigs fnames st))
  :hints (("Goal" :use (:instance sn-ok-thm (flag :expr)))))

(defthm sna-ok-holds
  (implies (and (sn-hyps) (no-calls :list xs sigs nil)) (sna-ok xs em cnt locs sigs fnames st))
  :hints (("Goal" :use (:instance sn-ok-thm (flag :args) (x xs)))))

(defthm snv-ok-holds
  (implies (and (sn-hyps) (no-calls :list xs sigs nil)) (snv-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :use (:instance sn-ok-thm (flag :vals) (x xs)))))
