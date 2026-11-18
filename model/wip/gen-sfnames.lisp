; gen-sfnames: gen-stnames on svf/sxf-list/a-sxf (clone.py).

(in-package "ACL2")

(include-book "gen-stnames")
(include-book "gen-sfcall")

(defun sx-fr-f (ss fr heap) (mv-let (st fr2 h2) (sxf-list ss fr heap) (declare (ignore st h2)) fr2))

(defun a-sv-f (x env s st defs n) (mv-let (e v) (a-sxf x env s st defs n) (declare (ignore e)) v))

(defun a-svs-f (xs env s st defs n) (mv-let (e vs) (a-sxf-list xs env s st defs n) (declare (ignore e)) vs))

(defun sn-ind-f (flag x vars em cnt locs sigs fnames st env s defs n fr heap)
  (declare (xargs :measure (acl2-count x) :verify-guards nil
                  :hints (("Goal" :in-theory (disable g-st-free g-mvnth g-role)))))
  (cond
   ((eq flag :args)
    (if (atom x) nil
      (mv-let (e s1 c ty cnt1 locs1) (g-sexpr (car x) em cnt locs sigs fnames st)
        (declare (ignore e c ty))
        (list (sn-ind-f :expr (car x) nil em cnt locs sigs fnames st env s defs (1- n) fr heap)
              (sn-ind-f :args (cdr x) nil em cnt1 locs1 sigs fnames st env s defs (1- n)
                      (sx-fr-f s1 fr heap) heap)))))
   ((eq flag :vals)
    (cond ((or (atom vars) (atom x)) nil)
          ((or (eq (car vars) (car x)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv))
           (sn-ind-f :vals (cdr x) (cdr vars) em cnt locs sigs fnames st env s defs (1- n) fr heap))
          (t (mv-let (e s1 c ty cnt1 locs1) (g-sexpr (car x) em cnt locs sigs fnames st)
               (declare (ignore e c))
               (mv-let (e tmp cnt2 locs2) (g-fresh (car vars) ty cnt1 locs1 (append fnames (em-names em)))
                 (declare (ignore e))
                 (list (sn-ind-f :expr (car x) nil em cnt locs sigs fnames st env s defs (1- n) fr heap)
                       (sn-ind-f :vals (cdr x) (cdr vars) em cnt2 locs2 sigs fnames st env s defs (1- n)
                               (put tmp (cons ty (a-sv-f (car x) env s st defs (1- n))) (sx-fr-f s1 fr heap))
                               heap)))))))
   ((or (g-mvnth x) (g-st-free x st) (atom x) (not (true-listp x))) nil)
   ((member-eq (g-role (car x) st) '(:field :size)) nil)
   ((eq (g-role (car x) st) :elem) (sn-ind-f :expr (cadr x) nil em cnt locs sigs fnames st env s defs (1- n) fr heap))
   ((member-eq (car x) '(if implies))
    (let ((imp (eq (car x) 'implies)))
      (mv-let (e sc cc tc cnt1 locs1) (g-sexpr (cadr x) em cnt locs sigs fnames st)
        (declare (ignore e cc tc))
        (mv-let (e sa ca ta cnt2 locs2) (g-sexpr (caddr x) em cnt1 locs1 sigs fnames st)
          (declare (ignore e sa ca ta))
          (let ((fr1-f (sx-fr-f sc fr heap)))
            (list (sn-ind-f :expr (cadr x) nil em cnt locs sigs fnames st env s defs (if imp (- n 2) (1- n)) fr heap)
                  (sn-ind-f :expr (caddr x) nil em cnt1 locs1 sigs fnames st env s defs (if imp (- n 3) (1- n)) fr1-f heap)
                  (sn-ind-f :expr (cadddr x) nil em cnt2 locs2 sigs fnames st env s defs (1- n) fr1-f heap)))))))
   ((eq (car x) 'the-check)
    (sn-ind-f :expr (cadddr x) nil em cnt locs sigs fnames st env s defs (- n 4) fr heap))
   ((consp (car x))
    (mv-let (e s1 binds cnt1 locs1) (g-svals (cadr (car x)) (cdr x) em cnt locs sigs fnames st)
      (declare (ignore e))
      (list (sn-ind-f :vals (cdr x) (cadr (car x)) em cnt locs sigs fnames st env s defs (1- n) fr heap)
            (sn-ind-f :expr (caddr (car x)) nil (append binds em) cnt1 locs1 sigs fnames st
                    (pairlis$ (true-list-fix (cadr (car x))) (a-svs-f (cdr x) env s st defs (1- n)))
                    s defs (1- n) (sx-fr-f s1 fr heap) heap))))
   (t (list (sn-ind-f :args (cdr x) nil em cnt locs sigs fnames st env s defs (1- n) fr heap)
            (sn-ind-f :args (g-cvals (kar (cdr (lkp (car x) sigs))) (cdr x) st) nil em cnt locs sigs fnames st env s defs (1- n)
                      fr heap)))))

(in-theory (disable sn-ok-f sna-ok-f snv-ok))

(defthm sn-mvnth-f
  (implies (g-mvnth x) (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (enable sn-ok-f) :expand ((g-sexpr x em cnt locs sigs fnames st)))))

(defthm sn-free-f
  (implies (and (g-st-free x st) (not (g-mvnth x)) (sfc-ok :term x sigs st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (sn-ok-f) (g-expr g-st-free g-mvnth sx-list-is-fx-list-f))
           :expand ((g-sexpr x em cnt locs sigs fnames st))
           :use ((:instance g-expr-cf)))))

(defthm sn-field-size-f
  (implies (and (consp x) (member-eq (g-role (car x) st) '(:field :size)) (sobjs))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (sn-ok-f) (g-obj g-comp g-role))
           :expand ((g-sexpr x em cnt locs sigs fnames st) (g-st-free x st)))))

(defthm sn-elem-f
  (implies (and (consp x) (eq (g-role (car x) st) :elem) (not (g-mvnth x)) (not (g-st-free x st)) (sobjs) (sn-ok-f (cadr x) em cnt locs sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok-f x em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-obj g-comp g-role g-st-free g-mvnth sn-ok-use-f)
           :use ((:instance sn-ok-use-f (x (cadr x)))))))

(defthm sn-the-check-f
  (implies (and (not-leaf) (eq (car x) 'the-check) (sn-ok-f (cadddr x) em cnt locs sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok-f x em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-st-free g-mvnth g-role sn-ok-use-f)
           :use ((:instance sn-ok-use-f (x (cadddr x)))))))

(defthm sn-quote-role-f
  (implies (and (not-leaf) (not (member-eq (car x) '(if implies the-check))) (not (consp (car x)))
                (not (consp (lkp (car x) sigs))) (or (g-role (car x) st) (eq (car x) 'quote)))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (sn-ok-f) (g-sexpr g-st-free g-mvnth g-role))
           :expand ((g-sexpr x em cnt locs sigs fnames st)))))

(defmacro snf-f (s c la lb)
  `(and (subsetp-equal ,la ,lb) (subsetp-equal (asg :list ,s) (strip-cars ,lb))
        (not (intersectp-equal (asg :list ,s) f)) (not (intersectp-equal (asg :list ,s) e))
        (not (intersectp-equal (asg :list ,s) (strip-cars ,la)))
        (subsetp-equal (svf-names ,c) (append f e (strip-cars ,lb)))))

(defthm sn-if-abs-f
  (implies (and (snf-f sc cc l0 l1) (snf-f sa ca l1 l2) (snf-f sb cb l2 l3)
                (not (member-equal tmp f)) (not (member-equal tmp e)) (not (member-equal tmp (strip-cars l3))))
           (let ((l4 (cons (cons tmp ty) (true-list-fix l3))))
             (and (subsetp-equal l0 l4)
                  (subsetp-equal (asg :list (if-stmts sc cc sa ca sb cb tmp)) (strip-cars l4))
                  (not (intersectp-equal (asg :list (if-stmts sc cc sa ca sb cb tmp)) (append f e (strip-cars l0))))
                  (subsetp-equal (svf-names (list :var tmp)) (append f e (strip-cars l4))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable if-stmts)
           :use ((:instance subsetp-trans (a l0) (b l1) (c l2))
                 (:instance subsetp-trans (a l0) (b l2) (c l3))
                 (:instance subsetp-trans (a l1) (b l2) (c l3))))))

(defthm sn-if-f
  (implies (and (gs-ifp x st)
                (sn-ok-f (cadr x) em cnt locs sigs fnames st)
                (sn-ok-f (caddr x) em (j1 4) (j1 5) sigs fnames st)
                (sn-ok-f (cadddr x) em (j2 4) (j2 5) sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok-f x em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-sexpr-if gs-ifp g-tmp if-stmts asg-if-stmts svf-names nfix)
           :use ((:instance sn-if-abs-f (sc (j1 1)) (cc (j1 2)) (sa (j2 1)) (ca (j2 2)) (sb (j3 1)) (cb (j3 2))
                            (l0 locs) (l1 (j1 5)) (l2 (j2 5)) (l3 (j3 5)) (f fnames) (e (em-names em))
                            (tmp (g-tmp 't (1+ (nfix (j3 4))))) (ty (j2 3)))))))

(defthm sn-imp-f
  (implies (and (gs-impp x st)
                (sn-ok-f (cadr x) em cnt locs sigs fnames st)
                (sn-ok-f (caddr x) em (j1 4) (j1 5) sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok-f x em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-sexpr-imp gs-impp g-tmp if-stmts asg-if-stmts svf-names nfix)
           :use ((:instance sn-if-abs-f (sc (j1 1)) (cc (j1 2)) (sa (j2 1)) (ca (j2 2)) (sb nil) (cb '(:true))
                            (l0 locs) (l1 (j1 5)) (l2 (j2 5)) (l3 (j2 5)) (f fnames) (e (em-names em))
                            (tmp (g-tmp 't (1+ (nfix (j2 4))))) (ty :logical))))))

(defthm sv-names-g-unop-f
  (implies (subsetp-equal (svf-names c) tgt) (subsetp-equal (svf-names (mv-nth 1 (g-unop op c ty))) tgt)))

(defthm sv-names-g-binop-f
  (implies (and (subsetp-equal (svf-names a) tgt) (subsetp-equal (svf-names b) tgt))
           (subsetp-equal (svf-names (mv-nth 1 (g-binop op a ta b tb))) tgt)))

(defthm svs-names-parts-f
  (implies (subsetp-equal (svs-names-f cs) tgt)
           (and (subsetp-equal (svf-names (car cs)) tgt) (subsetp-equal (svf-names (cadr cs)) tgt)))
  :hints (("Goal" :expand ((svs-names-f cs) (svs-names-f (cdr cs))))))

(defthm sn-prim-f
  (implies (and (gs-primp x sigs st) (sna-ok-f (cdr x) em cnt locs sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (sn-ok-f sna-ok-f) (g-sargs g-unop g-binop gs-primp svf-names svs-names-f)))))

(defthm sna-nil-f
  (implies (atom xs) (sna-ok-f xs em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (enable sna-ok-f) :expand ((g-sargs xs em cnt locs sigs fnames st)))))

(defthm sna-abs-f
  (implies (and (snl s1 (svf-names c) l0 l1) (snl s2 (svs-names-f cs) l1 l2))
           (and (subsetp-equal l0 l2)
                (subsetp-equal (asg :list (append s1 s2)) (strip-cars l2))
                (not (intersectp-equal (asg :list (append s1 s2)) (append f e (strip-cars l0))))
                (subsetp-equal (svs-names-f (cons c cs)) (append f e (strip-cars l2)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance subsetp-trans (a l0) (b l1) (c l2))
                 (:instance subsetp-strip-cars (a l1) (b l2))
                 (:instance subsetp-trans (a (svf-names c)) (b (append f e (strip-cars l1)))
                            (c (append f e (strip-cars l2))))))))

(defthm sna-cons-f
  (implies (and (consp xs) (sn-ok-f (car xs) em cnt locs sigs fnames st)
                (sna-ok-f (cdr xs) em (sa1 4) (sa1 5) sigs fnames st))
           (sna-ok-f xs em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sna-ok-f xs em cnt locs sigs fnames st) (g-sargs xs em cnt locs sigs fnames st))
           :in-theory (disable g-sexpr g-sargs svs-names-f)
           :use ((:instance sna-abs-f (s1 (sa1 1)) (c (sa1 2)) (s2 (sa2 1)) (cs (sa2 2))
                            (l0 locs) (l1 (sa1 5)) (l2 (sa2 5)) (f fnames) (e (em-names em)))))))

(defthm snv-abs-f
  (let ((l1t (cons (cons tmp ty) (true-list-fix l1))))
    (implies (and (snl s1 (svf-names c) l0 l1)
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

(defthm snv-cons-f
  (implies (and (consp vars) (consp xs)
                (not (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv)))
                (sn-ok-f (car xs) em cnt locs sigs fnames st)
                (snv-ok (cdr vars) (cdr xs) em (gfv 2) (gfv 3) sigs fnames st))
           (snv-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((snv-ok vars xs em cnt locs sigs fnames st)
                                            (g-svals vars xs em cnt locs sigs fnames st))
           :in-theory (e/d (snv-ok) (g-sexpr g-svals g-role g-fresh g-tmp em-names nfix))
           :use ((:instance snv-abs-f (s1 (sv1 1)) (c (sv1 2)) (tmp (gfv 1)) (ty (sv1 3)) (ss (svr 1)) (bs (svr 2))
                            (v (car vars)) (l0 locs) (l1 (sv1 5)) (l2 (svr 4)) (f fnames) (e (em-names em)))
                 (:instance g-fresh-out (b (car vars)) (ty (sv1 3)) (cnt (sv1 4)) (locs (sv1 5))
                            (used (append fnames (em-names em))))))))

(defthm sn-lam-abs-f
  (implies (and (subsetp-equal l0 l1) (subsetp-equal (asg :list s) (strip-cars l1))
                (not (intersectp-equal (asg :list s) f)) (not (intersectp-equal (asg :list s) e))
                (not (intersectp-equal (asg :list s) (strip-cars l0)))
                (subsetp-equal eb (strip-cars l1))
                (subsetp-equal l1 l2) (subsetp-equal (asg :list sb) (strip-cars l2))
                (not (intersectp-equal (asg :list sb) f)) (not (intersectp-equal (asg :list sb) (append eb e)))
                (not (intersectp-equal (asg :list sb) (strip-cars l1)))
                (subsetp-equal (svf-names cb) (append f (append eb e) (strip-cars l2))))
           (and (subsetp-equal l0 l2)
                (subsetp-equal (asg :list (append s sb)) (strip-cars l2))
                (not (intersectp-equal (asg :list (append s sb)) (append f e (strip-cars l0))))
                (subsetp-equal (svf-names cb) (append f e (strip-cars l2)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable subsetp-app-drop-mid)
           :use ((:instance subsetp-trans (a l0) (b l1) (c l2))
                 (:instance subsetp-strip-cars (a l1) (b l2))
                 (:instance subsetp-strip-cars (a l0) (b l1))
                 (:instance subsetp-trans (a eb) (b (strip-cars l1)) (c (strip-cars l2)))
                 (:instance subsetp-app-drop-mid (a (svf-names cb)) (b eb) (c (strip-cars l2)))))))

(defthm sn-lambda-f
  (implies (and (gs-lamp x st)
                (snv-ok (cadr (car x)) (cdr x) em cnt locs sigs fnames st)
                (sn-ok-f (caddr (car x)) (append (gl1 2) em) (gl1 3) (gl1 4) sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :expand ((sn-ok-f x em cnt locs sigs fnames st))
           :in-theory (e/d (snv-ok) (g-sexpr g-svals gs-lamp svf-names g-st-ident sn-ok-use-f))
           :use ((:instance sn-lam-abs-f (s (gl1 1)) (sb (gl2 1)) (cb (gl2 2)) (eb (em-names (gl1 2)))
                            (l0 locs) (l1 (gl1 4)) (l2 (gl2 5)) (f fnames) (e (em-names em)))
                 (:instance sn-ok-use-f (x (caddr (car x))) (em (append (gl1 2) em)) (cnt (gl1 3)) (locs (gl1 4)))))))

(defthm sn-err-f
  (implies (gsx 0) (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (e/d (sn-ok-f) (g-sexpr)))))

(defthm sn-rest-f
  (implies (and (not-leaf) (not (member-eq (car x) '(if implies the-check))) (not (consp (car x)))
                (not (consp (lkp (car x) sigs))) (sna-ok-f (cdr x) em cnt locs sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :cases ((g-role (car x) st))
           :in-theory (e/d (gs-primp) (sn-ok-f sna-ok-f g-sexpr g-st-free g-mvnth g-role sn-quote-role-f sn-prim-f))
           :use (sn-quote-role-f sn-prim-f))))

(defthm sn-if-any-f
  (implies (and (consp x) (eq (car x) 'if) (true-listp x) (not (g-st-free x st)) (not (g-role 'if st))
                (sn-ok-f (cadr x) em cnt locs sigs fnames st)
                (sn-ok-f (caddr x) em (j1 4) (j1 5) sigs fnames st)
                (sn-ok-f (cadddr x) em (j2 4) (j2 5) sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :cases ((= (len x) 4))
           :in-theory (e/d (gs-ifp) (sn-ok-f g-sexpr g-st-free g-role sn-if-f sn-err-f g-sexpr-if-badlen))
           :use (sn-if-f sn-err-f g-sexpr-if-badlen))))

(defthm sn-imp-any-f
  (implies (and (consp x) (eq (car x) 'implies) (true-listp x) (not (g-st-free x st)) (not (g-role 'implies st))
                (sn-ok-f (cadr x) em cnt locs sigs fnames st)
                (sn-ok-f (caddr x) em (j1 4) (j1 5) sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :cases ((= (len x) 3))
           :in-theory (e/d (gs-impp) (sn-ok-f g-sexpr g-st-free g-role sn-imp-f sn-err-f g-sexpr-if-badlen))
           :use (sn-imp-f sn-err-f g-sexpr-if-badlen))))

(defthm sn-free-any-f
  (implies (and (g-st-free x st) (sfc-ok :term x sigs st)) (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :cases ((g-mvnth x)) :in-theory (disable sn-ok-f g-sexpr g-st-free g-mvnth no-calls sfc-ok))))

(defthm sn-bad-f
  (implies (and (or (atom x) (not (true-listp x))) (not (g-mvnth x)) (sfc-ok :term x sigs st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t :cases ((g-st-free x st))
           :in-theory (disable sn-ok-f g-sexpr g-st-free g-mvnth sn-free-f sn-err-f g-sexpr-bad no-calls sfc-ok)
           :use (sn-free-f sn-err-f g-sexpr-bad))))

(defthm sn-ok-thm-f
  (implies (and (sobjs) (not (g-role 'if st)) (not (g-role 'implies st)))
           (if (eq flag :args) (implies (sfc-ok :list x sigs st) (sna-ok-f x em cnt locs sigs fnames st))
             (if (eq flag :vals) (implies (sfc-ok :list x sigs st) (snv-ok vars x em cnt locs sigs fnames st))
               (implies (sfc-ok :term x sigs st) (sn-ok-f x em cnt locs sigs fnames st)))))
  :rule-classes nil
  :hints (("Goal" :induct (sn-ind-f flag x vars em cnt locs sigs fnames st env s defs n fr heap) :do-not-induct t
           :in-theory (disable sn-ok-f sna-ok-f snv-ok g-sexpr g-sargs g-svals no-calls sfc-ok g-st-free g-mvnth g-role
                               gs-ifp gs-impp gs-lamp gs-primp sn-ok-use-f sna-ok-use-f g-fresh sx-fr-f a-svs-f))
          (and stable-under-simplificationp '(:in-theory (e/d (gs-ifp gs-impp gs-lamp gs-primp)
                                                              (sn-ok-f sna-ok-f snv-ok g-sexpr g-sargs g-svals no-calls sfc-ok g-st-free
                                                               g-mvnth g-role sn-ok-use-f sna-ok-use-f g-fresh sx-fr-f a-svs-f))))))

(defthm sn-ok-holds-f
  (implies (and (sn-hyps) (sfc-ok :term x sigs st)) (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :use (:instance sn-ok-thm-f (flag :expr)))))

(defthm sna-ok-holds-f
  (implies (and (sn-hyps) (sfc-ok :list xs sigs st)) (sna-ok-f xs em cnt locs sigs fnames st))
  :hints (("Goal" :use (:instance sn-ok-thm-f (flag :args) (x xs)))))

(defthm snv-ok-holds-f
  (implies (and (sn-hyps) (sfc-ok :list xs sigs st)) (snv-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :use (:instance sn-ok-thm-f (flag :vals) (x xs)))))
