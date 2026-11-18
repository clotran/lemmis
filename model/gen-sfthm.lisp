; gen-sfthm: gen-stthm on svf/sxf-list/a-sxf (clone.py), plus the call case.

(in-package "ACL2")

(include-book "gen-stthm")
(include-book "gen-sflam")

(defthm a-sx-the-check-f
  (implies (and (not-leaf) (eq (car x) 'the-check) (= (len x) 4) (no-prim-defs defs) (not (car (a-sxf x env s st defs n))))
           (and (not (car (a-sxf (cadddr x) env s st defs (- n 4))))
                (equal (mv-nth 1 (a-sxf x env s st defs n)) (mv-nth 1 (a-sxf (cadddr x) env s st defs (- n 4))))))
  :hints (("Goal" :in-theory (e/d (kaddr kdr kar) (g-st-free g-role a-ev a-sxf g-mvnth no-prim-defs))
           :expand ((a-sxf x env s st defs n) (a-sxf-list (cdr x) env s st defs (1- n))
                    (a-sxf-list (cddr x) env s st defs (+ -2 n)) (a-sxf-list (cdddr x) env s st defs (+ -3 n))
                    (a-sxf-list (cddddr x) env s st defs (+ -4 n)) (len x) (len (cdr x)) (len (cddr x))
                    (len (cdddr x)) (len (cddddr x))))))

(defthm gsx-the-check-f
  (implies (and (not-leaf) (eq (car x) 'the-check)
                (gs-sem-f (cadddr x) em cnt locs sigs fnames st env s defs (- n 4) fr heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((= (len x) 4))
           :expand ((gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
           :in-theory (disable g-sexpr a-sxf sxf-list svf no-calls sfc-ok em-ok decl-ok scalar-ok st-ok obj-is g-st-free
                               g-mvnth g-role gs-sem-use-f)
           :use ((:instance gs-sem-use-f (x (cadddr x)) (n (- n 4)))))))

(defthm a-sx-imp-f
  (implies (and (gs-impp x st) (no-prim-defs defs) (not (car (a-sxf x env s st defs n))))
           (and (not (car (a-sxf (cadr x) env s st defs (- n 2))))
                (not (car (a-sxf (caddr x) env s st defs (- n 3))))
                (equal (mv-nth 1 (a-sxf x env s st defs n))
                       (implies (mv-nth 1 (a-sxf (cadr x) env s st defs (- n 2)))
                                (mv-nth 1 (a-sxf (caddr x) env s st defs (- n 3)))))))
  :hints (("Goal" :in-theory (e/d (kaddr kdr kar) (g-st-free g-role a-ev a-sxf g-mvnth no-prim-defs))
           :expand ((a-sxf x env s st defs n) (a-sxf-list (cdr x) env s st defs (1- n))
                    (a-sxf-list (cddr x) env s st defs (+ -2 n)) (a-sxf-list (cdddr x) env s st defs (+ -3 n))
                    (len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))))))

(defthm sx-list-nil-f (equal (sxf-list nil fr heap) (mv :normal fr heap)) :hints (("Goal" :expand ((sxf-list nil fr heap)))))

(defthm sv-true-f (equal (svf '(:true) fr heap) (mv nil t)))

(defthm gsx-implies-f
  (implies (and (gs-impp x st)
                (gs-sem-f (cadr x) em cnt locs sigs fnames st env s defs (- n 2) fr heap o)
                (gs-sem-f (caddr x) em (j1 4) (j1 5) sigs fnames st env s defs (- n 3) (fr1-f) heap o)
                (sn-ok-f (cadr x) em cnt locs sigs fnames st)
                (sn-ok-f (caddr x) em (j1 4) (j1 5) sigs fnames st))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
           :cases ((and (mv-nth 1 (a-sxf (cadr x) env s st defs (- n 2))) (booleanp (mv-nth 1 (a-sxf (caddr x) env s st defs (- n 3)))))
                   (not (mv-nth 1 (a-sxf (cadr x) env s st defs (- n 2)))))
           :in-theory (disable g-sexpr a-sxf sxf-list sxf svf no-calls sfc-ok em-ok scalar-ok st-ok obj-is gs-impp
                               g-sexpr-imp if-stmts g-tmp nfix dty decl-ok-subset sif-glue-f sv-is-fv-f fv
                               sx-list-is-fx-list-f fx-list sxf-sx-list-cons svf-is-sv sxf-list-is-sx-list)
           :do-not (quote (eliminate-destructors generalize))
           :use ((:instance decl-ok-subset (a (j1 5)) (b (j2 5)))))))

(defthm gs-err-f
  (implies (gsx 0) (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gs-sem-f) (g-sexpr a-sxf sxf-list svf)))))

(defthm gs-nocalls-f
  (implies (not (sfc-ok :term x sigs st)) (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gs-sem-f) (g-sexpr a-sxf sxf-list svf no-calls sfc-ok)))))

(defthm gsa-nocalls-f
  (implies (not (sfc-ok :list xs sigs st)) (gsa-sem-f xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gsa-sem-f) (g-sargs a-sxf-list sxf-list svs-ok-f no-calls sfc-ok)))))

(defthm gsb-nocalls-f
  (implies (not (sfc-ok :list xs sigs st)) (gsb-sem-f vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gsb-sem-f) (g-svals a-sxf-list sxf-list no-calls sfc-ok em-ok)))))

(defthm gs-free-any-f
  (implies (g-st-free x st) (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :cases ((g-mvnth x)) :in-theory (disable gs-sem-f g-sexpr g-st-free g-mvnth))))

(defthm gs-bad-f
  (implies (and (or (atom x) (not (true-listp x))) (not (g-mvnth x)))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((g-st-free x st))
           :in-theory (disable gs-sem-f g-sexpr g-st-free g-mvnth gs-free-f gs-err-f g-sexpr-bad)
           :use (gs-free-f gs-err-f g-sexpr-bad))))

(defthm gs-if-any-f
  (implies (and (consp x) (eq (car x) 'if) (true-listp x) (not (g-st-free x st)) (sn-hyps)
                (gs-sem-f (cadr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gs-sem-f (caddr x) em (j1 4) (j1 5) sigs fnames st env s defs (1- n) (fr1-f) heap o)
                (gs-sem-f (cadddr x) em (j2 4) (j2 5) sigs fnames st env s defs (1- n) (fr1-f) heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((and (= (len x) 4) (sfc-ok :term x sigs st)) (not (= (len x) 4)))
           :in-theory (e/d (gs-ifp) (gs-sem-f sn-ok-f g-sexpr g-st-free g-role gsx-if-f gs-err-f g-sexpr-if-badlen no-calls sfc-ok))
           :use (gsx-if-f gs-err-f g-sexpr-if-badlen))))

(defthm gs-imp-any-f
  (implies (and (consp x) (eq (car x) 'implies) (true-listp x) (not (g-st-free x st)) (sn-hyps)
                (gs-sem-f (cadr x) em cnt locs sigs fnames st env s defs (- n 2) fr heap o)
                (gs-sem-f (caddr x) em (j1 4) (j1 5) sigs fnames st env s defs (- n 3) (fr1-f) heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((and (= (len x) 3) (sfc-ok :term x sigs st)) (not (= (len x) 3)))
           :in-theory (e/d (gs-impp) (gs-sem-f sn-ok-f g-sexpr g-st-free g-role gsx-implies-f gs-err-f g-sexpr-if-badlen no-calls sfc-ok))
           :use (gsx-implies-f gs-err-f g-sexpr-if-badlen))))

(defthm gs-rest-f
  (implies (and (not-leaf) (not (member-eq (car x) '(if implies the-check))) (not (consp (car x)))
                (gsa-sem-f (cdr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gsa-sem-f (g-cvals (kar (cdr (lkp (car x) sigs))) (cdr x) st) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((consp (lkp (car x) sigs)) (g-role (car x) st) (eq (car x) 'quote))
           :in-theory (e/d (gs-primp) (gs-sem-f gsa-sem-f g-sexpr g-st-free g-mvnth g-role gs-prim-f gs-err-f g-sexpr-role-err
                                      gs-call-f))
           :use (gs-prim-f gs-err-f g-sexpr-role-err gs-call-f))))

(defthm gsa-cons-any-f
  (implies (and (consp xs) (sn-hyps)
                (gs-sem-f (car xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gsa-sem-f (cdr xs) em (sa1 4) (sa1 5) sigs fnames st env s defs (1- n)
                         (mv-nth 1 (sxf-list (sa1 1) fr heap)) heap o))
           (gsa-sem-f xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((sfc-ok :list xs sigs st))
           :in-theory (disable gs-sem-f gsa-sem-f sn-ok-f sna-ok-f g-sexpr g-sargs no-calls sfc-ok gsa-cons-f)
           :use (gsa-cons-f))))

(defthm gs-lam-any-f
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (g-st-free x st)) (sn-hyps) (em-nostobj em st)
                (gsb-sem-f (cadr (car x)) (cdr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gs-sem-f (caddr (car x)) (append (gl1 2) em) (gl1 3) (gl1 4) sigs fnames st
                        (pairlis$ (true-list-fix (cadr (car x))) (mv-nth 1 (a-sxf-list (cdr x) env s st defs (1- n))))
                        s defs (1- n) (mv-nth 1 (sxf-list (gl1 1) fr heap)) heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (gs-lamp) (gs-sem-f gsb-sem-f g-sexpr g-svals g-st-free gsx-lambda-f))
           :use (gsx-lambda-f))))

(defthm gs-sem-thm-f
  (implies (and (sn-hyps) (em-nostobj em st))
           (if (eq flag :args) (gsa-sem-f x em cnt locs sigs fnames st env s defs n fr heap o)
             (if (eq flag :vals) (gsb-sem-f vars x em cnt locs sigs fnames st env s defs n fr heap o)
               (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))))
  :rule-classes nil
  :hints (("Goal" :induct (sn-ind-f flag x vars em cnt locs sigs fnames st env s defs n fr heap) :do-not-induct t
           :in-theory (union-theories
                       '((:induction sn-ind-f) sx-fr-f a-sv-f a-svs-f em-nostobj-append em-nostobj-g-svals
                         gs-err-f gs-nocalls-f gsa-nocalls-f gsb-nocalls-f gs-bad-f gs-mvnth-f gs-free-f gs-free-any-f gs-field-f gs-size-f gs-elem-f
                         gs-if-any-f gs-imp-any-f gsx-the-check-f gs-rest-f gsa-nil-f gsa-cons-any-f gsb-nil-f gsb-skip-f gsb-cons-f
                         gs-lam-any-f)
                       (theory 'minimal-theory)))
          (and stable-under-simplificationp '(:in-theory (e/d (sx-fr-f a-sv-f a-svs-f) (g-sexpr g-sargs g-svals no-calls sfc-ok a-sxf
                                                                a-sxf-list sxf-list gs-sem-f gsa-sem-f gsb-sem-f g-role g-st-free g-mvnth))))))

(defthm gs-sem-holds-f
  (implies (and (sn-hyps) (em-nostobj em st)) (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :use (:instance gs-sem-thm-f (flag :expr)))))
