; gen-sflam: gen-stlam on svf/sxf-list/a-sxf (clone.py).

(in-package "ACL2")

(include-book "gen-stlam")
(include-book "gen-sfnames")

(defun gsb-sem-f (vars xs em cnt locs sigs fnames st env s defs n fr heap o)
  (mv-let (e ss binds cnt2 locs2) (g-svals vars xs em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae vs) (a-sxf-list xs env s st defs n)
      (implies (and (not e) (not ae) (sfc-ok :list xs sigs st) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (obj-is o s fr heap) (sn-hyps) (em-nostobj em st)
                    (symbol-listp vars) (no-duplicatesp-equal vars) (equal (len vars) (len xs))
                    (not (member-equal 'mv vars)) (g-st-ident vars xs st))
               (mv-let (stt fr2 h2) (sxf-list ss fr heap)
                 (and (equal stt :normal) (equal h2 heap) (subsetp-equal (strip-cars binds) vars)
                      (em-nostobj binds st)
                      (em-ok em env fr2) (em-ok (append binds em) (pairlis$ vars vs) fr2)))))))

(defthm gsb-sem-use-f
  (implies (and (gsb-sem-f vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                (not (gsv 0)) (not (car (a-sxf-list xs env s st defs n))) (sfc-ok :list xs sigs st) (em-ok em env fr)
                (decl-ok (gsv 4) fr) (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap) (sn-hyps)
                (em-nostobj em st) (symbol-listp vars) (no-duplicatesp-equal vars) (equal (len vars) (len xs))
                (not (member-equal 'mv vars)) (g-st-ident vars xs st))
           (and (equal (car (sxf-list (gsv 1) fr heap)) :normal)
                (equal (mv-nth 2 (sxf-list (gsv 1) fr heap)) heap)
                (subsetp-equal (strip-cars (gsv 2)) vars)
                (em-nostobj (gsv 2) st)
                (em-ok em env (mv-nth 1 (sxf-list (gsv 1) fr heap)))
                (em-ok (append (gsv 2) em) (pairlis$ vars (mv-nth 1 (a-sxf-list xs env s st defs n)))
                       (mv-nth 1 (sxf-list (gsv 1) fr heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (gsb-sem-f) (g-svals a-sxf-list sxf-list no-calls sfc-ok em-ok decl-ok st-ok obj-is g-role)))))

(in-theory (disable gsb-sem-f))

(defthm a-sx-list-open-f
  (implies (consp xs)
           (equal (a-sxf-list xs env s st defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e v) (a-sxf (car xs) env s st defs (1- n))
                      (if e (mv e nil)
                        (mv-let (e vs) (a-sxf-list (cdr xs) env s st defs (1- n))
                          (if e (mv e nil) (mv nil (cons v vs)))))))))
  :hints (("Goal" :in-theory (disable a-sxf) :expand ((a-sxf-list xs env s st defs n)))))

(defthm a-sx-list-atom-f
  (implies (and (atom xs) (not (zp n))) (equal (a-sxf-list xs env s st defs n) (mv nil nil)))
  :hints (("Goal" :expand ((a-sxf-list xs env s st defs n)))))

(defthm a-sx-sym-f
  (implies (symbolp x)
           (equal (a-sxf x env s st defs n)
                  (cond ((zp n) (mv :fuel nil))
                        ((eq (g-role x st) :stobj) (mv nil nil))
                        ((consp (lkp x env)) (mv nil (cdr (lkp x env))))
                        (t (mv :unbound nil)))))
  :hints (("Goal" :in-theory (disable g-role) :expand ((a-sxf x env s st defs n) (g-st-free x st)))))

(defthm gsb-nil-f
  (implies (or (atom vars) (atom xs)) (gsb-sem-f vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (enable gsb-sem-f) :cases ((consp vars))
           :expand ((sxf-list nil fr heap) (a-sxf-list xs env s st defs n) (len vars) (len xs)))))

(defthm gsb-skip-f
  (implies (and (consp vars) (consp xs)
                (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv))
                (gsb-sem-f (cdr vars) (cdr xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gsb-sem-f vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gsb-sem-f vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                                            (g-st-ident vars xs st) (sfc-ok :list xs sigs st))
           :in-theory (disable g-sexpr a-sxf a-sxf-list sxf-list no-calls sfc-ok em-ok decl-ok st-ok obj-is g-role a-sx-sym-f)
           :use ((:instance a-sx-sym-f (x (car xs)) (n (1- n)))))))

(defthm sx-list-cons-open-f
  (equal (sxf-list (cons a b) fr heap)
         (mv-let (st fr2 h2) (sxf a fr heap) (if (eq st :normal) (sxf-list b fr2 h2) (mv st fr2 h2))))
  :hints (("Goal" :expand ((sxf-list (cons a b) fr heap)) :in-theory (disable sxf))))

(defmacro frb-f () '(put (gfv 1) (cons (sv1 3) (mv-nth 1 (a-sxf (car xs) env s st defs (1- n)))) (mv-nth 1 (sxf-list (sv1 1) fr heap))))

(defthm gsb-cons-f
  (implies (and (consp vars) (consp xs)
                (not (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv)))
                (gs-sem-f (car xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gsb-sem-f (cdr vars) (cdr xs) em (gfv 2) (gfv 3) sigs fnames st env s defs (1- n) (frb-f) heap o))
           (gsb-sem-f vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gsb-sem-f vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                                            (g-st-ident vars xs st) (sfc-ok :list xs sigs st))
           :in-theory (disable g-sexpr a-sxf a-sxf-list sxf-list sxf svf no-calls sfc-ok em-ok st-ok obj-is g-role g-fresh
                               g-tmp nfix scalar-ok decl-ok-subset g-fresh-out dty subsetp-equal)
           :use ((:instance decl-ok-subset (a (gfv 3)) (b (svr 4)))
                 (:instance decl-ok-subset (a (sv1 5)) (b (gfv 3)))
                 (:instance g-fresh-out (b (car vars)) (ty (sv1 3)) (cnt (sv1 4)) (locs (sv1 5))
                            (used (append fnames (em-names em))))))))

(defthm a-sx-lambda-f
  (implies (and (consp x) (consp (car x)) (not (g-st-free x st)))
           (equal (a-sxf x env s st defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e vs) (a-sxf-list (cdr x) env s st defs (1- n))
                      (if e (mv e nil)
                        (a-sxf (caddr (car x)) (pairlis$ (true-list-fix (cadr (car x))) vs) s st defs (1- n)))))))
  :hints (("Goal" :in-theory (e/d (kar kdr) (a-sxf-list g-st-free g-role a-ev)) :expand ((a-sxf x env s st defs n)))))

(defthm gsx-lambda-f
  (implies (and (gs-lamp x st) (sn-hyps) (em-nostobj em st)
                (gsb-sem-f (cadr (car x)) (cdr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gs-sem-f (caddr (car x)) (append (gl1 2) em) (gl1 3) (gl1 4) sigs fnames st
                        (pairlis$ (true-list-fix (cadr (car x))) (mv-nth 1 (a-sxf-list (cdr x) env s st defs (1- n))))
                        s defs (1- n) (mv-nth 1 (sxf-list (gl1 1) fr heap)) heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
           :in-theory (disable g-sexpr g-svals a-sxf a-sxf-list sxf-list sxf svf no-calls sfc-ok em-ok st-ok obj-is g-role
                               scalar-ok decl-ok-subset g-st-ident sv-is-fv-f fv sx-list-is-fx-list-f)
           :use ((:instance decl-ok-subset (a (gl1 4)) (b (gl2 5)))))))
