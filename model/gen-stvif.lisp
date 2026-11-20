; gen-stvif: gstv-sem's if and lambda (no mv) cases (GEN.md 4 (4a) (2b)):
; gen-stcase's gst-if and gen-stlst's gst-lam on sxc-list, a-stv, with
; dests passed to the branches / the body unchanged.

(in-package "ACL2")

(include-book "gen-stvcase")

; ---- if

(defmacro iad (k) `(mv-nth ,k (g-stmt (caddr x) em (e1 4) (e1 5) sigs fnames st outs dests nil)))
(defmacro ibd (k) `(mv-nth ,k (g-stmt (cadddr x) em (iad 2) (iad 3) sigs fnames st outs dests nil)))

(defthm sifc-glue
  (let ((fr1 (mv-nth 1 (sx-list sc fr heap))))
    (implies (and (equal (car (sx-list sc fr heap)) :normal) (equal (mv-nth 2 (sx-list sc fr heap)) heap)
                  (not (car (sv cc fr1 heap))) (booleanp (mv-nth 1 (sv cc fr1 heap))))
             (let ((l (sxc-list (append sc (list (list :if cc sa sb))) fr heap))
                   (b (if (mv-nth 1 (sv cc fr1 heap)) (sxc-list sa fr1 heap) (sxc-list sb fr1 heap))))
               (and (equal (car l) (car b)) (equal (mv-nth 1 l) (mv-nth 1 b)) (equal (mv-nth 2 l) (mv-nth 2 b))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (e/d (sxc-list-append-sx) (sx sv sx-list sxc-list-is-sx-list))
           :expand ((sxc-list (list (list :if cc sa sb)) (mv-nth 1 (sx-list sc fr heap)) heap)
                    (sxc (list :if cc sa sb) (mv-nth 1 (sx-list sc fr heap)) heap)
                    (:free (f h) (sxc-list nil f h))))))

(defthm dests-apart-sub
  (implies (and (subsetp-equal a b) (not (intersectp-equal d (append f e (strip-cars b)))))
           (not (intersectp-equal d (append f e (strip-cars a)))))
  :hints (("Goal" :in-theory (enable intersectp-append-r)
           :use ((:instance subsetp-strip-cars) (:instance not-intersect-via-sub (a d) (b (strip-cars a)) (c (strip-cars b)))))))

(defmacro ifd-ctx ()
  '(and (consp x) (true-listp x) (eq (car x) 'if) (not (e1 0)) (equal (e1 3) :logical) (not (iad 0)) (not (ibd 0))
        (not (car (a-sx (cadr x) env s st defs (1- n))))
        (implies (ifc) (not (car (a-stv (caddr x) outs env s st defs (1- n)))))
        (implies (not (ifc)) (not (car (a-stv (cadddr x) outs env s st defs (1- n)))))
        (no-calls :term (cadr x) sigs nil) (em-ok em env fr) (decl-ok (ibd 3) fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
        (c-sorc o st) (c-sorc-d o st) (a-call-ok st o)
        (true-listp dests) (dests-ok dests fr) (equal (len dests) (nvals outs)) (no-duplicatesp-equal (dnames dests))
        (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars (ibd 3)))))
        (gstv-sem (caddr x) em (e1 4) (e1 5) sigs fnames st outs dests env s defs (1- n) (sfa) heap o)
        (gstv-sem (cadddr x) em (iad 2) (iad 3) sigs fnames st outs dests env s defs (1- n) (sfa) heap o)
        (stv-grow (caddr x) em (e1 4) (e1 5) sigs fnames st outs dests)
        (stv-grow (cadddr x) em (iad 2) (iad 3) sigs fnames st outs dests)))

(defun-nx ifd-ctxp (x em cnt locs sigs fnames st outs dests env s defs n fr heap o) (ifd-ctx))
(in-theory (disable ifd-ctxp))

(defmacro avt (k) `(mv-nth ,k (a-stv (caddr x) outs env s st defs (1- n))))
(defmacro ave (k) `(mv-nth ,k (a-stv (cadddr x) outs env s st defs (1- n))))

(defthm ifd-hyps
  (implies (ifd-ctxp x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
           (and (equal (car (sx-list (e1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (e1 1) fr heap)) heap)
                (em-ok em env (sfa)) (obj-at o s (sfa) heap) (dests-ok dests (sfa))
                (decl-ok (iad 3) (sfa)) (decl-ok (ibd 3) (sfa)) (decl-ok (e1 5) fr)
                (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars (iad 3)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(ifd-ctxp em-ok-after-sx decl-ok-after-sx obj-at-frame obj-at-cadr okey-after obj-at-is
                                        obj-is-after-sx scalar-ok dests-ok-after-sx (equal) (consp))
                                      (theory 'minimal-theory))
           :use ((:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-use (x (cadr x)))
                 (:instance gs-sem-holds (x (cadr x)) (n (1- n)))
                 (:instance gs-sem-use (x (cadr x)) (n (1- n)))
                 (:instance stv-grow-use (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance stv-grow-use (x (cadddr x)) (cnt (iad 2)) (locs (iad 3)))
                 (:instance decl-ok-subset (a (iad 3)) (b (ibd 3)))
                 (:instance decl-ok-subset (a (e1 5)) (b (iad 3)))
                 (:instance dests-apart-sub (d (dnames dests)) (f fnames) (e (em-names em)) (a (iad 3)) (b (ibd 3)))))))

(defthm ifd-run
  (implies (ifd-ctxp x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
           (and (equal (car (sx-list (e1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (e1 1) fr heap)) heap)
                (not (car (sv (e1 2) (sfa) heap))) (equal (mv-nth 1 (sv (e1 2) (sfa) heap)) (ifc)) (booleanp (ifc))
                (implies (ifc)
                         (and (equal (car (sxc-list (iad 1) (sfa) heap)) :normal)
                              (equal (mv-nth 2 (sxc-list (iad 1) (sfa) heap)) (put (okey o fr) (avt 1) heap))
                              (st-ok st o (avt 1)) (st-wf st (avt 1))
                              (svs-is dests (avt 2) (mv-nth 1 (sxc-list (iad 1) (sfa) heap)) (mv-nth 2 (sxc-list (iad 1) (sfa) heap)))))
                (implies (not (ifc))
                         (and (equal (car (sxc-list (ibd 1) (sfa) heap)) :normal)
                              (equal (mv-nth 2 (sxc-list (ibd 1) (sfa) heap)) (put (okey o fr) (ave 1) heap))
                              (st-ok st o (ave 1)) (st-wf st (ave 1))
                              (svs-is dests (ave 2) (mv-nth 1 (sxc-list (ibd 1) (sfa) heap)) (mv-nth 2 (sxc-list (ibd 1) (sfa) heap)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (mthy ifd-ctxp em-ok-after-sx decl-ok-after-sx obj-at-frame obj-at-cadr okey-after obj-at-is
                               obj-is-after-sx scalar-ok dests-ok-after-sx (equal) (consp))
           :use (ifd-hyps
                 (:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-use (x (cadr x)))
                 (:instance gs-sem-holds (x (cadr x)) (n (1- n)))
                 (:instance gs-sem-use (x (cadr x)) (n (1- n)))
                 (:instance gstv-sem-use (x (caddr x)) (cnt (e1 4)) (locs (e1 5)) (n (1- n)) (fr (sfa)))
                 (:instance gstv-sem-use (x (cadddr x)) (cnt (iad 2)) (locs (iad 3)) (n (1- n)) (fr (sfa)))))))

(defthm gstv-if
  (implies (and (consp x) (true-listp x) (eq (car x) 'if) (sn-hyps) (no-calls :term (cadr x) sigs nil)
                (gstv-sem (caddr x) em (e1 4) (e1 5) sigs fnames st outs dests env s defs (1- n) (sfa) heap o)
                (gstv-sem (cadddr x) em (iad 2) (iad 3) sigs fnames st outs dests env s defs (1- n) (sfa) heap o)
                (stv-grow (caddr x) em (e1 4) (e1 5) sigs fnames st outs dests)
                (stv-grow (cadddr x) em (iad 2) (iad 3) sigs fnames st outs dests))
           (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
           :in-theory (union-theories '(g-stmt-if-d a-stv-if ifd-ctxp mv-nth-0-car mv-nth-cons-k (equal) (cons) (posp)
                                        (binary-+) (unary--) car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (ifd-run (:instance sifc-glue (sc (e1 1)) (cc (e1 2)) (sa (iad 1)) (sb (ibd 1)))))))

(defthm stv-grow-if
  (implies (and (consp x) (true-listp x) (eq (car x) 'if) (sn-hyps) (no-calls :term (cadr x) sigs nil)
                (stv-grow (caddr x) em (e1 4) (e1 5) sigs fnames st outs dests)
                (stv-grow (cadddr x) em (iad 2) (iad 3) sigs fnames st outs dests))
           (stv-grow x em cnt locs sigs fnames st outs dests))
  :hints (("Goal" :do-not-induct t :expand ((stv-grow x em cnt locs sigs fnames st outs dests))
           :in-theory (union-theories '(g-stmt-if-d mv-nth-0-car mv-nth-cons-k subsetp-trans2 (equal) (cons) car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-use (x (cadr x)))
                 (:instance stv-grow-use (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance stv-grow-use (x (cadddr x)) (cnt (iad 2)) (locs (iad 3)))))))

; ---- the lambda (no mv): its bindings, its stobj updates, then the body with dests

(defmacro lcd (k) `(mv-nth ,k (g-stmt (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests nil)))
(defmacro lsv (k) `(mv-nth ,k (a-stv (caddr (car x)) outs (lenv) (ls1) st defs (1- n))))

(defmacro lamd-ctx ()
  '(and (consp x) (consp (car x)) (true-listp x) (true-listp (car x)) (equal (len (car x)) 3) (eq (caar x) 'lambda)
        (symbol-listp (vars)) (no-duplicatesp-equal (vars)) (equal (len (vars)) (len (cdr x))) (not (member-equal 'mv (vars)))
        (not (gl1 0)) (not (la 0)) (not (lcd 0))
        (not (car (a-sx-list (stv (vars) (cdr x) st) env s st defs (1- n))))
        (not (car (a-sacts (vars) (cdr x) env s st defs (1- n))))
        (not (lsv 0))
        (no-calls :list (cdr x) sigs nil) (em-ok em env fr) (decl-ok (lcd 3) fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
        (c-sorc o st) (c-sorc-d o st) (a-call-ok st o)
        (true-listp dests) (dests-ok dests fr) (equal (len dests) (nvals outs)) (no-duplicatesp-equal (dnames dests))
        (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars (lcd 3)))))
        (gsc-sem (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st env s defs (1- n) (lfb) heap o)
        (stan-ok (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st)
        (gstv-sem (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests (lenv) (ls1) defs (1- n) (lfc) (lh1) o)
        (stv-grow (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests)))

(defun-nx lamd-ctxp (x em cnt locs sigs fnames st outs dests env s defs n fr heap o) (lamd-ctx))
(in-theory (disable lamd-ctxp))

(defthm lamd-binds
  (implies (lamd-ctxp x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
           (and (equal (car (sx-list (gl1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (gl1 1) fr heap)) heap)
                (em-ok em env (lfb)) (em-ok (append (gl1 2) em) (lenv) (lfb)) (em-nostobj (append (gl1 2) em) st)
                (decl-ok (la 3) fr) (decl-ok (lcd 3) fr)
                (subsetp-equal (em-names (gl1 2)) (strip-cars (gl1 4)))
                (subsetp-equal (gl1 4) (la 3)) (subsetp-equal (la 3) (lcd 3))
                (not (intersectp-equal (asgv :list (la 1)) (append fnames (em-names em) (strip-cars (gl1 4)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(lamd-ctxp g-svals-stv no-calls-stv g-st-ident-stv len-stv decl-ok-after-sx
                                        obj-at-is kaddr kar kdr tlf-symbol-listp em-nostobj-append em-nostobj-g-svals (equal))
                                      (theory 'minimal-theory))
           :use ((:instance gs-sem-thm (flag :vals) (vars (vars)) (x (stv (vars) (cdr x) st)) (n (1- n)))
                 (:instance gsb-sem-use (vars (vars)) (xs (stv (vars) (cdr x) st)) (n (1- n)))
                 (:instance snv-ok-holds (vars (vars)) (xs (cdr x)))
                 (:instance snv-ok-use (vars (vars)) (xs (cdr x)))
                 (:instance stan-ok-use (vars (vars)) (xs (cdr x)) (cnt (gl1 3)) (locs (gl1 4)))
                 (:instance stv-grow-use (x (caddr (car x))) (em (append (gl1 2) em)) (cnt (la 2)) (locs (la 3)))
                 (:instance decl-ok-subset (a (la 3)) (b (lcd 3)))
                 (:instance decl-ok-subset (a (gl1 4)) (b (la 3)))))))

(defthm lamd-acts
  (implies (lamd-ctxp x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
           (and (equal (car (sx-list (la 1) (lfb) heap)) :normal) (equal (mv-nth 2 (sx-list (la 1) (lfb) heap)) (lh1))
                (st-ok st o (ls1)) (st-wf st (ls1)) (obj-at o (ls1) (lfc) (lh1))
                (em-ok (append (gl1 2) em) (lenv) (lfc)) (decl-ok (lcd 3) (lfc)) (equal (okey o (lfc)) (okey o fr))
                (dests-ok dests (lfc))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(lamd-ctxp decl-ok-after-sx dests-ok-after-sx obj-at-frame obj-at-cadr okey-after obj-at-after
                                        kaddr kar kdr (equal))
                                      (theory 'minimal-theory))
           :use (lamd-binds (:instance obj-at-after (s2 (ls1)) (fr (lfb)) (ss (la 1))) (:instance obj-at-cadr (fr (lfb)))
                 (:instance gsc-sem-use (vars (vars)) (xs (cdr x)) (cnt (gl1 3)) (locs (gl1 4)) (n (1- n)) (fr (lfb)))
                 (:instance lam-em-abs (b (gl1 2)) (env2 (lenv)) (fr0 (lfb)) (l (gl1 4)) (ss (la 1)) (f fnames) (h heap))))))

(defthm em-names-append-v (equal (em-names (append a b)) (append (em-names a) (em-names b))))

(defthm dests-apart-lam
  (implies (and (not (intersectp-equal d (append f (em-names em) (strip-cars l)))) (subsetp-equal (em-names b) (strip-cars l)))
           (not (intersectp-equal d (append f (em-names (append b em)) (strip-cars l)))))
  :hints (("Goal" :in-theory (enable intersectp-append-r)
           :use ((:instance not-intersect-via-sub (a d) (b (em-names b)) (c (strip-cars l)))))))

(defthm lamd-run
  (implies (lamd-ctxp x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
           (and (equal (car (sx-list (gl1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (gl1 1) fr heap)) heap)
                (equal (car (sx-list (la 1) (lfb) heap)) :normal) (equal (mv-nth 2 (sx-list (la 1) (lfb) heap)) (lh1))
                (equal (car (sxc-list (lcd 1) (lfc) (lh1))) :normal)
                (equal (mv-nth 2 (sxc-list (lcd 1) (lfc) (lh1))) (put (okey o fr) (lsv 1) heap))
                (st-ok st o (lsv 1)) (st-wf st (lsv 1))
                (svs-is dests (lsv 2) (mv-nth 1 (sxc-list (lcd 1) (lfc) (lh1))) (mv-nth 2 (sxc-list (lcd 1) (lfc) (lh1))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(lamd-ctxp obj-at-cadr okey-after put-put-same kaddr kar kdr (equal))
                                      (theory 'minimal-theory))
           :use (lamd-binds lamd-acts
                 (:instance dests-apart-sub (d (dnames dests)) (f fnames) (e (em-names em)) (a (gl1 4)) (b (lcd 3)))
                 (:instance subsetp-trans2 (a (gl1 4)) (b (la 3)) (c (lcd 3)))
                 (:instance subsetp-strip-cars-trans (a (em-names (gl1 2))) (b (gl1 4)) (c (lcd 3)))
                 (:instance dests-apart-lam (d (dnames dests)) (f fnames) (l (lcd 3)) (b (gl1 2)))
                 (:instance gstv-sem-use (x (caddr (car x))) (em (append (gl1 2) em)) (cnt (la 2)) (locs (la 3))
                            (env (lenv)) (s (ls1)) (n (1- n)) (fr (lfc)) (heap (lh1)))))))

(defthm gstv-lam
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (vars))) (sn-hyps) (em-nostobj em st)
                (no-calls :list (cdr x) sigs nil)
                (gsc-sem (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st env s defs (1- n) (lfb) heap o)
                (stan-ok (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st)
                (gstv-sem (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests (lenv) (ls1) defs (1- n) (lfc) (lh1) o)
                (stv-grow (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests))
           (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
           :in-theory (union-theories '(g-stmt-lam-d a-stv-lam a-st-args-split lamd-ctxp mv-nth-0-car mv-nth-cons-k
                                        sxc-list-append-sx (equal) (cons) (posp) (binary-+) (unary--) car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (lamd-run))))

(defthm stv-grow-lam
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (vars))) (sn-hyps)
                (no-calls :list (cdr x) sigs nil) (stan-ok (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st)
                (stv-grow (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests))
           (stv-grow x em cnt locs sigs fnames st outs dests))
  :hints (("Goal" :do-not-induct t :expand ((stv-grow x em cnt locs sigs fnames st outs dests))
           :in-theory (union-theories '(g-stmt-lam-d mv-nth-0-car mv-nth-cons-k subsetp-trans2 (equal) (cons) car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance snv-ok-holds (vars (vars)) (xs (cdr x)))
                 (:instance snv-ok-use (vars (vars)) (xs (cdr x)))
                 (:instance stan-ok-use (vars (vars)) (xs (cdr x)) (cnt (gl1 3)) (locs (gl1 4)))
                 (:instance stv-grow-use (x (caddr (car x))) (em (append (gl1 2) em)) (cnt (la 2)) (locs (la 3)))))))
