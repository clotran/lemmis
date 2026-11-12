; gen-stlst: g-stmt's lambda without mv against a-st on sx-list (GEN.md
; "What remains" 4 (a), step (2')): the value bindings by gsb-sem, then
; g-sacts' stobj updates in the outer em (gsc-sem), then the body in
; (append binds em).
;
; a-st-args threads S through the stobj arguments and reads every value on
; S0; it is split here into a-sx-list on stv (each stobj argument replaced
; by its var, whose a-sx is nil) and a-sacts (the stobj thread alone).

(in-package "ACL2")

(include-book "gen-stst")

(defthm mv-nth-0-car (equal (mv-nth 0 x) (car x)))
(defthm mv-nth-cons-k
  (implies (and (syntaxp (quotep k)) (posp k)) (equal (mv-nth k (cons a b)) (mv-nth (1- k) b))))
(in-theory (disable mv-nth-0-car mv-nth-cons-k))

(defun stv (vars xs st)
  (if (atom xs) nil
    (cons (if (eq (g-role (kar vars) st) :stobj) (kar vars) (car xs)) (stv (kdr vars) (cdr xs) st))))

(defun a-sacts (vars xs env s st defs n)
  ; the stobj thread of a-st-args: (mv err S')
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) (mv :fuel s))
        ((atom xs) (mv nil s))
        ((eq (g-role (kar vars) st) :stobj)
         (mv-let (e s1) (a-st (car xs) env s st defs (1- n))
           (if e (mv e s) (a-sacts (kdr vars) (cdr xs) env s1 st defs (1- n)))))
        (t (a-sacts (kdr vars) (cdr xs) env s st defs (1- n)))))

(defun a-sta-ind (vars xs env s st defs n)
  (declare (xargs :measure (nfix n)) (irrelevant env s defs))
  (cond ((zp n) nil)
        ((atom xs) nil)
        ((eq (g-role (kar vars) st) :stobj)
         (mv-let (e s1) (a-st (car xs) env s st defs (1- n)) (declare (ignore e)) (a-sta-ind (kdr vars) (cdr xs) env s1 st defs (1- n))))
        (t (a-sta-ind (kdr vars) (cdr xs) env s st defs (1- n)))))

(defthm a-st-args-split
  (implies (not (car (a-st-args vars xs env s0 s st defs n)))
           (and (not (car (a-sx-list (stv vars xs st) env s0 st defs n)))
                (equal (mv-nth 1 (a-st-args vars xs env s0 s st defs n))
                       (mv-nth 1 (a-sx-list (stv vars xs st) env s0 st defs n)))
                (not (car (a-sacts vars xs env s st defs n)))
                (equal (mv-nth 2 (a-st-args vars xs env s0 s st defs n))
                       (mv-nth 1 (a-sacts vars xs env s st defs n)))))
  :hints (("Goal" :induct (a-sta-ind vars xs env s st defs n)
           :in-theory (disable a-st a-sx g-role)
           :expand ((a-st-args vars xs env s0 s st defs n) (a-sacts vars xs env s st defs n)
                    (a-sx-list (stv vars xs st) env s0 st defs n) (stv vars xs st)
))))

(defthm g-svals-stv
  (equal (g-svals vars (stv vars xs st) em cnt locs sigs fnames st)
         (g-svals vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :induct (gsv-ind vars xs em cnt locs sigs fnames st)
           :in-theory (disable g-role g-sexpr g-fresh g-svals-cons g-svals-skip g-svals-nil)
           :expand ((stv vars xs st) (:free (xs) (g-svals vars xs em cnt locs sigs fnames st))))))

(defthm no-calls-stv
  (implies (no-calls :list xs sigs cs) (no-calls :list (stv vars xs st) sigs cs))
  :hints (("Goal" :induct (stv vars xs st) :in-theory (disable g-role)
           :expand ((no-calls :list xs sigs cs) (:free (a b) (no-calls :list (cons a b) sigs cs))
                    (no-calls :term (car vars) sigs cs)))))

(defthm g-st-ident-stv
  (implies (equal (len vars) (len xs)) (g-st-ident vars (stv vars xs st) st))
  :hints (("Goal" :induct (stv vars xs st) :in-theory (disable g-role))))

(defthm len-stv (equal (len (stv vars xs st)) (len xs)))

; ---- openers

(defthm g-stmt-lam
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (cadr (car x)))))
           (equal (g-stmt x em cnt locs sigs fnames st outs nil nil)
                  (let ((vars (cadr (car x))) (body (caddr (car x))))
                    (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                                  (no-duplicatesp-eq vars) (= (len vars) (len (cdr x)))))
                        (mv :stobj nil cnt locs)
                      (mv-let (e s binds cnt locs) (g-svals vars (cdr x) em cnt locs sigs fnames st)
                        (if e (mv e nil cnt locs)
                          (if (not (g-acts-place vars (cdr x) em st)) (mv :mv nil cnt locs)
                            (mv-let (e sa cnt locs) (g-sacts vars (cdr x) em cnt locs sigs fnames st)
                              (if e (mv e nil cnt locs)
                                (mv-let (e sb cnt locs) (g-stmt body (append binds em) cnt locs sigs fnames st outs nil nil)
                                  (if e (mv e nil cnt locs)
                                    (mv nil (append s sa sb) cnt locs))))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) '(kadr kaddr kar)) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs nil nil)))))

(defthm a-st-lam
  (implies (and (consp x) (consp (car x)))
           (equal (a-st x env s st defs n)
                  (if (zp n) (mv :fuel s)
                    (mv-let (e vs s1) (a-st-args (cadr (car x)) (cdr x) env s s st defs (1- n))
                      (if e (mv e s) (a-st (caddr (car x)) (pairlis$ (true-list-fix (cadr (car x))) vs) s1 st defs (1- n)))))))
  :hints (("Goal" :in-theory (e/d (kadr kaddr kar) (g-role a-sx a-st-args)) :expand ((a-st x env s st defs n)))))

(defthm g-sacts-nil
  (implies (or (atom vars) (atom xs)) (equal (g-sacts vars xs em cnt locs sigs fnames st) (mv nil nil cnt locs)))
  :hints (("Goal" :expand ((g-sacts vars xs em cnt locs sigs fnames st)))))

(defthm g-sacts-act
  (implies (and (consp vars) (consp xs) (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs))))
           (equal (g-sacts vars xs em cnt locs sigs fnames st)
                  (mv-let (e s cnt locs) (g-stmt (car xs) em cnt locs sigs fnames st (list (car vars)) nil nil)
                    (if e (mv e nil cnt locs)
                      (mv-let (e ss cnt locs) (g-sacts (cdr vars) (cdr xs) em cnt locs sigs fnames st)
                        (mv e (append s ss) cnt locs))))))
  :hints (("Goal" :in-theory (disable g-stmt g-role g-mvnth) :expand ((g-sacts vars xs em cnt locs sigs fnames st)))))

(defthm g-sacts-skip
  (implies (and (consp vars) (consp xs)
                (not (and (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs))))))
           (equal (g-sacts vars xs em cnt locs sigs fnames st) (g-sacts (cdr vars) (cdr xs) em cnt locs sigs fnames st)))
  :hints (("Goal" :in-theory (disable g-stmt g-role g-mvnth) :expand ((g-sacts vars xs em cnt locs sigs fnames st)))))

(defthm a-sacts-open
  (implies (and (not (zp n)) (consp xs))
           (equal (a-sacts vars xs env s st defs n)
                  (if (eq (g-role (kar vars) st) :stobj)
                      (mv-let (e s1) (a-st (car xs) env s st defs (1- n))
                        (if e (mv e s) (a-sacts (kdr vars) (cdr xs) env s1 st defs (1- n))))
                    (a-sacts (kdr vars) (cdr xs) env s st defs (1- n)))))
  :hints (("Goal" :in-theory (disable a-st g-role) :expand ((a-sacts vars xs env s st defs n)))))

(in-theory (disable a-sacts))

; ---- the stobj updates, g-sacts: each a gst-sem, S threaded

(defun gsc-sem (vars xs em cnt locs sigs fnames st env s defs n fr heap o)
  (mv-let (e ss cnt2 locs2) (g-sacts vars xs em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae s2) (a-sacts vars xs env s st defs n)
      (implies (and (not e) (not ae) (no-calls :list xs sigs nil) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
                    (equal (len vars) (len xs)))
               (mv-let (stt fr2 h2) (sx-list ss fr heap)
                 (declare (ignore fr2))
                 (and (equal stt :normal) (equal h2 (put (okey o fr) s2 heap)) (st-ok st o s2) (st-wf st s2)))))))

(defun stan-ok (vars xs em cnt locs sigs fnames st)
  (mv-let (e ss cnt2 locs2) (g-sacts vars xs em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (implies (not e)
             (and (subsetp-equal locs locs2) (subsetp-equal (asgv :list ss) (strip-cars locs2))
                  (not (intersectp-equal (asgv :list ss) (append fnames (em-names em) (strip-cars locs))))))))

(defmacro gac (k) `(mv-nth ,k (g-sacts vars xs em cnt locs sigs fnames st)))

(defthm gsc-sem-use
  (implies (and (gsc-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                (not (gac 0)) (not (car (a-sacts vars xs env s st defs n))) (no-calls :list xs sigs nil) (em-ok em env fr)
                (decl-ok (gac 3) fr) (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (st-wf st s) (obj-at o s fr heap)
                (sn-hyps) (em-nostobj em st) (equal (len vars) (len xs)))
           (and (equal (car (sx-list (gac 1) fr heap)) :normal)
                (equal (mv-nth 2 (sx-list (gac 1) fr heap)) (put (okey o fr) (mv-nth 1 (a-sacts vars xs env s st defs n)) heap))
                (st-ok st o (mv-nth 1 (a-sacts vars xs env s st defs n)))
                (st-wf st (mv-nth 1 (a-sacts vars xs env s st defs n)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (gsc-sem) (g-sacts a-sacts sx-list no-calls em-ok decl-ok st-ok st-wf obj-at)))))

(defthm stan-ok-use
  (implies (and (stan-ok vars xs em cnt locs sigs fnames st) (not (gac 0)))
           (and (subsetp-equal locs (gac 3))
                (subsetp-equal (asgv :list (gac 1)) (strip-cars (gac 3)))
                (not (intersectp-equal (asgv :list (gac 1)) (append fnames (em-names em) (strip-cars locs))))))
  :hints (("Goal" :in-theory (disable g-sacts))))

(in-theory (disable gsc-sem stan-ok))

(defthm gsc-nil
  (implies (or (atom vars) (atom xs)) (gsc-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (gsc-sem a-sacts) (obj-at)) :cases ((consp xs))
           :expand ((sx-list nil fr heap) (len xs) (len vars) (a-sacts vars xs env s st defs n)))))

(defthm a-st-mvnth
  (implies (and (g-mvnth x) (not (g-role 'mv-nth st))) (car (a-st x env s st defs n)))
  :hints (("Goal" :expand ((a-st x env s st defs n)))))

(defthm gsc-skip
  (implies (and (consp vars) (consp xs)
                (not (and (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs)))))
                (gsc-sem (cdr vars) (cdr xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gsc-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gsc-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                                            (no-calls :list xs sigs nil) (a-sacts vars xs env s st defs n))
           :in-theory (disable g-sacts a-st sx-list no-calls em-ok decl-ok st-ok st-wf obj-at g-role g-mvnth a-st-sym)
           :use ((:instance a-st-sym (x (car xs)) (n (1- n)))
                 (:instance a-st-mvnth (x (car xs)) (n (1- n)))))))

(defmacro gc1 (k) `(mv-nth ,k (g-stmt (car xs) em cnt locs sigs fnames st (list (car vars)) nil nil)))
(defmacro sc1 () '(mv-nth 1 (a-st (car xs) env s st defs (1- n))))
(defmacro frc1 () '(mv-nth 1 (sx-list (gc1 1) fr heap)))

(defthm len-cons-eq
  (implies (and (consp a) (consp b)) (equal (equal (len a) (len b)) (equal (len (cdr a)) (len (cdr b))))))

(defthm intersectp-append-r
  (equal (intersectp-equal x (append a b)) (or (intersectp-equal x a) (intersectp-equal x b))))

(defthm gsc-act
  (implies (and (consp vars) (consp xs) (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs)))
                (gst-sem (car xs) em cnt locs sigs fnames st (list (car vars)) env s defs (1- n) fr heap o)
                (stn-ok (car xs) em cnt locs sigs fnames st (list (car vars)))
                (gsc-sem (cdr vars) (cdr xs) em (gc1 2) (gc1 3) sigs fnames st env (sc1) defs (1- n) (frc1)
                         (put (okey o fr) (sc1) heap) o)
                (stan-ok (cdr vars) (cdr xs) em (gc1 2) (gc1 3) sigs fnames st))
           (gsc-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gsc-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                                            (no-calls :list xs sigs nil) (a-sacts vars xs env s st defs n))
           :in-theory (union-theories '(g-sacts-act kar kdr len-cons-eq intersectp-append-r sx-list-append em-ok-after-sx-v decl-ok-after-sx obj-at-after
                                        okey-after obj-at-cadr put-put-same mv-nth-0-car mv-nth-cons-k (posp) (binary-+) (unary--)
                                        car-cons cdr-cons (equal))
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance gst-sem-use (x (car xs)) (outs (list (car vars))) (n (1- n)))
                 (:instance stn-ok-use (x (car xs)) (outs (list (car vars))))
                 (:instance stan-ok-use (vars (cdr vars)) (xs (cdr xs)) (cnt (gc1 2)) (locs (gc1 3)))
                 (:instance decl-ok-subset (a (gc1 3)) (b (mv-nth 3 (g-sacts (cdr vars) (cdr xs) em (gc1 2) (gc1 3) sigs fnames st))))
                 (:instance gsc-sem-use (vars (cdr vars)) (xs (cdr xs)) (cnt (gc1 2)) (locs (gc1 3)) (s (sc1)) (n (1- n))
                            (fr (frc1)) (heap (put (okey o fr) (sc1) heap)))))))

; ---- the lambda: bindings, then the updates in the outer em, then the body

(defmacro vars () '(cadr (car x)))
(defmacro la (k) `(mv-nth ,k (g-sacts (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st)))
(defmacro lc (k) `(mv-nth ,k (g-stmt (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs nil nil)))
(defmacro lvs () '(mv-nth 1 (a-sx-list (stv (vars) (cdr x) st) env s st defs (1- n))))
(defmacro ls1 () '(mv-nth 1 (a-sacts (vars) (cdr x) env s st defs (1- n))))
(defmacro lenv () '(pairlis$ (true-list-fix (vars)) (lvs)))
(defmacro lfb () '(mv-nth 1 (sx-list (gl1 1) fr heap)))
(defmacro lfc () '(mv-nth 1 (sx-list (la 1) (lfb) heap)))
(defmacro lh1 () '(put (okey o fr) (ls1) heap))

; the body's scope survives the updates: they assign none of binds' temporaries
(defthm lam-em-abs
  (implies (and (em-ok (append b em) env2 fr0) (subsetp-equal (em-names b) (strip-cars l))
                (not (intersectp-equal (asgv :list ss) (append f (em-names em) (strip-cars l)))))
           (em-ok (append b em) env2 (mv-nth 1 (sx-list ss fr0 h))))
  :hints (("Goal" :in-theory (disable em-ok-after-sx-v not-intersect-via-sub)
           :use ((:instance em-ok-after-sx-v (em (append b em)) (env env2) (fr fr0) (s ss) (heap h))
                 (:instance not-intersect-via-sub (a (em-names b)) (b (asgv :list ss)) (c (strip-cars l)))))))

(defmacro lam-ctx ()
  '(and (consp x) (consp (car x)) (true-listp x) (true-listp (car x)) (equal (len (car x)) 3) (eq (caar x) 'lambda)
        (symbol-listp (vars)) (no-duplicatesp-equal (vars)) (equal (len (vars)) (len (cdr x))) (not (member-equal 'mv (vars)))
        (not (gl1 0)) (not (la 0)) (not (lc 0))
        (not (car (a-sx-list (stv (vars) (cdr x) st) env s st defs (1- n))))
        (not (car (a-sacts (vars) (cdr x) env s st defs (1- n))))
        (not (car (a-st (caddr (car x)) (lenv) (ls1) st defs (1- n))))
        (no-calls :term x sigs nil) (em-ok em env fr) (decl-ok (lc 3) fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
        (gsc-sem (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st env s defs (1- n) (lfb) heap o)
        (stan-ok (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st)
        (gst-sem (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs (lenv) (ls1) defs (1- n) (lfc) (lh1) o)
        (stn-ok (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs)))

(defun-nx lam-ctxp (x em cnt locs sigs fnames st outs env s defs n fr heap o) (lam-ctx))
(in-theory (disable lam-ctxp))

(defthm tlf-symbol-listp (implies (symbol-listp x) (equal (true-list-fix x) x)))

(defmacro ls2 () '(mv-nth 1 (a-st (caddr (car x)) (lenv) (ls1) st defs (1- n))))

(defthm lam-binds
  (implies (lam-ctxp x em cnt locs sigs fnames st outs env s defs n fr heap o)
           (and (equal (car (sx-list (gl1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (gl1 1) fr heap)) heap)
                (em-ok em env (lfb)) (em-ok (append (gl1 2) em) (lenv) (lfb)) (em-nostobj (append (gl1 2) em) st)
                (decl-ok (la 3) fr) (decl-ok (lc 3) fr)
                (subsetp-equal (em-names (gl1 2)) (strip-cars (gl1 4)))
                (not (intersectp-equal (asgv :list (la 1)) (append fnames (em-names em) (strip-cars (gl1 4)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(lam-ctxp g-svals-stv no-calls-stv g-st-ident-stv len-stv decl-ok-after-sx
                                        obj-at-is kaddr kar kdr tlf-symbol-listp em-nostobj-append em-nostobj-g-svals (equal))
                                      (theory 'minimal-theory))
           :expand ((no-calls :term x sigs nil))
           :use ((:instance gs-sem-thm (flag :vals) (vars (vars)) (x (stv (vars) (cdr x) st)) (n (1- n)))
                 (:instance gsb-sem-use (vars (vars)) (xs (stv (vars) (cdr x) st)) (n (1- n)))
                 (:instance snv-ok-holds (vars (vars)) (xs (cdr x)))
                 (:instance snv-ok-use (vars (vars)) (xs (cdr x)))
                 (:instance stan-ok-use (vars (vars)) (xs (cdr x)) (cnt (gl1 3)) (locs (gl1 4)))
                 (:instance stn-ok-use (x (caddr (car x))) (em (append (gl1 2) em)) (cnt (la 2)) (locs (la 3)))
                 (:instance decl-ok-subset (a (la 3)) (b (lc 3)))
                 (:instance decl-ok-subset (a (gl1 4)) (b (la 3)))))))

(defthm lam-acts
  (implies (lam-ctxp x em cnt locs sigs fnames st outs env s defs n fr heap o)
           (and (equal (car (sx-list (la 1) (lfb) heap)) :normal) (equal (mv-nth 2 (sx-list (la 1) (lfb) heap)) (lh1))
                (st-ok st o (ls1)) (st-wf st (ls1)) (obj-at o (ls1) (lfc) (lh1))
                (em-ok (append (gl1 2) em) (lenv) (lfc)) (decl-ok (lc 3) (lfc)) (equal (okey o (lfc)) (okey o fr))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(lam-ctxp decl-ok-after-sx obj-at-frame obj-at-cadr okey-after obj-at-after kaddr kar kdr
                                        (equal))
                                      (theory 'minimal-theory))
           :expand ((no-calls :term x sigs nil))
           :use (lam-binds (:instance obj-at-after (s2 (ls1)) (fr (lfb)) (ss (la 1))) (:instance obj-at-cadr (fr (lfb)))
                 (:instance gsc-sem-use (vars (vars)) (xs (cdr x)) (cnt (gl1 3)) (locs (gl1 4)) (n (1- n)) (fr (lfb)))
                 (:instance lam-em-abs (b (gl1 2)) (env2 (lenv)) (fr0 (lfb)) (l (gl1 4)) (ss (la 1)) (f fnames) (h heap))))))

(defthm lam-run
  (implies (lam-ctxp x em cnt locs sigs fnames st outs env s defs n fr heap o)
           (and (equal (car (sx-list (gl1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (gl1 1) fr heap)) heap)
                (equal (car (sx-list (la 1) (lfb) heap)) :normal) (equal (mv-nth 2 (sx-list (la 1) (lfb) heap)) (lh1))
                (equal (car (sx-list (lc 1) (lfc) (lh1))) :normal)
                (equal (mv-nth 2 (sx-list (lc 1) (lfc) (lh1))) (put (okey o fr) (ls2) heap))
                (st-ok st o (ls2)) (st-wf st (ls2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(lam-ctxp obj-at-cadr okey-after put-put-same kaddr kar kdr (equal))
                                      (theory 'minimal-theory))
           :expand ((no-calls :term x sigs nil))
           :use (lam-binds lam-acts
                 (:instance gst-sem-use (x (caddr (car x))) (em (append (gl1 2) em)) (cnt (la 2)) (locs (la 3))
                            (env (lenv)) (s (ls1)) (n (1- n)) (fr (lfc)) (heap (lh1)))))))

(defthm gst-lam
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (vars))) (sn-hyps) (em-nostobj em st)
                (gsc-sem (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st env s defs (1- n) (lfb) heap o)
                (stan-ok (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st)
                (gst-sem (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs (lenv) (ls1) defs (1- n) (lfc) (lh1) o)
                (stn-ok (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
           :in-theory (union-theories '(g-stmt-lam a-st-lam a-st-args-split sx-list-append lam-ctxp mv-nth-0-car mv-nth-cons-k
                                        (equal) (cons) (posp) (binary-+) (unary--) car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (lam-run))))
