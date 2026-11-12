; gen-stlam: g-sexpr's lambda against a-sx, on sx/sv (GEN.md "What
; remains" 4 (a)): its value bindings (gsb-sem, gen-proof's gb-sem on
; g-svals), each temporary holding its argument's value, then the body in
; the new scope. A stobj var is bound only to itself (g-st-ident), a-sx
; gives it the value nil, so em must not bind a stobj var (em-nostobj).

(in-package "ACL2")

(include-book "gen-stnames")

(defun em-nostobj (em st)
  (if (atom em) t (and (not (eq (g-role (caar em) st) :stobj)) (em-nostobj (cdr em) st))))

(defthm em-nostobj-lkp
  (implies (and (em-nostobj em st) (eq (g-role k st) :stobj)) (not (consp (lkp k em))))
  :hints (("Goal" :in-theory (disable g-role))))

(defthm em-nostobj-append
  (equal (em-nostobj (append a b) st) (and (em-nostobj a st) (em-nostobj b st))))

; a var em does not bind may take any value
(defthm em-ok-unbound
  (implies (and (em-ok em env fr) (not (consp (lkp k em))))
           (em-ok em (cons (cons k v) env) fr))
  :hints (("Goal" :expand ((em-ok em (cons (cons k v) env) fr))
           :in-theory (e/d (var-ok) (em-ok-necc))
           :use ((:instance em-ok-necc (x (em-ok-witness em (cons (cons k v) env) fr)))))))

(defun gsb-sem (vars xs em cnt locs sigs fnames st env s defs n fr heap o)
  (mv-let (e ss binds cnt2 locs2) (g-svals vars xs em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae vs) (a-sx-list xs env s st defs n)
      (implies (and (not e) (not ae) (no-calls :list xs sigs nil) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (obj-is o s fr heap) (sn-hyps) (em-nostobj em st)
                    (symbol-listp vars) (no-duplicatesp-equal vars) (equal (len vars) (len xs))
                    (not (member-equal 'mv vars)) (g-st-ident vars xs st))
               (mv-let (stt fr2 h2) (sx-list ss fr heap)
                 (and (equal stt :normal) (equal h2 heap) (subsetp-equal (strip-cars binds) vars)
                      (em-nostobj binds st)
                      (em-ok em env fr2) (em-ok (append binds em) (pairlis$ vars vs) fr2)))))))

(defmacro gsv (k) `(mv-nth ,k (g-svals vars xs em cnt locs sigs fnames st)))

(defthm gsb-sem-use
  (implies (and (gsb-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                (not (gsv 0)) (not (car (a-sx-list xs env s st defs n))) (no-calls :list xs sigs nil) (em-ok em env fr)
                (decl-ok (gsv 4) fr) (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap) (sn-hyps)
                (em-nostobj em st) (symbol-listp vars) (no-duplicatesp-equal vars) (equal (len vars) (len xs))
                (not (member-equal 'mv vars)) (g-st-ident vars xs st))
           (and (equal (car (sx-list (gsv 1) fr heap)) :normal)
                (equal (mv-nth 2 (sx-list (gsv 1) fr heap)) heap)
                (subsetp-equal (strip-cars (gsv 2)) vars)
                (em-nostobj (gsv 2) st)
                (em-ok em env (mv-nth 1 (sx-list (gsv 1) fr heap)))
                (em-ok (append (gsv 2) em) (pairlis$ vars (mv-nth 1 (a-sx-list xs env s st defs n)))
                       (mv-nth 1 (sx-list (gsv 1) fr heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (gsb-sem) (g-svals a-sx-list sx-list no-calls em-ok decl-ok st-ok obj-is g-role)))))

(in-theory (disable gsb-sem))

; ---- openers

(defthm a-sx-list-open
  (implies (consp xs)
           (equal (a-sx-list xs env s st defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e v) (a-sx (car xs) env s st defs (1- n))
                      (if e (mv e nil)
                        (mv-let (e vs) (a-sx-list (cdr xs) env s st defs (1- n))
                          (if e (mv e nil) (mv nil (cons v vs)))))))))
  :hints (("Goal" :in-theory (disable a-sx) :expand ((a-sx-list xs env s st defs n)))))

(defthm a-sx-list-atom
  (implies (and (atom xs) (not (zp n))) (equal (a-sx-list xs env s st defs n) (mv nil nil)))
  :hints (("Goal" :expand ((a-sx-list xs env s st defs n)))))

(defthm a-sx-sym
  (implies (symbolp x)
           (equal (a-sx x env s st defs n)
                  (cond ((zp n) (mv :fuel nil))
                        ((eq (g-role x st) :stobj) (mv nil nil))
                        ((consp (lkp x env)) (mv nil (cdr (lkp x env))))
                        (t (mv :unbound nil)))))
  :hints (("Goal" :in-theory (disable g-role) :expand ((a-sx x env s st defs n) (g-st-free x st)))))

(defthm g-svals-nil
  (implies (or (atom vars) (atom xs)) (equal (g-svals vars xs em cnt locs sigs fnames st) (mv nil nil nil cnt locs)))
  :hints (("Goal" :expand ((g-svals vars xs em cnt locs sigs fnames st)))))

(defthm g-svals-skip
  (implies (and (consp vars) (consp xs)
                (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv)))
           (equal (g-svals vars xs em cnt locs sigs fnames st)
                  (g-svals (cdr vars) (cdr xs) em cnt locs sigs fnames st)))
  :hints (("Goal" :in-theory (disable g-sexpr g-role) :expand ((g-svals vars xs em cnt locs sigs fnames st)))))

(defthm g-svals-cons
  (implies (and (consp vars) (consp xs)
                (not (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv))))
           (equal (g-svals vars xs em cnt locs sigs fnames st)
                  (if (sv1 0) (mv (sv1 0) nil nil (sv1 4) (sv1 5))
                    (if (gfv 0) (mv (gfv 0) nil nil (gfv 2) (gfv 3))
                      (if (svr 0) (mv (svr 0) nil nil (svr 3) (svr 4))
                        (mv nil (append (sv1 1) (list (list :assign (list :var (gfv 1)) (sv1 2))) (svr 1))
                            (cons (list* (car vars) (gfv 1) (sv1 3)) (svr 2)) (svr 3) (svr 4)))))))
  :hints (("Goal" :in-theory (union-theories '(mv-nth) (theory 'minimal-theory))
           :expand ((g-svals vars xs em cnt locs sigs fnames st)))))

(in-theory (disable g-svals))

; ---- the value bindings

(defthm gsb-nil
  (implies (or (atom vars) (atom xs)) (gsb-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (enable gsb-sem) :cases ((consp vars))
           :expand ((sx-list nil fr heap) (a-sx-list xs env s st defs n) (len vars) (len xs)))))

(defthm not-member-binds
  (implies (and (subsetp-equal (strip-cars b) (cdr vars)) (no-duplicatesp-equal vars) (consp vars))
           (not (member-equal (car vars) (strip-cars b))))
  :hints (("Goal" :in-theory (disable member-subset-not)
           :use (:instance member-subset-not (k (car vars)) (a (strip-cars b)) (b (cdr vars))))))

(defthm em-ok-skip-stobj
  (implies (and (em-ok (append b em) env2 fr) (em-nostobj em st) (eq (g-role k st) :stobj)
                (not (member-equal k (strip-cars b))))
           (em-ok (append b em) (cons (cons k v) env2) fr))
  :hints (("Goal" :in-theory (disable g-role))))

(defthm gsb-skip
  (implies (and (consp vars) (consp xs)
                (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv))
                (gsb-sem (cdr vars) (cdr xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gsb-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gsb-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                                            (g-st-ident vars xs st) (no-calls :list xs sigs nil))
           :in-theory (disable g-sexpr a-sx a-sx-list sx-list no-calls em-ok decl-ok st-ok obj-is g-role a-sx-sym)
           :use ((:instance a-sx-sym (x (car xs)) (n (1- n)))))))

(defthm snv-ok-use
  (implies (and (snv-ok vars xs em cnt locs sigs fnames st) (not (gsv 0)))
           (and (subsetp-equal locs (gsv 4))
                (subsetp-equal (asg :list (gsv 1)) (strip-cars (gsv 4)))
                (not (intersectp-equal (asg :list (gsv 1)) fnames))
                (not (intersectp-equal (asg :list (gsv 1)) (em-names em)))
                (not (intersectp-equal (asg :list (gsv 1)) (strip-cars locs)))
                (subsetp-equal (em-names (gsv 2)) (strip-cars (gsv 4)))))
  :hints (("Goal" :in-theory (enable snv-ok))))

(defthm sx-list-cons-open
  (equal (sx-list (cons a b) fr heap)
         (mv-let (st fr2 h2) (sx a fr heap) (if (eq st :normal) (sx-list b fr2 h2) (mv st fr2 h2))))
  :hints (("Goal" :expand ((sx-list (cons a b) fr heap)) :in-theory (disable sx))))

(defthm obj-is-put-scalar
  (implies (and (obj-is o s fr heap) (equal (dty k fr) (list ty)) (scalar-ok ty v))
           (obj-is o s (put k (cons ty v) fr) heap))
  :hints (("Goal" :cases ((equal k o)) :in-theory (enable dty))))

(defthm subsetp-cons-vars
  (implies (and (consp vars) (subsetp-equal x (cdr vars))) (subsetp-equal (cons (car vars) x) vars)))

(defthm snv-keeps-tmp
  (implies (and (snv-ok vars xs em cnt (cons (cons k ty) l) sigs fnames st)
                (not (car (g-svals vars xs em cnt (cons (cons k ty) l) sigs fnames st))))
           (not (member-equal k (asg :list (mv-nth 1 (g-svals vars xs em cnt (cons (cons k ty) l) sigs fnames st))))))
  :hints (("Goal" :in-theory (disable snv-ok-use not-member-intersect)
           :use ((:instance snv-ok-use (locs (cons (cons k ty) l)))
                 (:instance not-member-intersect (y k) (a (strip-cars (cons (cons k ty) l)))
                            (b (asg :list (mv-nth 1 (g-svals vars xs em cnt (cons (cons k ty) l) sigs fnames st)))))))))

(defmacro frb () '(put (gfv 1) (cons (sv1 3) (mv-nth 1 (a-sx (car xs) env s st defs (1- n)))) (mv-nth 1 (sx-list (sv1 1) fr heap))))

(defthm gsb-cons
  (implies (and (consp vars) (consp xs)
                (not (or (eq (car vars) (car xs)) (eq (g-role (car vars) st) :stobj) (eq (car vars) 'mv)))
                (gs-sem (car xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gsb-sem (cdr vars) (cdr xs) em (gfv 2) (gfv 3) sigs fnames st env s defs (1- n) (frb) heap o))
           (gsb-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gsb-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o)
                                            (g-st-ident vars xs st) (no-calls :list xs sigs nil))
           :in-theory (disable g-sexpr a-sx a-sx-list sx-list sx sv no-calls em-ok st-ok obj-is g-role g-fresh
                               g-tmp nfix scalar-ok decl-ok-subset g-fresh-out dty subsetp-equal)
           :use ((:instance decl-ok-subset (a (gfv 3)) (b (svr 4)))
                 (:instance decl-ok-subset (a (sv1 5)) (b (gfv 3)))
                 (:instance g-fresh-out (b (car vars)) (ty (sv1 3)) (cnt (sv1 4)) (locs (sv1 5))
                            (used (append fnames (em-names em))))))))
