; gen-stcallu: g-callst with stobj arguments that are updates (GEN.md 4 (4a)
; (ii), first piece). acl2-fortran's call-stmt settles the value arguments
; when a stobj argument is an update: each argument's statements, then,
; unless its code is g-stable, the code into a temporary v_N (g-settle);
; then the updates (g-sacts), then CALL f(objs, codes). The source's
; meaning (`a-stcall-u`): the value arguments by a-sx-list on S, the stobj
; arguments' updates threaded from S (a-sacts), then a-call-val on the
; values and the updated S. `gst-callst-u`: under gst-callst's hypotheses
; (c-sorc, a-call-ok, no-calls, em-ok, decl-ok, st-ok, st-wf, obj-at,
; sn-hyps, em-nostobj) plus the updates' gsc-sem/stan-ok (as gst-lam takes
; them), sxc-list of g-callst's statements answers :normal, the heap put to
; a-stcall-u's S'.

(in-package "ACL2")

(include-book "gen-stccall")

; ---- set facts


(defthm subsetp-strip-cars (implies (subsetp-equal a b) (subsetp-equal (strip-cars a) (strip-cars b))))




; the temporary is not assigned by the rest: the rest's argument statements
; assign their own locals (within la, within l2, which v is not in), its
; temporaries are none of l2' (which has v)
(defthm v-not-asg-abs
  (implies (and (subsetp-equal (asg :list tr) (append af vs))
                (subsetp-equal af (strip-cars la)) (subsetp-equal la l2)
                (not (member-equal v (strip-cars l2)))
                (not (intersectp-equal vs (strip-cars (cons (cons v ty) l2x)))))
           (not (member-equal v (asg :list tr))))
  :rule-classes nil)

(defthm intersectp-member-both
  (implies (and (member-equal z p) (member-equal z q)) (intersectp-equal p q)))

(defthm intersectp-cons-2 (iff (intersectp-equal b (cons x a)) (or (member-equal x b) (intersectp-equal b a)))
  :hints (("Goal" :induct (len b))))

(defthm intersectp-comm (equal (intersectp-equal a b) (intersectp-equal b a)) :rule-classes nil
  :hints (("Goal" :induct (len a))))

(defthm disj-subsets
  (implies (and (subsetp-equal x p) (subsetp-equal y q) (not (intersectp-equal p q))) (not (intersectp-equal x y)))
  :hints (("Goal" :induct (len x))))

; a stable code's names are not assigned by the rest
(defthm stable-not-asg-abs
  (implies (and (subsetp-equal nm (append f e (strip-cars l1)))
                (subsetp-equal a (append af vs))
                (not (intersectp-equal af f)) (not (intersectp-equal af e)) (not (intersectp-equal af (strip-cars l1)))
                (not (intersectp-equal vs (append f e))) (not (intersectp-equal vs (strip-cars l2)))
                (subsetp-equal l1 l2))
           (not (intersectp-equal nm a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable disj-subsets)
           :use ((:instance disj-subsets (x nm) (p (append f e (strip-cars l1))) (y a) (q (append af vs)))
                 (:instance intersectp-comm (a af) (b f)) (:instance intersectp-comm (a af) (b e))
                 (:instance intersectp-comm (a af) (b (strip-cars l1))) (:instance intersectp-comm (a vs) (b f))
                 (:instance intersectp-comm (a vs) (b e))
                 (:instance disj-subsets (x (strip-cars l1)) (p (strip-cars l2)) (y vs) (q vs))
                 (:instance intersectp-comm (a vs) (b (strip-cars l2)))))))



; ---- the settled arguments, statically

; g-sargs' statements, one list per argument (g-scall-args' sss)
(defun g-sss (xs em cnt locs sigs fnames st)
  (if (atom xs) nil
    (mv-let (e s c ty cnt locs) (g-sexpr (car xs) em cnt locs sigs fnames st)
      (declare (ignore e c ty))
      (cons s (g-sss (cdr xs) em cnt locs sigs fnames st)))))

(defthm g-scall-args-sss
  (implies (not (gsc 0)) (equal (gsc 1) (g-sss (g-cvals formals xs st) em cnt locs sigs fnames st)))
  :hints (("Goal" :induct (gsc-ind formals xs em cnt locs sigs fnames st)
           :in-theory (disable g-sexpr)
           :expand ((g-scall-args formals xs t em cnt locs sigs fnames st)
                    (g-sss (g-cvals formals xs st) em cnt locs sigs fnames st)
                    (g-cvals formals xs st)))))

; the temporaries g-settle adds
(defun g-settle-vs (sss cs cnt locs used)
  (declare (irrelevant sss))
  (if (atom cs) nil
    (mv-let (e tmp cnt locs) (if (g-stable (car cs)) (mv nil nil cnt locs) (g-fresh 'v :int64 cnt locs used))
      (declare (ignore e))
      (if tmp (cons tmp (g-settle-vs (cdr sss) (cdr cs) cnt locs used))
        (g-settle-vs (cdr sss) (cdr cs) cnt locs used)))))

(defun stables (cs) (if (atom cs) t (and (g-stable (car cs)) (stables (cdr cs)))))

(defmacro gse (k) `(mv-nth ,k (g-settle sss cs cnt locs used)))
(defmacro gvs () '(g-settle-vs sss cs cnt locs used))

(defthm asg-assign-var (equal (asg :list (list (list :assign (list :var v) c))) (list v))
  :hints (("Goal" :expand ((asg :list (list (list :assign (list :var v) c))) (asg :list nil)))))

(defthm asg-true-list-fix (equal (asg :list (true-list-fix ss)) (asg :list ss))
  :hints (("Goal" :induct (len ss) :expand ((asg :list ss) (:free (a b) (asg :list (cons a b))) (true-list-fix ss)))))

(defthm subsetp-append-l (implies (subsetp-equal a b) (subsetp-equal a (append b c))))
(defthm subsetp-append-r (implies (subsetp-equal a c) (subsetp-equal a (append b c))))
(defthm subsetp-append-split (equal (subsetp-equal (append a b) c) (and (subsetp-equal a c) (subsetp-equal b c))))
(defthm intersectp-append-l (equal (intersectp-equal (append a b) c) (or (intersectp-equal a c) (intersectp-equal b c))))
(defthm member-append-eq (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))
(defthm subsetp-cons-r (implies (subsetp-equal a b) (subsetp-equal a (cons x b))))
(defthm subsetp-true-list-fix-l (equal (subsetp-equal (true-list-fix a) b) (subsetp-equal a b)))
(defthm member-true-list-fix (iff (member-equal x (true-list-fix a)) (member-equal x a)))
(defthm subsetp-true-list-fix-r (equal (subsetp-equal a (true-list-fix b)) (subsetp-equal a b)))
(defthm strip-cars-true-list-fix (equal (strip-cars (true-list-fix l)) (strip-cars l)))
(defthm subsetp-refl (subsetp-equal x x))
(defthm subsetp-trans2 (implies (and (subsetp-equal a b) (subsetp-equal b c)) (subsetp-equal a c)))
(defthm member-subsetp2 (implies (and (subsetp-equal b c) (member-equal x b)) (member-equal x c)))

(defthm g-settle-cons
  (implies (consp cs)
           (equal (g-settle sss cs cnt locs used)
                  (if (g-stable (car cs))
                      (mv-let (e ss cs2 cnt locs) (g-settle (cdr sss) (cdr cs) cnt locs used)
                        (if e (mv e nil nil cnt locs) (mv nil (append (kar sss) ss) (cons (car cs) cs2) cnt locs)))
                    (if (car (g-fresh 'v :int64 cnt locs used)) (mv :name nil nil cnt locs)
                      (let ((tmp (g-tmp 'v (1+ (nfix cnt)))))
                        (mv-let (e ss cs2 cnt locs)
                          (g-settle (cdr sss) (cdr cs) (1+ (nfix cnt)) (cons (cons tmp :int64) (true-list-fix locs)) used)
                          (if e (mv e nil nil cnt locs)
                            (mv nil (append (kar sss) (list (list :assign (list :var tmp) (car cs))) ss)
                                (cons (list :var tmp) cs2) cnt locs))))))))
  :hints (("Goal" :in-theory (e/d (g-fresh) (g-tmp g-stable)) :expand ((g-settle sss cs cnt locs used)))))

(defthm g-settle-vs-cons
  (implies (consp cs)
           (equal (g-settle-vs sss cs cnt locs used)
                  (if (g-stable (car cs)) (g-settle-vs (cdr sss) (cdr cs) cnt locs used)
                    (if (car (g-fresh 'v :int64 cnt locs used)) (g-settle-vs (cdr sss) (cdr cs) cnt locs used)
                      (cons (g-tmp 'v (1+ (nfix cnt)))
                            (g-settle-vs (cdr sss) (cdr cs) (1+ (nfix cnt))
                                         (cons (cons (g-tmp 'v (1+ (nfix cnt))) :int64) (true-list-fix locs)) used))))))
  :hints (("Goal" :in-theory (e/d (g-fresh) (g-tmp g-stable)) :expand ((g-settle-vs sss cs cnt locs used)))))

(defthm g-settle-atom
  (implies (atom cs) (and (equal (g-settle sss cs cnt locs used) (list nil nil nil cnt locs))
                          (equal (g-settle-vs sss cs cnt locs used) nil)))
  :hints (("Goal" :expand ((g-settle sss cs cnt locs used) (g-settle-vs sss cs cnt locs used)))))

(defthm subsetp-app-cons
  (implies (subsetp-equal r (append f vr)) (subsetp-equal r (append f (cons v vr))))
  :hints (("Goal" :induct (len r))))

(defthm g-stable-var (g-stable (list :var x)))

(defmacro gset-thy () '(e/d (g-settle-cons g-settle-vs-cons g-settle-atom (:induction g-settle))
                            ((:definition g-settle) (:definition g-settle-vs) g-fresh g-tmp g-stable)))
(defmacro defgset (name term &rest more)
  `(defthm ,name ,term
     :hints (("Goal" :induct (g-settle sss cs cnt locs used) :in-theory (gset-thy)) ,@more)))

(defgset g-settle-locs (implies (not (gse 0)) (subsetp-equal locs (gse 4))))
(defthm g-settle-locs-cars
  (implies (and (not (gse 0)) (member-equal a (strip-cars locs))) (member-equal a (strip-cars (gse 4))))
  :hints (("Goal" :in-theory (disable g-settle subsetp-strip-cars)
           :use (g-settle-locs (:instance subsetp-strip-cars (a locs) (b (gse 4)))))))
(defgset g-settle-stables (stables (gse 2)))
(defgset g-settle-vs-in (implies (not (gse 0)) (subsetp-equal (gvs) (strip-cars (gse 4)))))
(defgset g-settle-vs-fresh
  (implies (not (gse 0)) (and (not (intersectp-equal (gvs) (strip-cars locs))) (not (intersectp-equal (gvs) used))))
  (and stable-under-simplificationp '(:use ((:instance g-fresh-out (b 'v) (ty :int64))))))
(defgset g-settle-asg
  (implies (not (gse 0)) (subsetp-equal (asg :list (gse 1)) (append (asg :list (g-flat sss)) (gvs)))))
(defthm g-settle-names
  (implies (not (gse 0)) (subsetp-equal (svs-names (gse 2)) (append (svs-names cs) (gvs))))
  :hints (("Goal" :induct (g-settle sss cs cnt locs used)
           :in-theory (e/d (g-settle-cons g-settle-vs-cons g-settle-atom (:induction g-settle) sv-names-var)
                           ((:definition g-settle) (:definition g-settle-vs) g-fresh g-tmp g-stable sv-names)))))

(defthm g-settle-static
  (implies (not (gse 0))
           (and (subsetp-equal (asg :list (gse 1)) (append (asg :list (g-flat sss)) (gvs)))
                (not (intersectp-equal (gvs) (strip-cars locs)))
                (not (intersectp-equal (gvs) used))
                (subsetp-equal (gvs) (strip-cars (gse 4)))
                (subsetp-equal locs (gse 4))
                (stables (gse 2))
                (subsetp-equal (svs-names (gse 2)) (append (svs-names cs) (gvs)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (g-settle-locs g-settle-stables g-settle-vs-in g-settle-vs-fresh g-settle-asg g-settle-names))))

; v_N, fresh at l, is not assigned by the rest of the settling when the
; arguments' statements assign only names of l
(defthm settle-v-not-asg
  (let ((v (g-tmp 'v (1+ (nfix c)))) (l2 (cons (cons (g-tmp 'v (1+ (nfix c))) :int64) (true-list-fix l))))
    (implies (and (not (car (g-settle sss cs (1+ (nfix c)) l2 used)))
                  (subsetp-equal (asg :list (g-flat sss)) (strip-cars l))
                  (not (member-equal v (strip-cars l))))
             (not (member-equal v (asg :list (mv-nth 1 (g-settle sss cs (1+ (nfix c)) l2 used)))))))
  :hints (("Goal" :in-theory (union-theories '(mv-nth-0-car) (theory 'minimal-theory))
           :use ((:instance g-settle-static (cnt (1+ (nfix c))) (locs (cons (cons (g-tmp 'v (1+ (nfix c))) :int64) (true-list-fix l))))
                 (:instance v-not-asg-abs (tr (mv-nth 1 (g-settle sss cs (1+ (nfix c)) (cons (cons (g-tmp 'v (1+ (nfix c))) :int64) (true-list-fix l)) used)))
                            (af (asg :list (g-flat sss)))
                            (vs (g-settle-vs sss cs (1+ (nfix c)) (cons (cons (g-tmp 'v (1+ (nfix c))) :int64) (true-list-fix l)) used))
                            (la l) (l2 l) (v (g-tmp 'v (1+ (nfix c)))) (ty :int64) (l2x (true-list-fix l)))
                 (:instance subsetp-refl (x l))))))

; ---- the settled arguments run

(defthm g-flat-sss
  (implies (not (car (g-sargs xs em cnt locs sigs fnames st)))
           (equal (g-flat (g-sss xs em cnt locs sigs fnames st)) (mv-nth 1 (g-sargs xs em cnt locs sigs fnames st))))
  :hints (("Goal" :induct (g-sss xs em cnt locs sigs fnames st) :in-theory (disable g-sexpr)
           :expand ((g-sargs xs em cnt locs sigs fnames st) (g-sss xs em cnt locs sigs fnames st)))))

(defthm obj-is-put-int
  (implies (and (obj-is o s fr heap) (equal (dty k fr) '(:int64))) (obj-is o s (put k (cons :int64 v) fr) heap))
  :hints (("Goal" :cases ((equal k o)) :in-theory (enable dty obj-is))))

(defthm decl-ok-member-dty
  (implies (and (decl-ok l fr) (member-equal (cons v ty) l)) (equal (dty v fr) (list ty)))
  :hints (("Goal" :induct (len l))))

(defthm svs-is-cons
  (equal (svs-is (cons c cs) ks fr heap)
         (and (consp ks) (not (car (sv c fr heap))) (equal (mv-nth 1 (sv c fr heap)) (car ks)) (svs-is cs (cdr ks) fr heap))))

; the glue, on plain variables: s1, then v = c1 (tmp) or nothing (stable), then the rest
(defthm settle-tmp-glue
  (let ((fr1 (mv-nth 1 (sx-list s1 fr heap))))
    (implies (and (equal (car (sx-list s1 fr heap)) :normal) (equal (mv-nth 2 (sx-list s1 fr heap)) heap)
                  (not (car (sv c1 fr1 heap))) (equal (mv-nth 1 (sv c1 fr1 heap)) k1) (int64p k1)
                  (equal (dty v fr1) '(:int64))
                  (equal (car (sx-list tr (put v (cons :int64 k1) fr1) heap)) :normal)
                  (equal (mv-nth 2 (sx-list tr (put v (cons :int64 k1) fr1) heap)) heap)
                  (svs-is cr ks (mv-nth 1 (sx-list tr (put v (cons :int64 k1) fr1) heap)) heap)
                  (not (member-equal v (asg :list tr))))
             (let ((r (sx-list (append s1 (list (list :assign (list :var v) c1)) tr) fr heap)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap)
                    (svs-is (cons (list :var v) cr) (cons k1 ks) (mv-nth 1 r) heap)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable sx sx-list sv stable-sv-after int64p dty member-subsetp asgv asg)
           :expand ((sx-list (cons (list :assign (list :var v) c1) tr) (mv-nth 1 (sx-list s1 fr heap)) heap))
           :use ((:instance stable-sv-after (c (list :var v)) (ss tr) (fr (put v (cons :int64 k1) (mv-nth 1 (sx-list s1 fr heap))))
                            (h2 heap))
                 (:instance asgv-subset-asg (flag :list) (x tr))
                 (:instance member-subsetp (x v) (b (asgv :list tr)) (c (asg :list tr)))
                 (:instance sx-list-append (a s1) (b (cons (list :assign (list :var v) c1) tr)))
                 (:instance sx-assign-run (tmp v) (ca c1) (fr (mv-nth 1 (sx-list s1 fr heap))))
                 (:instance sv-var-put (k v) (ty :int64) (v k1) (fr (mv-nth 1 (sx-list s1 fr heap))))))))

(defthm settle-stable-glue
  (let ((fr1 (mv-nth 1 (sx-list s1 fr heap))))
    (implies (and (equal (car (sx-list s1 fr heap)) :normal) (equal (mv-nth 2 (sx-list s1 fr heap)) heap)
                  (not (car (sv c1 fr1 heap))) (equal (mv-nth 1 (sv c1 fr1 heap)) k1) (g-stable c1)
                  (equal (car (sx-list tr fr1 heap)) :normal)
                  (equal (mv-nth 2 (sx-list tr fr1 heap)) heap)
                  (svs-is cr ks (mv-nth 1 (sx-list tr fr1 heap)) heap)
                  (not (intersectp-equal (sv-names c1) (asg :list tr))))
             (let ((r (sx-list (append s1 tr) fr heap)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap)
                    (svs-is (cons c1 cr) (cons k1 ks) (mv-nth 1 r) heap)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable sx sx-list sv stable-sv-after)
           :use ((:instance stable-sv-after (c c1) (ss tr) (fr (mv-nth 1 (sx-list s1 fr heap))) (h2 heap))
                 (:instance asgv-subset-asg (flag :list) (x tr))))))

(defun stu-sem (xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o)
  (mv-let (e ss cs ts cnta locsa) (g-sargs xs em cnt locs sigs fnames st)
    (declare (ignore ss cnta))
    (mv-let (e2 tt cs2 c3 l3) (g-settle (g-sss xs em cnt locs sigs fnames st) cs c2 l2 (append fnames (em-names em)))
      (declare (ignore c3))
      (mv-let (ae vs) (a-sx-list xs env s st defs n)
        (implies (and (not e) (not e2) (not ae) (all-int64-ty ts) (no-calls :list xs sigs nil) (em-ok em env fr)
                      (decl-ok l3 fr) (subsetp-equal locsa l2)
                      (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                      (st-ok st o s) (obj-is o s fr heap))
                 (mv-let (stt fr2 h2) (sx-list tt fr heap)
                   (and (equal stt :normal) (equal h2 heap) (svs-is cs2 vs fr2 heap))))))))

(defmacro used () '(append fnames (em-names em)))
(defmacro fl (k) `(mv-nth ,k (g-sargs xs em cnt locs sigs fnames st)))
(defmacro fs (k) `(mv-nth ,k (g-settle (g-sss xs em cnt locs sigs fnames st) (fl 2) c2 l2 (used))))
(defmacro u1 (k) `(mv-nth ,k (g-sexpr (car xs) em cnt locs sigs fnames st)))
(defmacro u2 (k) `(mv-nth ,k (g-sargs (cdr xs) em (u1 4) (u1 5) sigs fnames st)))
(defmacro usss () '(g-sss (cdr xs) em (u1 4) (u1 5) sigs fnames st))
(defmacro uv () '(g-tmp 'v (1+ (nfix c2))))
(defmacro ul2 () '(cons (cons (uv) :int64) (true-list-fix l2)))
(defmacro rs (k) `(mv-nth ,k (g-settle (usss) (u2 2) (1+ (nfix c2)) (ul2) (used))))
(defmacro rq (k) `(mv-nth ,k (g-settle (usss) (u2 2) c2 l2 (used))))
(defmacro uk1 () '(mv-nth 1 (a-sx (car xs) env s st defs (1- n))))
(defmacro uvs () '(mv-nth 1 (a-sx-list (cdr xs) env s st defs (1- n))))
(defmacro ufr1 () '(mv-nth 1 (sx-list (u1 1) fr heap)))
(defmacro ufrv () '(put (uv) (cons :int64 (uk1)) (ufr1)))

(defmacro stu-hyps ()
  '(and (not (fl 0)) (not (fs 0)) (not (car (a-sx-list xs env s st defs n))) (all-int64-ty (fl 3))
        (no-calls :list xs sigs nil) (em-ok em env fr) (decl-ok (fs 4) fr) (subsetp-equal (fl 5) l2)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (obj-is o s fr heap)))

(defthm stu-sem-use
  (implies (and (stu-sem xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o) (stu-hyps))
           (and (equal (car (sx-list (fs 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (fs 1) fr heap)) heap)
                (svs-is (fs 2) (mv-nth 1 (a-sx-list xs env s st defs n)) (mv-nth 1 (sx-list (fs 1) fr heap)) heap)))
  :hints (("Goal" :in-theory (e/d (stu-sem) (g-sargs g-settle g-sss a-sx-list sx-list svs-is no-calls em-ok decl-ok st-ok obj-is)))))

(in-theory (disable stu-sem))

(defthm stu-nil
  (implies (atom xs) (stu-sem xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (enable stu-sem)
           :expand ((g-sargs xs em cnt locs sigs fnames st) (g-sss xs em cnt locs sigs fnames st)
                    (g-settle nil nil c2 l2 (used)) (sx-list nil fr heap) (a-sx-list xs env s st defs n)))))

(defthm stu-ashape
  (implies (and (consp xs) (not (car (a-sx-list xs env s st defs n))))
           (and (not (zp n)) (not (car (a-sx (car xs) env s st defs (1- n))))
                (not (car (a-sx-list (cdr xs) env s st defs (1- n))))
                (equal (mv-nth 1 (a-sx-list xs env s st defs n)) (cons (uk1) (uvs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((a-sx-list xs env s st defs n)) :in-theory (disable a-sx))))

(defthm stu-shape-tmp
  (implies (and (consp xs) (not (fl 0)) (not (fs 0)) (not (g-stable (u1 2))))
           (and (not (u1 0)) (not (u2 0))
                (equal (fl 2) (cons (u1 2) (u2 2))) (equal (fl 3) (cons (u1 3) (u2 3))) (equal (fl 5) (u2 5))
                (not (car (g-fresh 'v :int64 c2 l2 (used))))
                (not (rs 0))
                (equal (fs 1) (append (u1 1) (list (list :assign (list :var (uv)) (u1 2))) (rs 1)))
                (equal (fs 2) (cons (list :var (uv)) (rs 2)))
                (equal (fs 4) (rs 4))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable g-sexpr g-sargs g-settle g-fresh g-stable g-tmp g-sss)
           :expand ((g-sargs xs em cnt locs sigs fnames st) (g-sss xs em cnt locs sigs fnames st)
                    (:free (a b c d) (g-settle (cons a b) (cons c d) c2 l2 (used))))
           :use ((:instance g-fresh-out (b 'v) (ty :int64) (cnt c2) (locs l2) (used (used)))))))

(defthm stu-shape-stable
  (implies (and (consp xs) (not (fl 0)) (not (fs 0)) (g-stable (u1 2)))
           (and (not (u1 0)) (not (u2 0))
                (equal (fl 2) (cons (u1 2) (u2 2))) (equal (fl 3) (cons (u1 3) (u2 3))) (equal (fl 5) (u2 5))
                (not (rq 0))
                (equal (fs 1) (append (u1 1) (rq 1)))
                (equal (fs 2) (cons (u1 2) (rq 2)))
                (equal (fs 4) (rq 4))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable g-sexpr g-sargs g-settle g-fresh g-stable g-tmp g-sss)
           :expand ((g-sargs xs em cnt locs sigs fnames st) (g-sss xs em cnt locs sigs fnames st)
                    (:free (a b c d) (g-settle (cons a b) (cons c d) c2 l2 (used)))))))


; ---- the step: the first argument, then the rest at its frame.
; The case's context is a disabled predicate; each fact lemma uses the
; earlier ones (whose hypothesis is the same predicate, so nothing splits)
; plus one or two outside lemmas, in the minimal theory.

(defmacro mthy (&rest rules) `(union-theories '(mv-nth-0-car ,@rules) (set-difference-theories (theory 'minimal-theory) '(mv-nth))))

(defun-nx stu-tctx (xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o)
  (and (consp xs) (not (g-stable (u1 2))) (stu-hyps) (sn-hyps) (em-nostobj em st)))
(defun-nx stu-sctx (xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o)
  (and (consp xs) (g-stable (u1 2)) (stu-hyps) (sn-hyps) (em-nostobj em st)))
(in-theory (disable stu-tctx stu-sctx))

(defmacro tctx () '(stu-tctx xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o))
(defmacro sctx () '(stu-sctx xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o))

(defthm stu-t0
  (implies (tctx) (and (consp xs) (not (g-stable (u1 2))) (stu-hyps) (sn-hyps) (em-nostobj em st)))
  :rule-classes nil :hints (("Goal" :in-theory (mthy stu-tctx))))
(defthm stu-s0
  (implies (sctx) (and (consp xs) (g-stable (u1 2)) (stu-hyps) (sn-hyps) (em-nostobj em st)))
  :rule-classes nil :hints (("Goal" :in-theory (mthy stu-sctx))))

(defthm stu-ta
  (implies (tctx)
           (and (not (u1 0)) (not (u2 0)) (not (rs 0)) (not (zp n))
                (not (car (a-sx (car xs) env s st defs (1- n)))) (not (car (a-sx-list (cdr xs) env s st defs (1- n))))
                (all-int64-ty (u2 3)) (equal (u1 3) :int64)
                (no-calls :term (car xs) sigs nil) (no-calls :list (cdr xs) sigs nil)
                (equal (fs 4) (rs 4)) (equal (fl 5) (u2 5)) (not (car (g-fresh 'v :int64 c2 l2 (used))))
                (equal (fs 1) (append (u1 1) (list (list :assign (list :var (uv)) (u1 2))) (rs 1)))
                (equal (fs 2) (cons (list :var (uv)) (rs 2)))
                (equal (mv-nth 1 (a-sx-list xs env s st defs n)) (cons (uk1) (uvs)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy all-int64-ty car-cons cdr-cons)
           :use (stu-t0 stu-shape-tmp stu-ashape (:instance no-calls-cons (cs nil))))))

(defthm stu-ta-eq
  (implies (tctx)
           (and (equal (fs 4) (rs 4)) (equal (fl 5) (u2 5)) (equal (u1 3) :int64)
                (equal (fs 1) (append (u1 1) (list (list :assign (list :var (uv)) (u1 2))) (rs 1)))
                (equal (fs 2) (cons (list :var (uv)) (rs 2)))
                (equal (mv-nth 1 (a-sx-list xs env s st defs n)) (cons (uk1) (uvs)))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy) :use stu-ta)))

(defthm stu-sa
  (implies (sctx)
           (and (not (u1 0)) (not (u2 0)) (not (rq 0)) (not (zp n))
                (not (car (a-sx (car xs) env s st defs (1- n)))) (not (car (a-sx-list (cdr xs) env s st defs (1- n))))
                (all-int64-ty (u2 3)) (equal (u1 3) :int64)
                (no-calls :term (car xs) sigs nil) (no-calls :list (cdr xs) sigs nil)
                (equal (fs 4) (rq 4)) (equal (fl 5) (u2 5))
                (equal (fs 1) (append (u1 1) (rq 1)))
                (equal (fs 2) (cons (u1 2) (rq 2)))
                (equal (mv-nth 1 (a-sx-list xs env s st defs n)) (cons (uk1) (uvs)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy all-int64-ty car-cons cdr-cons)
           :use (stu-s0 stu-shape-stable stu-ashape (:instance no-calls-cons (cs nil))))))

(defthm stu-sa-eq
  (implies (sctx)
           (and (equal (fs 4) (rq 4)) (equal (fl 5) (u2 5)) (equal (u1 3) :int64)
                (equal (fs 1) (append (u1 1) (rq 1)))
                (equal (fs 2) (cons (u1 2) (rq 2)))
                (equal (mv-nth 1 (a-sx-list xs env s st defs n)) (cons (uk1) (uvs)))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy) :use stu-sa)))
(in-theory (disable stu-ta-eq stu-sa-eq))

(defthm stu-tsn
  (implies (tctx) (and (sn-ok (car xs) em cnt locs sigs fnames st) (sna-ok (cdr xs) em (u1 4) (u1 5) sigs fnames st)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-ta-eq) :use (stu-t0 stu-ta (:instance sn-ok-holds (x (car xs)))
                                           (:instance sna-ok-holds (xs (cdr xs)) (cnt (u1 4)) (locs (u1 5)))))))
(defthm stu-ssn
  (implies (sctx) (and (sn-ok (car xs) em cnt locs sigs fnames st) (sna-ok (cdr xs) em (u1 4) (u1 5) sigs fnames st)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-sa-eq) :use (stu-s0 stu-sa (:instance sn-ok-holds (x (car xs)))
                                           (:instance sna-ok-holds (xs (cdr xs)) (cnt (u1 4)) (locs (u1 5)))))))

(defmacro set-rules () ''(mv-nth-0-car subsetp-trans2 subsetp-cons-r subsetp-true-list-fix-r member-subsetp2 member-append-eq subsetp-refl
                          car-cons cdr-cons member-equal strip-cars))

(defthm stu-tb
  (implies (tctx)
           (and (subsetp-equal (u1 5) (fs 4)) (subsetp-equal (u2 5) (ul2)) (member-equal (cons (uv) :int64) (rs 4))
                (not (member-equal (uv) (strip-cars l2))) (not (member-equal (uv) (em-names em)))
                (not (intersectp-equal (asg :list (u1 1)) (em-names em)))
                (not (member-equal (uv) (asg :list (rs 1))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (union-theories (list* 'stu-ta-eq 'g-flat-sss (set-rules)) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (stu-t0 stu-ta stu-tsn
                 (:instance sn-ok-use (x (car xs)))
                 (:instance sna-ok-use (xs (cdr xs)) (cnt (u1 4)) (locs (u1 5)))
                 (:instance g-settle-static (sss (g-sss xs em cnt locs sigs fnames st)) (cs (fl 2)) (cnt c2) (locs l2) (used (used)))
                 (:instance g-settle-static (sss (usss)) (cs (u2 2)) (cnt (1+ (nfix c2))) (locs (ul2)) (used (used)))
                 (:instance g-fresh-out (b 'v) (ty :int64) (cnt c2) (locs l2) (used (used)))
                 (:instance g-flat-sss (xs (cdr xs)) (cnt (u1 4)) (locs (u1 5)))
                 (:instance settle-v-not-asg (sss (usss)) (cs (u2 2)) (c c2) (l l2) (used (used)))
                 (:instance subsetp-strip-cars (a (u2 5)) (b l2))))))

(defthm stu-sb
  (implies (sctx)
           (and (subsetp-equal (u1 5) (fs 4)) (subsetp-equal (u2 5) l2)
                (not (intersectp-equal (asg :list (u1 1)) (em-names em)))
                (not (intersectp-equal (sv-names (u1 2)) (asg :list (rq 1))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (union-theories (list* 'stu-sa-eq 'g-flat-sss (set-rules)) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (stu-s0 stu-sa stu-ssn
                 (:instance sn-ok-use (x (car xs)))
                 (:instance sna-ok-use (xs (cdr xs)) (cnt (u1 4)) (locs (u1 5)))
                 (:instance g-settle-static (sss (g-sss xs em cnt locs sigs fnames st)) (cs (fl 2)) (cnt c2) (locs l2) (used (used)))
                 (:instance g-settle-static (sss (usss)) (cs (u2 2)) (cnt c2) (locs l2) (used (used)))
                 (:instance g-flat-sss (xs (cdr xs)) (cnt (u1 4)) (locs (u1 5)))
                 (:instance stable-not-asg-abs (nm (sv-names (u1 2))) (f fnames) (e (em-names em)) (l1 (u1 5))
                            (a (asg :list (rq 1))) (af (asg :list (u2 1))) (vs (g-settle-vs (usss) (u2 2) c2 l2 (used))))))))

; the first argument's statements and code
(defmacro first-run ()
  '(and (equal (car (sx-list (u1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (u1 1) fr heap)) heap)
        (not (car (sv (u1 2) (ufr1) heap))) (equal (mv-nth 1 (sv (u1 2) (ufr1) heap)) (uk1)) (int64p (uk1))))

(defthm stu-tc
  (implies (tctx) (first-run))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-ta-eq scalar-ok obj-at-is)
           :use (stu-t0 stu-ta stu-tb
                 (:instance gs-sem-holds (x (car xs)) (n (1- n)))
                 (:instance gs-sem-use (x (car xs)) (n (1- n)))
                 (:instance decl-ok-subset (a (u1 5)) (b (fs 4)))))))
(defthm stu-sc
  (implies (sctx) (first-run))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-sa-eq scalar-ok obj-at-is)
           :use (stu-s0 stu-sa stu-sb
                 (:instance gs-sem-holds (x (car xs)) (n (1- n)))
                 (:instance gs-sem-use (x (car xs)) (n (1- n)))
                 (:instance decl-ok-subset (a (u1 5)) (b (fs 4)))))))

; the frame the rest starts from
(defthm stu-td
  (implies (tctx)
           (and (equal (dty (uv) (ufr1)) '(:int64))
                (em-ok em env (ufrv)) (decl-ok (rs 4) (ufrv)) (obj-is o s (ufrv) heap)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-ta-eq decl-ok-after-sx)
           :use (stu-t0 stu-ta stu-tb stu-tc
                 (:instance decl-ok-member-dty (l (rs 4)) (fr (ufr1)) (v (uv)) (ty :int64))
                 (:instance em-ok-after-sx (s (u1 1)))
                 (:instance em-ok-put (fr (ufr1)) (k (uv)) (v (cons :int64 (uk1))))
                 (:instance decl-ok-put-int (locs (rs 4)) (fr (ufr1)) (k (uv)) (v (uk1)))
                 (:instance obj-is-after-sx (ss (u1 1)))
                 (:instance obj-is-put-int (fr (ufr1)) (k (uv)) (v (uk1)))))))
(defthm stu-sd
  (implies (sctx) (and (em-ok em env (ufr1)) (decl-ok (rq 4) (ufr1)) (obj-is o s (ufr1) heap)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-sa-eq decl-ok-after-sx)
           :use (stu-s0 stu-sa stu-sb
                 (:instance em-ok-after-sx (s (u1 1)))
                 (:instance obj-is-after-sx (ss (u1 1)))))))


(defmacro stu-concl ()
  '(and (equal (car (sx-list (fs 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (fs 1) fr heap)) heap)
        (svs-is (fs 2) (mv-nth 1 (a-sx-list xs env s st defs n)) (mv-nth 1 (sx-list (fs 1) fr heap)) heap)))
(defthm stu-sem-intro
  (implies (implies (stu-hyps) (stu-concl)) (stu-sem xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (e/d (stu-sem) (g-sargs g-settle g-sss a-sx-list sx-list svs-is no-calls em-ok decl-ok st-ok obj-is)))))



(defthm stu-tmp-core
  (implies (and (tctx)
                (stu-sem (cdr xs) em (u1 4) (u1 5) (1+ (nfix c2)) (ul2) sigs fnames st env s defs (1- n) (ufrv) heap o))
           (stu-concl))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-ta-eq)
           :use (stu-t0 stu-ta stu-tb stu-tc stu-td
                 (:instance stu-sem-use (xs (cdr xs)) (cnt (u1 4)) (locs (u1 5)) (c2 (1+ (nfix c2))) (l2 (ul2))
                            (n (1- n)) (fr (ufrv)))
                 (:instance settle-tmp-glue (s1 (u1 1)) (c1 (u1 2)) (k1 (uk1)) (v (uv)) (tr (rs 1)) (cr (rs 2)) (ks (uvs)))))))

(defthm stu-stable-core
  (implies (and (sctx)
                (stu-sem (cdr xs) em (u1 4) (u1 5) c2 l2 sigs fnames st env s defs (1- n) (ufr1) heap o))
           (stu-concl))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-sa-eq)
           :use (stu-s0 stu-sa stu-sb stu-sc stu-sd
                 (:instance stu-sem-use (xs (cdr xs)) (cnt (u1 4)) (locs (u1 5)) (n (1- n)) (fr (ufr1)))
                 (:instance settle-stable-glue (s1 (u1 1)) (c1 (u1 2)) (k1 (uk1)) (tr (rq 1)) (cr (rq 2)) (ks (uvs)))))))

(defthm stu-tmp
  (implies (and (consp xs) (not (g-stable (u1 2))) (sn-hyps) (em-nostobj em st)
                (stu-sem (cdr xs) em (u1 4) (u1 5) (1+ (nfix c2)) (ul2) sigs fnames st env s defs (1- n) (ufrv) heap o))
           (stu-sem xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-tctx)
           :use (stu-tmp-core stu-sem-intro))))

(defthm stu-stable
  (implies (and (consp xs) (g-stable (u1 2)) (sn-hyps) (em-nostobj em st)
                (stu-sem (cdr xs) em (u1 4) (u1 5) c2 l2 sigs fnames st env s defs (1- n) (ufr1) heap o))
           (stu-sem xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (mthy stu-sctx)
           :use (stu-stable-core stu-sem-intro))))


(defun-nx stu-ind (xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap)
  (declare (xargs :measure (acl2-count xs)))
  (if (atom xs) t
    (mv-let (e s1 c1 ty cnt1 locs1) (g-sexpr (car xs) em cnt locs sigs fnames st)
      (declare (ignore e ty))
      (if (g-stable c1)
          (stu-ind (cdr xs) em cnt1 locs1 c2 l2 sigs fnames st env s defs (1- n) (mv-nth 1 (sx-list s1 fr heap)) heap)
        (stu-ind (cdr xs) em cnt1 locs1 (1+ (nfix c2)) (cons (cons (g-tmp 'v (1+ (nfix c2))) :int64) (true-list-fix l2))
                 sigs fnames st env s defs (1- n)
                 (put (g-tmp 'v (1+ (nfix c2))) (cons :int64 (mv-nth 1 (a-sx (car xs) env s st defs (1- n))))
                      (mv-nth 1 (sx-list s1 fr heap)))
                 heap)))))

(defthm stu-thm
  (implies (and (sn-hyps) (em-nostobj em st))
           (stu-sem xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :induct (stu-ind xs em cnt locs c2 l2 sigs fnames st env s defs n fr heap)
           :in-theory (union-theories '(stu-ind stu-nil stu-tmp stu-stable) (theory 'minimal-theory)))))

; ---- the CALL with updated stobj arguments

; the source: the values on S, the updates threaded from S, then the oracle
(defun a-stcall-u (x env s st defs n)
  (mv-let (e ks) (a-sx-list (g-cvals (g-obj (car x) st) (cdr x) st) env s st defs n)
    (if e (mv e s nil)
      (mv-let (e s1) (a-sacts (g-obj (car x) st) (cdr x) env s st defs n)
        (if e (mv e s nil) (a-call-val (car x) ks s1))))))

(defmacro cu-s (k) `(mv-nth ,k (g-settle (g-sss (cvs) em cnt locs sigs fnames st) (gca 2) (gca 4) (gca 5) (used))))
(defmacro cu-a (k) `(mv-nth ,k (g-sacts (g-obj (car x) st) (cdr x) em (cu-s 3) (cu-s 4) sigs fnames st)))
(defmacro cu-call () '(list :call (g-sym (car x) nil) (append (g-scs (g-obj (car x) st) (cdr x) st) (cu-s 2))))

(defthm g-settle-true-list (true-listp (mv-nth 2 (g-settle sss cs cnt locs used)))
  :hints (("Goal" :induct (g-settle sss cs cnt locs used) :in-theory (disable g-fresh g-stable)
           :expand ((g-settle sss cs cnt locs used)))))


(defthm callu-shape
  (implies (and (not (car (g-callst x em cnt locs sigs fnames st nil))) (g-upd (g-obj (car x) st) (cdr x) st))
           (and (consp x) (true-listp x) (equal (len (g-obj (car x) st)) (len (cdr x)))
                (not (car (g-sargs (cvs) em cnt locs sigs fnames st))) (all-int64-ty (gca 3))
                (not (cu-s 0)) (not (cu-a 0))
                (equal (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) (append (cu-s 1) (cu-a 1) (list (cu-call))))
                (equal (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) (cu-a 3))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-sargs g-scall-args g-settle g-sacts g-scall-args-is-g-sargs g-scall-args-sss g-cvals g-scs g-upd
                               g-sss)
           :expand ((g-callst x em cnt locs sigs fnames st nil))
           :use ((:instance g-callst-ok (dests nil))
                 (:instance g-scall-args-is-g-sargs (formals (g-obj (car x) st)) (xs (cdr x)))
                 (:instance g-scall-args-sss (formals (g-obj (car x) st)) (xs (cdr x)))))))

; settled codes keep their values past statements assigning none of their names
(defthm svs-is-after
  (implies (and (stables cs) (svs-is cs ks fr heap) (not (intersectp-equal (svs-names cs) (asgv :list ss))))
           (svs-is cs ks (mv-nth 1 (sx-list ss fr heap)) h2))
  :hints (("Goal" :induct (svs-is cs ks fr heap) :in-theory (disable sv sx-list g-stable))))

(defthm callu-glue
  (implies (and (equal (car (sx-list a fr heap)) :normal) (equal (mv-nth 2 (sx-list a fr heap)) heap)
                (equal (car (sx-list b (mv-nth 1 (sx-list a fr heap)) heap)) :normal)
                (equal (kar c) :call)
                (equal (s-call-val (kadr c) (kaddr c) (mv-nth 1 (sx-list b (mv-nth 1 (sx-list a fr heap)) heap))
                                   (mv-nth 2 (sx-list b (mv-nth 1 (sx-list a fr heap)) heap)))
                       (list nil fr3 h3)))
           (equal (sxc-list (append a b (list c)) fr heap) (list :normal fr3 h3)))
  :hints (("Goal" :in-theory (disable sx-list sxc-list sxc-list-one-call)
           :use ((:instance sxc-list-append-sx (b (append b (list c))))
                 (:instance sxc-list-append-sx (a b) (b (list c)) (fr (mv-nth 1 (sx-list a fr heap))))
                 (:instance sxc-list-one-call (fr (mv-nth 1 (sx-list b (mv-nth 1 (sx-list a fr heap)) heap)))
                            (heap (mv-nth 2 (sx-list b (mv-nth 1 (sx-list a fr heap)) heap))))))))


(defthm no-calls-cvals
  (implies (no-calls :list xs sigs cs) (no-calls :list (g-cvals formals xs st) sigs cs))
  :hints (("Goal" :induct (g-cvals formals xs st) :in-theory (disable g-role)
           :expand ((no-calls :list xs sigs cs) (:free (a b) (no-calls :list (cons a b) sigs cs))))))

(defthm em-disj-abs
  (implies (and (subsetp-equal a (append b c)) (not (intersectp-equal b e)) (not (intersectp-equal c (append f e))))
           (not (intersectp-equal a e)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance disj-subsets (x a) (p (append b c)) (y e) (q e))))))

(defthm subsetp-append-mono (implies (subsetp-equal a b) (subsetp-equal (append c a) (append c b))))

(defthm codes-disj-abs
  (implies (and (subsetp-equal n2 (append n1 vs)) (subsetp-equal n1 (append f e (strip-cars la)))
                (subsetp-equal vs (strip-cars l)) (subsetp-equal la l)
                (not (intersectp-equal a (append f e (strip-cars l)))))
           (not (intersectp-equal n2 a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable disj-subsets subsetp-strip-cars)
           :use ((:instance disj-subsets (x n2) (p (append f e (strip-cars l))) (y a) (q a))
                 (:instance intersectp-comm (a a) (b (append f e (strip-cars l))))
                 (:instance subsetp-strip-cars (a la) (b l))
                 (:instance subsetp-trans2 (a n2) (b (append n1 vs)) (c (append f e (strip-cars l))))
                 (:instance subsetp-trans2 (a n1) (b (append f e (strip-cars la))) (c (append f e (strip-cars l))))))))

(defmacro cuks () '(mv-nth 1 (a-sx-list (cvs) env s st defs n)))
(defmacro cus1 () '(mv-nth 1 (a-sacts (g-obj (car x) st) (cdr x) env s st defs n)))
(defmacro cufr1 () '(mv-nth 1 (sx-list (cu-s 1) fr heap)))
(defmacro cufr2 () '(mv-nth 1 (sx-list (cu-a 1) (cufr1) heap)))
(defmacro cuh2 () '(put (okey o fr) (cus1) heap))

(defthm a-stcall-u-parts
  (implies (not (car (a-stcall-u x env s st defs n)))
           (and (not (car (a-sx-list (cvs) env s st defs n)))
                (not (car (a-sacts (g-obj (car x) st) (cdr x) env s st defs n)))
                (not (car (a-call-val (car x) (cuks) (cus1))))
                (equal (mv-nth 1 (a-stcall-u x env s st defs n)) (mv-nth 1 (a-call-val (car x) (cuks) (cus1))))))
  :rule-classes nil)

(defmacro callu-hyps ()
  '(and (eq (g-role (car x) st) :sub) (g-upd (g-obj (car x) st) (cdr x) st)
        (not (car (g-callst x em cnt locs sigs fnames st nil)))
        (not (car (a-stcall-u x env s st defs n))) (c-sorc o st) (a-call-ok st o)
        (no-calls :list (cdr x) sigs nil) (em-ok em env fr)
        (decl-ok (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
        (gsc-sem (g-obj (car x) st) (cdr x) em (cu-s 3) (cu-s 4) sigs fnames st env s defs n (cufr1) heap o)
        (stan-ok (g-obj (car x) st) (cdr x) em (cu-s 3) (cu-s 4) sigs fnames st)))


(defun-nx cu-ctxp (x em cnt locs sigs fnames st env s defs n fr heap o) (callu-hyps))
(in-theory (disable cu-ctxp))
(defmacro cuctx () '(cu-ctxp x em cnt locs sigs fnames st env s defs n fr heap o))

(defthm cu-0 (implies (cuctx) (callu-hyps)) :rule-classes nil :hints (("Goal" :in-theory (mthy cu-ctxp))))

(defthm cu-shape
  (implies (cuctx)
           (and (consp x) (true-listp x) (equal (len (g-obj (car x) st)) (len (cdr x)))
                (not (car (g-sargs (cvs) em cnt locs sigs fnames st))) (all-int64-ty (gca 3))
                (not (cu-s 0)) (not (cu-a 0)) (no-calls :list (cvs) sigs nil)
                (not (car (a-sx-list (cvs) env s st defs n)))
                (not (car (a-sacts (g-obj (car x) st) (cdr x) env s st defs n)))
                (not (car (a-call-val (car x) (cuks) (cus1))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy)
           :use (cu-0 callu-shape a-stcall-u-parts (:instance no-calls-cvals (formals (g-obj (car x) st)) (xs (cdr x)) (cs nil))))))

(defthm cu-eq
  (implies (cuctx)
           (and (equal (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) (append (cu-s 1) (cu-a 1) (list (cu-call))))
                (equal (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) (cu-a 3))
                (equal (mv-nth 1 (a-stcall-u x env s st defs n)) (mv-nth 1 (a-call-val (car x) (cuks) (cus1))))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy) :use (cu-0 callu-shape a-stcall-u-parts))))
(in-theory (disable cu-eq))

(defthm cu-stat1
  (implies (cuctx)
           (and (sna-ok (cvs) em cnt locs sigs fnames st)
                (subsetp-equal (gca 5) (cu-s 4)) (decl-ok (cu-s 4) fr) (decl-ok (gca 5) fr)
                (not (intersectp-equal (asg :list (cu-s 1)) (em-names em)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy cu-eq g-flat-sss)
           :use (cu-0 cu-shape
                 (:instance sna-ok-holds (xs (cvs)))
                 (:instance sna-ok-use (xs (cvs)))
                 (:instance stan-ok-use (vars (g-obj (car x) st)) (xs (cdr x)) (cnt (cu-s 3)) (locs (cu-s 4)))
                 (:instance g-settle-static (sss (g-sss (cvs) em cnt locs sigs fnames st)) (cs (gca 2)) (cnt (gca 4))
                            (locs (gca 5)) (used (used)))
                 (:instance decl-ok-subset (a (cu-s 4)) (b (cu-a 3)))
                 (:instance decl-ok-subset (a (gca 5)) (b (cu-s 4)))
                 (:instance em-disj-abs (a (asg :list (cu-s 1))) (b (asg :list (gca 1)))
                            (c (g-settle-vs (g-sss (cvs) em cnt locs sigs fnames st) (gca 2) (gca 4) (gca 5) (used)))
                            (f fnames) (e (em-names em)))))))

(defthm cu-stat2
  (implies (cuctx)
           (and (stables (cu-s 2)) (not (intersectp-equal (svs-names (cu-s 2)) (asgv :list (cu-a 1))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy)
           :use (cu-0 cu-shape cu-stat1
                 (:instance sna-ok-use (xs (cvs)))
                 (:instance stan-ok-use (vars (g-obj (car x) st)) (xs (cdr x)) (cnt (cu-s 3)) (locs (cu-s 4)))
                 (:instance g-settle-static (sss (g-sss (cvs) em cnt locs sigs fnames st)) (cs (gca 2)) (cnt (gca 4))
                            (locs (gca 5)) (used (used)))
                 (:instance codes-disj-abs (n2 (svs-names (cu-s 2))) (n1 (svs-names (gca 2)))
                            (vs (g-settle-vs (g-sss (cvs) em cnt locs sigs fnames st) (gca 2) (gca 4) (gca 5) (used)))
                            (f fnames) (e (em-names em)) (la (gca 5)) (l (cu-s 4)) (a (asgv :list (cu-a 1))))))))

; the settled arguments run, then the frame for the updates
(defthm cu-run1
  (implies (cuctx)
           (and (equal (car (sx-list (cu-s 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (cu-s 1) fr heap)) heap)
                (svs-is (cu-s 2) (cuks) (cufr1) heap) (int64s (cuks))
                (em-ok em env (cufr1)) (decl-ok (cu-a 3) (cufr1)) (obj-at o s (cufr1) heap)
                (equal (okey o (cufr1)) (okey o fr))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy cu-eq decl-ok-after-sx subsetp-refl obj-at-is)
           :use (cu-0 cu-shape cu-stat1
                 (:instance stu-thm (xs (cvs)) (c2 (gca 4)) (l2 (gca 5)))
                 (:instance stu-sem-use (xs (cvs)) (c2 (gca 4)) (l2 (gca 5)))
                 (:instance callst-args-run (xs (cvs)))
                 (:instance em-ok-after-sx (s (cu-s 1)))
                 (:instance obj-at-after-same (ss (cu-s 1)))))))

; the updates run, the codes still answer, the object at S1
(defthm cu-run2
  (implies (cuctx)
           (and (equal (car (sx-list (cu-a 1) (cufr1) heap)) :normal)
                (equal (mv-nth 2 (sx-list (cu-a 1) (cufr1) heap)) (cuh2))
                (st-ok st o (cus1)) (st-wf st (cus1))
                (svs-is (cu-s 2) (cuks) (cufr2) (cuh2))
                (obj-at o (cus1) (cufr2) (cuh2))
                (equal (okey o (cufr2)) (okey o fr))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy cu-eq)
           :use (cu-0 cu-shape cu-stat2 cu-run1
                 (:instance gsc-sem-use (vars (g-obj (car x) st)) (xs (cdr x)) (cnt (cu-s 3)) (locs (cu-s 4)) (fr (cufr1)))
                 (:instance svs-is-after (cs (cu-s 2)) (ks (cuks)) (fr (cufr1)) (ss (cu-a 1)) (h2 (cuh2)))
                 (:instance obj-at-after (fr (cufr1)) (ss (cu-a 1)) (s2 (cus1)))
                 (:instance obj-at-cadr (fr (cufr1)))
                 (:instance okey-after (fr (cufr1)) (ss (cu-a 1)))))))

(defthm put-put-okey
  (implies (equal k1 k) (equal (put k1 v (put k w h)) (put k v h)))
  :rule-classes nil)

(defthm gst-callst-u-core
  (implies (cuctx)
           (and (equal (car (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap)) :normal)
                (equal (mv-nth 2 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap))
                       (put (okey o fr) (mv-nth 1 (a-stcall-u x env s st defs n)) heap))
                (st-ok st o (mv-nth 1 (a-stcall-u x env s st defs n)))
                (st-wf st (mv-nth 1 (a-stcall-u x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy cu-eq kar kdr kadr kaddr car-cons cdr-cons mv-nth-cons-k (equal) (consp)
                                                    (posp) (binary-+) (unary--))
           :use (cu-0 cu-shape cu-run1 cu-run2
                 (:instance c-sorc-necc (f (car x)) (xs (cdr x)) (cs (cu-s 2)) (fr (cufr2)) (heap (cuh2)) (ks (cuks)) (s (cus1)))
                 (:instance a-call-ok-necc (f (car x)) (ks (cuks)) (s (cus1)))
                 (:instance callu-glue (a (cu-s 1)) (b (cu-a 1)) (c (cu-call)) (fr3 (cufr2))
                            (h3 (put (okey o (cufr2)) (mv-nth 1 (a-call-val (car x) (cuks) (cus1))) (cuh2))))
                 (:instance put-put-okey (k1 (okey o (cufr2))) (k (okey o fr)) (v (mv-nth 1 (a-call-val (car x) (cuks) (cus1))))
                            (w (cus1)) (h heap))))))

(defthm gst-callst-u
  (implies (callu-hyps)
           (and (equal (car (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap)) :normal)
                (equal (mv-nth 2 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap))
                       (put (okey o fr) (mv-nth 1 (a-stcall-u x env s st defs n)) heap))
                (st-ok st o (mv-nth 1 (a-stcall-u x env s st defs n)))
                (st-wf st (mv-nth 1 (a-stcall-u x env s st defs n)))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy cu-ctxp) :use gst-callst-u-core)))
