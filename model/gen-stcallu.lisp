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

(include-book "gen-stsettle")

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
