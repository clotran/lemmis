; gen-stst: g-stmt against a-st on sx-list (GEN.md "What remains" 4 (a),
; step (2)), on acl2-fortran's fixed `stmt` (clotran 23ca95ac): a field
; update, an element update (and its :bounds), if, a lambda -- with no side
; condition on what the value reads (the three findings are fixed).
;
; A statement's frame changes only at the variables it assigns (asgv: asg
; less the objects a component or element assignment names); its heap only
; at the stobj's object, which is put to a-st's S'.

(in-package "ACL2")

(include-book "gen-stthm")

; ---- asgv: the variables a statement list assigns

(defun asgv (flag x)
  (declare (xargs :measure (acl2-count x)))
  (cond ((atom x) nil)
        ((eq flag :arms) (append (asgv :list (kadr (car x))) (asgv :arms (cdr x))))
        (t (append (let ((s (car x)))
                     (case (kar s)
                       (:assign (if (eq (kar (kadr s)) :var) (list (kadr (kadr s))) nil))
                       (:if (append (asgv :list (kaddr s)) (asgv :list (kadddr s))))
                       (:select (append (asgv :arms (kaddr s)) (asgv :list (kadddr s))))
                       (otherwise nil)))
                   (asgv :list (cdr x))))))

(defthm asgv-subset-asg (subsetp-equal (asgv flag x) (asg flag x)))

(defthm asgv-append (equal (asgv :list (append a b)) (append (asgv :list a) (asgv :list b))))

(defthm member-asgv-lkp-arm
  (implies (not (member-equal n (asgv :arms arms))) (not (member-equal n (asgv :list (kadr (lkp k arms))))))
  :hints (("Goal" :induct (len arms) :expand ((lkp k arms) (asgv :arms arms)))))

(defun skv-stmt (n s fr heap)
  (mv-let (st fr2 h2) (sx s fr heap)
    (declare (ignore st h2))
    (implies (not (member-equal n (asgv :list (list s)))) (equal (lkp n fr2) (lkp n fr)))))

(defun skv-list (n ss fr heap)
  (mv-let (st fr2 h2) (sx-list ss fr heap)
    (declare (ignore st h2))
    (implies (not (member-equal n (asgv :list ss))) (equal (lkp n fr2) (lkp n fr)))))

(defthm skv-assign
  (implies (eq (kar s) :assign) (skv-stmt n s fr heap))
  :hints (("Goal" :expand ((sx s fr heap) (asgv :list (list s))))))

(defthm skv-if
  (implies (and (eq (kar s) :if) (skv-list n (kaddr s) fr heap) (skv-list n (kadddr s) fr heap))
           (skv-stmt n s fr heap))
  :hints (("Goal" :in-theory (disable sx-list) :expand ((sx s fr heap) (asgv :list (list s))))))

(defthm skv-select
  (implies (and (eq (kar s) :select) (skv-list n (kadddr s) fr heap)
                (skv-list n (kadr (lkp (mv-nth 1 (sv (kadr s) fr heap)) (kaddr s))) fr heap))
           (skv-stmt n s fr heap))
  :hints (("Goal" :in-theory (disable sx-list) :expand ((sx s fr heap) (asgv :list (list s)))
           :use ((:instance member-asgv-lkp-arm (k (mv-nth 1 (sv (kadr s) fr heap))) (arms (kaddr s)))))))

(defthm skv-other
  (implies (not (member-equal (kar s) '(:assign :if :select))) (skv-stmt n s fr heap))
  :hints (("Goal" :expand ((sx s fr heap)))))

(defthm skv-nil
  (implies (atom ss) (skv-list n ss fr heap))
  :hints (("Goal" :expand ((sx-list ss fr heap)))))

(defthm skv-cons
  (implies (and (consp ss) (skv-stmt n (car ss) fr heap)
                (skv-list n (cdr ss) (mv-nth 1 (sx (car ss) fr heap)) (mv-nth 2 (sx (car ss) fr heap))))
           (skv-list n ss fr heap))
  :hints (("Goal" :in-theory (disable sx) :expand ((sx-list ss fr heap) (asgv :list ss)))))

(defthm skv-flag
  (if (eq flag :stmt) (skv-stmt n s fr heap) (skv-list n s fr heap))
  :rule-classes nil
  :hints (("Goal" :induct (sxk-ind flag s fr heap) :do-not-induct t
           :in-theory (disable skv-stmt skv-list sx sx-list kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select))))))

(defthm sx-list-keeps-v
  (implies (not (member-equal n (asgv :list s)))
           (equal (lkp n (mv-nth 1 (sx-list s fr heap))) (lkp n fr)))
  :hints (("Goal" :use (:instance skv-flag (flag :list)))))

(defthm sx-list-agree-v
  (implies (not (intersectp-equal ns (asgv :list s)))
           (lkp-agree ns fr (mv-nth 1 (sx-list s fr heap))))
  :hints (("Goal" :induct (lkp-agree-ind ns))))

(defthm em-ok-after-sx-v
  (implies (and (em-ok em env fr) (not (intersectp-equal (asgv :list s) (em-names em))))
           (em-ok em env (mv-nth 1 (sx-list s fr heap))))
  :hints (("Goal" :do-not-induct t :expand ((em-ok em env (mv-nth 1 (sx-list s fr heap))))
           :in-theory (e/d (var-ok) (em-ok-necc sx-list sx-list-keeps-v sx-list-keeps not-member-intersect))
           :use ((:instance em-ok-necc (x (em-ok-witness em env (mv-nth 1 (sx-list s fr heap)))))
                 (:instance sx-list-keeps (n (cadr (lkp (em-ok-witness em env (mv-nth 1 (sx-list s fr heap))) em))))
                 (:instance sx-list-keeps-v (n (cadr (lkp (em-ok-witness em env (mv-nth 1 (sx-list s fr heap))) em))))
                 (:instance not-member-intersect (y (cadr (lkp (em-ok-witness em env (mv-nth 1 (sx-list s fr heap))) em)))
                            (a (em-names em)) (b (asgv :list s)))))))

; ---- the stobj's object, INOUT, its heap entry S; the update roles' components

(defun okey (o fr) (cddr (cdr (lkp o fr))))

(defun obj-at (o s fr heap)
  (let ((b (cdr (lkp o fr))))
    (and (consp b) (eq (car b) :obj) (consp (cdr b)) (eq (cadr b) :inout)
         (consp (lkp (cddr b) heap)) (equal (cdr (lkp (cddr b) heap)) s))))

(defthm obj-at-is (implies (obj-at o s fr heap) (obj-is o s fr heap)))

(defthm put-put-same (equal (put k v (put k w al)) (put k v al)))

(defthm lkp-put-same (equal (lkp k (put k v al)) (cons k v)))

(defthm obj-at-after
  (implies (obj-at o s fr heap) (obj-at o s2 (mv-nth 1 (sx-list ss fr heap)) (put (okey o fr) s2 heap))))

(defthm okey-after (implies (equal (cadr (lkp o fr)) :obj) (equal (okey o (mv-nth 1 (sx-list ss fr heap))) (okey o fr))))

(defthm obj-at-cadr (implies (obj-at o s fr heap) (equal (cadr (lkp o fr)) :obj)))

(defun-sk st-wf (st s)
  (forall x (and (implies (eq (g-role x st) :set) (int64p (cdr (lkp (g-comp x st) s))))
                 (implies (eq (g-role x st) :seti) (farrayp (cdr (lkp (g-comp x st) s)))))))

(in-theory (disable st-wf okey obj-at))

(defthm st-ok-put-int
  (implies (and (st-ok st o s) (int64p v) (int64p (cdr (lkp c s)))) (st-ok st o (put c v s)))
  :hints (("Goal" :expand ((st-ok st o (put c v s))) :in-theory (disable st-ok-necc g-role g-obj g-comp)
           :use ((:instance st-ok-necc (x (st-ok-witness st o (put c v s))))))))

(defthm st-ok-put-arr
  (implies (and (st-ok st o s) (farrayp a) (farrayp (cdr (lkp c s))) (equal (len (cdr a)) (len (cddr (lkp c s)))))
           (st-ok st o (put c a s)))
  :hints (("Goal" :expand ((st-ok st o (put c a s))) :in-theory (disable st-ok-necc g-role g-obj g-comp)
           :use ((:instance st-ok-necc (x (st-ok-witness st o (put c a s))))))))

(defthm st-wf-put-int
  (implies (and (st-wf st s) (int64p v) (int64p (cdr (lkp c s)))) (st-wf st (put c v s)))
  :hints (("Goal" :expand ((st-wf st (put c v s))) :in-theory (disable st-wf-necc g-role g-comp)
           :use ((:instance st-wf-necc (x (st-wf-witness st (put c v s))))))))

(defthm st-wf-put-arr
  (implies (and (st-wf st s) (farrayp a) (farrayp (cdr (lkp c s)))) (st-wf st (put c a s)))
  :hints (("Goal" :expand ((st-wf st (put c a s))) :in-theory (disable st-wf-necc g-role g-comp)
           :use ((:instance st-wf-necc (x (st-wf-witness st (put c a s))))))))

; ---- stable code reads only variables: unchanged past statements not assigning them

(defthm g-stable-cf (implies (g-stable c) (cf-expr c)))

(defthm stable-sv-after
  (implies (and (g-stable c) (not (intersectp-equal (sv-names c) (asgv :list ss))))
           (equal (sv c (mv-nth 1 (sx-list ss fr heap)) h2) (sv c fr heap)))
  :hints (("Goal" :in-theory (disable sv-agree sx-list-agree-v sv-is-fv cf-sv-names)
           :use ((:instance sv-agree (e c) (fr2 (mv-nth 1 (sx-list ss fr heap))))
                 (:instance sx-list-agree-v (ns (sv-names c)) (s ss))
                 (:instance sv-is-fv (e c) (fr (mv-nth 1 (sx-list ss fr heap))) (heap h2))
                 (:instance sv-is-fv (e c) (fr (mv-nth 1 (sx-list ss fr heap))) (heap heap))))))

(defthm not-intersect-via-sub
  (implies (and (subsetp-equal a c) (not (intersectp-equal b c))) (not (intersectp-equal a b))))

; ---- what is proved of a statement: run by sx-list it answers :normal, the
; stobj's heap entry put to a-st's S', which keeps st-ok and st-wf
(defun gst-sem (x em cnt locs sigs fnames st outs env s defs n fr heap o)
  (mv-let (e ss cnt2 locs2) (g-stmt x em cnt locs sigs fnames st outs nil nil)
    (declare (ignore cnt2))
    (mv-let (ae s2) (a-st x env s st defs n)
      (implies (and (not e) (not ae) (no-calls :term x sigs nil) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st))
               (mv-let (stt fr2 h2) (sx-list ss fr heap)
                 (declare (ignore fr2))
                 (and (equal stt :normal) (equal h2 (put (okey o fr) s2 heap)) (st-ok st o s2) (st-wf st s2)))))))

; its names: it assigns only new temporaries
(defun stn-ok (x em cnt locs sigs fnames st outs)
  (mv-let (e ss cnt2 locs2) (g-stmt x em cnt locs sigs fnames st outs nil nil)
    (declare (ignore cnt2))
    (implies (not e)
             (and (subsetp-equal locs locs2) (subsetp-equal (asgv :list ss) (strip-cars locs2))
                  (not (intersectp-equal (asgv :list ss) (append fnames (em-names em) (strip-cars locs))))))))

(defmacro gtx (k) `(mv-nth ,k (g-stmt x em cnt locs sigs fnames st outs nil nil)))

(defthm gst-sem-use
  (implies (and (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o)
                (not (gtx 0)) (not (car (a-st x env s st defs n))) (no-calls :term x sigs nil) (em-ok em env fr)
                (decl-ok (gtx 3) fr) (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (st-wf st s) (obj-at o s fr heap)
                (sn-hyps) (em-nostobj em st))
           (and (equal (car (sx-list (gtx 1) fr heap)) :normal)
                (equal (mv-nth 2 (sx-list (gtx 1) fr heap)) (put (okey o fr) (mv-nth 1 (a-st x env s st defs n)) heap))
                (st-ok st o (mv-nth 1 (a-st x env s st defs n)))
                (st-wf st (mv-nth 1 (a-st x env s st defs n)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (gst-sem) (g-stmt a-st sx-list no-calls em-ok decl-ok st-ok st-wf obj-at)))))

(defthm stn-ok-use
  (implies (and (stn-ok x em cnt locs sigs fnames st outs) (not (gtx 0)))
           (and (subsetp-equal locs (gtx 3))
                (subsetp-equal (asgv :list (gtx 1)) (strip-cars (gtx 3)))
                (not (intersectp-equal (asgv :list (gtx 1)) (append fnames (em-names em) (strip-cars locs))))))
  :hints (("Goal" :in-theory (disable g-stmt))))

(in-theory (disable gst-sem stn-ok))

; ---- openers

(defmacro gst-dis ()
  ''(g-st-free g-if g-mvnth g-expr g-sargs g-scall-args g-svals g-unop g-binop g-st-ident g-role g-obj g-comp em-names
     g-sexpr g-settle g-stail g-tvals g-mvtmps g-moves g-acts-mv g-acts-place g-arg-of g-conses g-fresh g-chain
     g-callst g-sacts g-upd))

(defthm g-stmt-set
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :set))
           (equal (g-stmt x em cnt locs sigs fnames st outs nil nil)
                  (if (not (and (= (len x) 3) (equal outs (list (caddr x))) (equal (g-obj (car x) st) (g-obj (caddr x) st))))
                      (mv :stobj nil cnt locs)
                    (mv-let (e s c ty cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                      (if (or e (not (eq ty :int64))) (mv (or e :type) nil cnt locs)
                        (mv-let (e s cs cnt locs) (if (symbolp (caddr x)) (mv nil s (list c) cnt locs)
                                                    (g-settle (list s) (list c) cnt locs (append fnames (em-names em))))
                          (if e (mv e nil cnt locs)
                            (mv-let (e si cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs nil nil)
                              (if e (mv e nil cnt locs)
                                (mv nil (append s si (list (list :assign (list :comp (g-obj (car x) st) (g-comp (car x) st)) (car cs))))
                                    cnt locs))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (gst-dis)) :expand ((g-stmt x em cnt locs sigs fnames st outs nil nil)))))

(defthm a-st-set
  (implies (and (consp x) (eq (g-role (car x) st) :set))
           (equal (a-st x env s st defs n)
                  (if (zp n) (mv :fuel s)
                    (mv-let (e v) (a-sx (cadr x) env s st defs (1- n))
                      (if e (mv e s)
                        (mv-let (e s1) (a-st (caddr x) env s st defs (1- n))
                          (if e (mv e s) (mv nil (put (g-comp (car x) st) v s1)))))))))
  :hints (("Goal" :in-theory (e/d (kadr kaddr kar) (g-role g-comp a-sx)) :expand ((a-st x env s st defs n)))))

(defthm a-st-sym
  (implies (symbolp x)
           (equal (a-st x env s st defs n)
                  (cond ((zp n) (mv :fuel s)) ((eq (g-role x st) :stobj) (mv nil s)) (t (mv :stobj s)))))
  :hints (("Goal" :in-theory (disable g-role) :expand ((a-st x env s st defs n)))))

(defthm g-stmt-sym
  (implies (symbolp x)
           (equal (g-stmt x em cnt locs sigs fnames st outs nil nil)
                  (if (equal (list x) outs) (mv nil nil cnt locs) (mv :stobj nil cnt locs))))
  :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (gst-dis)) :expand ((g-stmt x em cnt locs sigs fnames st outs nil nil)))))

(defthm g-settle1
  (equal (g-settle (list s) (list c) cnt locs used)
         (if (g-stable c) (mv nil (true-list-fix s) (list c) cnt locs)
           (mv-let (e tmp cnt locs) (g-fresh 'v :int64 cnt locs used)
             (if e (mv e nil nil cnt locs)
               (mv nil (append (true-list-fix s) (list (list :assign (list :var tmp) c))) (list (list :var tmp)) cnt locs)))))
  :hints (("Goal" :in-theory (disable g-fresh g-stable)
           :expand ((g-settle (list s) (list c) cnt locs used) (:free (cnt locs) (g-settle nil nil cnt locs used))))))

(defmacro hs-of () '(cdr (lkp (okey o fr) heap)))

(defthm sx-assign-comp
  (implies (and (not (car (sv c fr heap))) (int64p (mv-nth 1 (sv c fr heap))) (obj-at o (hs-of) fr heap)
                (int64p (cdr (lkp comp (hs-of)))))
           (equal (sx (list :assign (list :comp o comp) c) fr heap)
                  (mv :normal fr (put (okey o fr) (put comp (mv-nth 1 (sv c fr heap)) (hs-of)) heap))))
  :hints (("Goal" :in-theory (e/d (obj-at okey) (sv)) :expand ((sx (list :assign (list :comp o comp) c) fr heap)))))

(defthm obj-at-lkp
  (implies (obj-at o s fr heap) (equal (cdr (lkp (okey o fr) heap)) s))
  :hints (("Goal" :in-theory (enable obj-at okey))))

(defthm sx-list-true-list-fix (equal (sx-list (true-list-fix ss) fr heap) (sx-list ss fr heap))
  :hints (("Goal" :induct (sapp-ind ss fr heap) :in-theory (disable sx) :expand ((sx-list ss fr heap) (sx-list nil fr heap)
                                             (:free (a b) (sx-list (cons a b) fr heap))))))
(defthm asgv-true-list-fix (equal (asgv :list (true-list-fix ss)) (asgv :list ss))
  :hints (("Goal" :induct (len ss) :expand ((asgv :list ss) (:free (a b) (asgv :list (cons a b))) (true-list-fix ss)))))

(defthm obj-at-frame
  (implies (equal (cadr (lkp o fr)) :obj) (equal (obj-at o s (mv-nth 1 (sx-list ss fr h0)) heap) (obj-at o s fr heap)))
  :hints (("Goal" :in-theory (enable obj-at))))

(defthm obj-at-put
  (implies (obj-at o s fr heap) (obj-at o s2 fr (put (okey o fr) s2 heap)))
  :hints (("Goal" :in-theory (enable obj-at okey))))

(defthm put-lkp-same
  (implies (consp (lkp k al)) (equal (put k (cdr (lkp k al)) al) al)))

(defthm put-okey-same
  (implies (obj-at o s fr heap) (equal (put (okey o fr) s heap) heap))
  :hints (("Goal" :in-theory (enable obj-at okey))))

(defthm no-calls-set
  (implies (and (consp x) (not (eq (car x) 'quote)) (not (consp (car x))) (no-calls :term x sigs cs))
           (and (no-calls :term (cadr x) sigs cs) (no-calls :term (caddr x) sigs cs) (no-calls :term (cadddr x) sigs cs)))
  :hints (("Goal" :expand ((no-calls :term x sigs cs) (no-calls :list (cdr x) sigs cs)
                           (no-calls :list (cddr x) sigs cs) (no-calls :list (cdddr x) sigs cs)))))

(defthm st-ok-obj
  (implies (and (st-ok st o s) (member-eq (g-role x st) '(:field :size :elem :set :seti :stobj))) (equal (g-obj x st) o))
  :hints (("Goal" :use st-ok-necc :in-theory (disable st-ok-necc g-role g-obj))))

(defthm st-wf-set
  (implies (and (st-wf st s) (eq (g-role x st) :set)) (int64p (cdr (lkp (g-comp x st) s))))
  :hints (("Goal" :use st-wf-necc :in-theory (disable st-wf-necc g-role g-comp))))

(defthm st-wf-seti
  (implies (and (st-wf st s) (eq (g-role x st) :seti)) (farrayp (cdr (lkp (g-comp x st) s))))
  :hints (("Goal" :use st-wf-necc :in-theory (disable st-wf-necc g-role g-comp))))

(defthm gs-sem-int64
  (implies (and (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o) (equal (gsx 3) :int64)
                (not (gsx 0)) (not (car (a-sx x env s st defs n))) (no-calls :term x sigs nil) (em-ok em env fr)
                (decl-ok (gsx 5) fr) (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap))
           (int64p (mv-nth 1 (a-sx x env s st defs n))))
  :hints (("Goal" :in-theory (union-theories '(scalar-ok) (theory 'minimal-theory)) :use gs-sem-use)))

(defmacro k1 (k) `(mv-nth ,k (g-sexpr (cadr x) em cnt locs sigs fnames st)))

(defmacro gst-hint-dis ()
  ''(g-sexpr g-stmt a-sx a-st sx-list sx sv no-calls em-ok st-ok st-wf obj-at g-role g-obj g-comp g-tmp
     g-fresh g-stable nfix dty decl-ok-subset sv-is-fv fv sx-list-is-fx-list fx-list okey st-ok-necc st-wf-necc
     put lkp put-okey-same obj-is gs-sem-holds))

; (update-f v hs): v's statements, then hs%f = v
(defthm gst-set-sym
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :set) (symbolp (caddr x)))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
           :in-theory (set-difference-theories (current-theory :here) (gst-hint-dis))
           :use ((:instance put-okey-same (fr (mv-nth 1 (sx-list (k1 1) fr heap))))
                 (:instance gs-sem-holds (x (cadr x)) (n (1- n)))))))

; (update-f v s), s an update, v's code stable: v's statements, s's, hs%f = v
(defmacro k3s (k) `(mv-nth ,k (g-stmt (caddr x) em (k1 4) (k1 5) sigs fnames st outs nil nil)))

; the value's code, stable, reads the same past the inner update's statements
(defthm set-code-after
  (implies (and (g-stable (k1 2)) (not (k1 0)) (not (k3s 0)) (sn-ok (cadr x) em cnt locs sigs fnames st)
                (stn-ok (caddr x) em (k1 4) (k1 5) sigs fnames st outs))
           (equal (sv (k1 2) (mv-nth 1 (sx-list (k3s 1) frx h)) h2) (sv (k1 2) frx h)))
  :hints (("Goal" :in-theory (union-theories '(stable-sv-after) (theory 'minimal-theory))
           :use ((:instance sn-ok-use (x (cadr x)))
                 (:instance stn-ok-use (x (caddr x)) (cnt (k1 4)) (locs (k1 5)))
                 (:instance not-intersect-via-sub (a (sv-names (k1 2))) (b (asgv :list (k3s 1)))
                            (c (append fnames (em-names em) (strip-cars (k1 5)))))))))

(defthm gst-set-stable
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :set) (not (symbolp (caddr x))) (g-stable (k1 2))
                (gst-sem (caddr x) em (k1 4) (k1 5) sigs fnames st outs env s defs (1- n)
                         (mv-nth 1 (sx-list (k1 1) fr heap)) heap o)
                (stn-ok (caddr x) em (k1 4) (k1 5) sigs fnames st outs))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
           :in-theory (set-difference-theories (current-theory :here) (gst-hint-dis))
           :use ((:instance gs-sem-holds (x (cadr x)) (n (1- n)))
                 (:instance decl-ok-subset (a (k1 5)) (b (k3s 3)))))))

; v's code into a temporary first
(defmacro tmpv () '(g-tmp 'v (1+ (nfix (k1 4)))))
(defmacro locv () '(cons (cons (tmpv) :int64) (true-list-fix (k1 5))))
(defmacro k3t (k) `(mv-nth ,k (g-stmt (caddr x) em (1+ (nfix (k1 4))) (locv) sigs fnames st outs nil nil)))
(defmacro frv () '(put (tmpv) (cons :int64 (mv-nth 1 (a-sx (cadr x) env s st defs (1- n)))) (mv-nth 1 (sx-list (k1 1) fr heap))))

(defthm obj-at-put-scalar
  (implies (and (obj-at o s fr heap) (equal (dty k fr) (list ty)) (scalar-ok ty v))
           (obj-at o s (put k (cons ty v) fr) heap))
  :hints (("Goal" :cases ((equal k o)) :in-theory (enable dty obj-at))))

(defthm lkp-obj-put-scalar
  (implies (and (equal (cadr (lkp o fr)) :obj) (consp (dty k fr)) (not (equal (car (dty k fr)) :obj)))
           (equal (lkp o (put k v fr)) (lkp o fr)))
  :hints (("Goal" :cases ((equal k o)) :in-theory (enable dty))))

(defthm okey-put-scalar
  (implies (and (equal (cadr (lkp o fr)) :obj) (consp (dty k fr)) (not (equal (car (dty k fr)) :obj)))
           (equal (okey o (put k v fr)) (okey o fr)))
  :hints (("Goal" :in-theory (e/d (okey) (lkp-put)) :use lkp-obj-put-scalar)))

(defthm g-fresh-cnt
  (implies (not (car (g-fresh b ty cnt locs used))) (equal (mv-nth 2 (g-fresh b ty cnt locs used)) (1+ (nfix cnt))))
  :hints (("Goal" :in-theory (e/d (g-fresh) (g-tmp)))))

(defthm sv-names-var (equal (sv-names (list :var k)) (list k)) :hints (("Goal" :expand ((sv-names (list :var k))))))

(defthm tmp-after-abs
  (implies (not (intersectp-equal (asgv :list si) (append f e (strip-cars (cons (cons tmp ty) l)))))
           (equal (sv (list :var tmp) (mv-nth 1 (sx-list si frx h)) h2) (sv (list :var tmp) frx h)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable stable-sv-after) :use (:instance stable-sv-after (c (list :var tmp)) (ss si) (fr frx) (heap h)))))

(defthm tmp-code-after
  (implies (and (not (k3t 0)) (stn-ok (caddr x) em (1+ (nfix (k1 4))) (locv) sigs fnames st outs))
           (equal (sv (list :var (tmpv)) (mv-nth 1 (sx-list (k3t 1) frx h)) h2) (sv (list :var (tmpv)) frx h)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance stn-ok-use (x (caddr x)) (cnt (1+ (nfix (k1 4)))) (locs (locv)))
                 (:instance tmp-after-abs (si (k3t 1)) (f fnames) (e (em-names em)) (tmp (tmpv)) (ty :int64)
                            (l (true-list-fix (k1 5))))))))

(defthm gst-set-tmp
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :set) (not (symbolp (caddr x))) (not (g-stable (k1 2)))
                (gst-sem (caddr x) em (1+ (nfix (k1 4))) (locv) sigs fnames st outs env s defs (1- n) (frv) heap o)
                (stn-ok (caddr x) em (1+ (nfix (k1 4))) (locv) sigs fnames st outs))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
           :in-theory (set-difference-theories (current-theory :here) (cons 'g-fresh-out (gst-hint-dis)))
           :use ((:instance gs-sem-holds (x (cadr x)) (n (1- n)))
                 (:instance g-fresh-out (b 'v) (ty :int64) (cnt (k1 4)) (locs (k1 5)) (used (append fnames (em-names em))))))
          (and stable-under-simplificationp '(:use ((:instance stn-ok-use (x (caddr x)) (cnt (1+ (nfix (k1 4)))) (locs (locv)) (outs (list (caddr x))))
                 (:instance decl-ok-subset (a (locv))
                     (b (mv-nth 3 (g-stmt (caddr x) em (1+ (nfix (k1 4))) (locv) sigs fnames st (list (caddr x)) nil nil)))))))))
