; gen-stcallst: g-callst, the CALL of a stobj subroutine (GEN.md 4 (4a),
; second piece), against the source's call under an oracle. For x = (f . args),
; f a :sub of st answering only its stobj, no stobj argument an update
; (not g-upd: each stobj argument is f's formal itself), g-callst's statements
; (the value arguments' statements, then CALL f(objs, codes)) run by sxc-list
; answer :normal, the stobj's heap entry put to a-call-val's S'. The source
; meaning: the value arguments by a-sx-list on S, then the oracle
; `(a-call-val f ks s)` => (mv err s') (`a-stcall`). Hypotheses: `c-sorc o st`
; (the Fortran oracle s-call-val answers on the emitted CALL as a-call-val
; does on its arguments' values, the caller's frame unchanged) and
; `a-call-ok st o` (a-call-val keeps st-ok and st-wf); both name only the
; oracles, not the translator's output.

(in-package "ACL2")

(include-book "gen-stthm")
(include-book "gen-stst")
(include-book "gen-stcall")

; (mv err S' rs): rs the call's results by position (nil at a stobj's), read by an mv lambda (gen-stc)
(encapsulate (((a-call-val * * *) => (mv * * *)))
  (local (defun a-call-val (f ks s) (declare (ignore f ks)) (mv :unknown s nil))))

; a call's value arguments, and the objects g-scall-args passes for its stobj formals
(defun g-cvals (formals xs st)
  (cond ((or (atom formals) (atom xs)) nil)
        ((eq (g-role (car formals) st) :stobj) (g-cvals (cdr formals) (cdr xs) st))
        (t (cons (car xs) (g-cvals (cdr formals) (cdr xs) st)))))

(defun g-scs (formals xs st)
  (cond ((or (atom formals) (atom xs)) nil)
        ((eq (g-role (car formals) st) :stobj) (cons (list :var (g-obj (car formals) st)) (g-scs (cdr formals) (cdr xs) st)))
        (t (g-scs (cdr formals) (cdr xs) st))))

(defun all-int64-ty (ts) (if (atom ts) t (and (eq (car ts) :int64) (all-int64-ty (cdr ts)))))

; the source's meaning of the call
(defun a-stcall (x env s st defs n)
  (mv-let (e ks) (a-sx-list (g-cvals (g-obj (car x) st) (cdr x) st) env s st defs n)
    (if e (mv e s nil) (a-call-val (car x) ks s))))

; ---- g-scall-args (upd t) is g-sargs on the value arguments

(defun gsc-ind (formals xs em cnt locs sigs fnames st)
  (cond ((or (atom formals) (atom xs)) (list em cnt locs))
        ((eq (g-role (car formals) st) :stobj) (gsc-ind (cdr formals) (cdr xs) em cnt locs sigs fnames st))
        (t (mv-let (e s c ty cnt locs) (g-sexpr (car xs) em cnt locs sigs fnames st)
             (declare (ignore e s c ty))
             (gsc-ind (cdr formals) (cdr xs) em cnt locs sigs fnames st)))))

(defthm append-true-list-fix-left (equal (append (true-list-fix a) b) (append a b)))

(defmacro gsc (k) `(mv-nth ,k (g-scall-args formals xs t em cnt locs sigs fnames st)))
(defmacro gsa (k) `(mv-nth ,k (g-sargs (g-cvals formals xs st) em cnt locs sigs fnames st)))

(defthm g-scall-args-is-g-sargs
  (implies (not (gsc 0))
           (and (not (gsa 0)) (equal (g-flat (gsc 1)) (gsa 1)) (equal (gsc 2) (g-scs formals xs st))
                (equal (gsc 3) (gsa 2)) (equal (gsc 4) (gsa 4)) (equal (gsc 5) (gsa 5)) (all-int64-ty (gsa 3))))
  :hints (("Goal" :induct (gsc-ind formals xs em cnt locs sigs fnames st)
           :in-theory (disable g-sexpr)
           :expand ((g-scall-args formals xs t em cnt locs sigs fnames st)
                    (g-sargs (g-cvals formals xs st) em cnt locs sigs fnames st)
                    (g-sargs nil em cnt locs sigs fnames st)
                    (g-cvals formals xs st)))))

(defthm g-scall-args-true-list
  (true-listp (mv-nth 3 (g-scall-args formals xs upd em cnt locs sigs fnames st)))
  :hints (("Goal" :induct (gsc-ind formals xs em cnt locs sigs fnames st)
           :in-theory (disable g-sexpr) :expand ((g-scall-args formals xs upd em cnt locs sigs fnames st)))))

(defthm g-sacts-noupd
  (implies (not (g-upd vars xs st))
           (equal (g-sacts vars xs em cnt locs sigs fnames st) (list nil nil cnt locs)))
  :hints (("Goal" :induct (g-upd vars xs st) :in-theory (disable g-stmt g-mvnth g-role)
           :expand ((g-sacts vars xs em cnt locs sigs fnames st)))))

(defthm g-callst-ok
  (implies (not (mv-nth 0 (g-callst x em cnt locs sigs fnames st dests)))
           (and (consp x) (true-listp x) (= (len (g-obj (car x) st)) (len (cdr x)))
                (not (mv-nth 0 (g-scall-args (g-obj (car x) st) (cdr x) t em cnt locs sigs fnames st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable g-scall-args g-settle g-sacts g-flat g-upd)
           :expand ((g-callst x em cnt locs sigs fnames st dests)))))

; g-callst, no stobj argument an update
(defthm g-callst-noupd
  (implies (and (consp x) (true-listp x) (= (len (g-obj (car x) st)) (len (cdr x)))
                (not (g-upd (g-obj (car x) st) (cdr x) st))
                (not (mv-nth 0 (g-scall-args (g-obj (car x) st) (cdr x) t em cnt locs sigs fnames st))))
           (equal (g-callst x em cnt locs sigs fnames st nil)
                  (list nil
                        (append (mv-nth 1 (g-sargs (g-cvals (g-obj (car x) st) (cdr x) st) em cnt locs sigs fnames st))
                                (list (list :call (g-sym (car x) nil)
                                            (append (g-scs (g-obj (car x) st) (cdr x) st)
                                                    (mv-nth 2 (g-sargs (g-cvals (g-obj (car x) st) (cdr x) st)
                                                                       em cnt locs sigs fnames st))))))
                        (mv-nth 4 (g-sargs (g-cvals (g-obj (car x) st) (cdr x) st) em cnt locs sigs fnames st))
                        (mv-nth 5 (g-sargs (g-cvals (g-obj (car x) st) (cdr x) st) em cnt locs sigs fnames st)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-scall-args g-sargs g-sacts g-scall-args-is-g-sargs g-scall-args-true-list)
           :use ((:instance g-scall-args-is-g-sargs (formals (g-obj (car x) st)) (xs (cdr x)))
                 (:instance g-scall-args-true-list (formals (g-obj (car x) st)) (xs (cdr x)) (upd t)))
           :expand ((g-callst x em cnt locs sigs fnames st nil)))))

; ---- the oracles' hypotheses

(defun svs-is (cs ks fr heap)
  (if (atom cs) (atom ks)
    (mv-let (err v) (sv (car cs) fr heap)
      (and (consp ks) (not err) (equal v (car ks)) (svs-is (cdr cs) (cdr ks) fr heap)))))

(defun int64s (ks) (if (atom ks) t (and (int64p (car ks)) (int64s (cdr ks)))))

(defthm svs-ok-is
  (implies (and (svs-ok cs ts ks fr heap) (all-int64-ty ts))
           (and (svs-is cs ks fr heap) (int64s ks)))
  :hints (("Goal" :induct (svs-ok cs ts ks fr heap))))

; the Fortran oracle answers the emitted CALL as the source's does
(defun-sk c-sorc (o st)
  (forall (f xs cs fr heap ks s)
    (implies (and (eq (g-role f st) :sub) (equal (len xs) (len (g-obj f st))) (obj-at o s fr heap) (svs-is cs ks fr heap) (int64s ks)
                  (not (mv-nth 0 (a-call-val f ks s))))
             (equal (s-call-val (g-sym f nil) (append (g-scs (g-obj f st) xs st) cs) fr heap)
                    (list nil fr (put (okey o fr) (mv-nth 1 (a-call-val f ks s)) heap))))))

; the source's call keeps the invariants
(defun-sk a-call-ok (st o)
  (forall (f ks s)
    (implies (and (not (mv-nth 0 (a-call-val f ks s))) (st-ok st o s) (st-wf st s))
             (and (st-ok st o (mv-nth 1 (a-call-val f ks s))) (st-wf st (mv-nth 1 (a-call-val f ks s)))))))

(in-theory (disable c-sorc a-call-ok))

; ---- sxc-list over an append, and one CALL

(defthm sxc-list-append-sx
  (implies (equal (mv-nth 0 (sx-list a fr heap)) :normal)
           (equal (sxc-list (append a b) fr heap)
                  (sxc-list b (mv-nth 1 (sx-list a fr heap)) (mv-nth 2 (sx-list a fr heap)))))
  :hints (("Goal" :induct (sapp-ind a fr heap) :in-theory (disable sx sxc sxc-is-sx)
           :expand ((sx-list a fr heap) (sxc-list (cons (car a) (append (cdr a) b)) fr heap) (sxc-list b fr heap)))
          ("Subgoal *1/2" :use (:instance sxc-is-sx (s (car a))))))

(defthm sxc-list-one-call
  (implies (and (equal (kar c) :call) (not (mv-nth 0 (s-call-val (kadr c) (kaddr c) fr heap))))
           (equal (sxc-list (list c) fr heap)
                  (list :normal (mv-nth 1 (s-call-val (kadr c) (kaddr c) fr heap))
                        (mv-nth 2 (s-call-val (kadr c) (kaddr c) fr heap)))))
  :hints (("Goal" :expand ((sxc-list (list c) fr heap) (sxc c fr heap)
                           (sxc-list nil (mv-nth 1 (s-call-val (kadr c) (kaddr c) fr heap))
                                     (mv-nth 2 (s-call-val (kadr c) (kaddr c) fr heap)))))))

; obj-at survives statements that answer with the heap unchanged
(defthm obj-at-after-same
  (implies (and (obj-at o s fr heap) (equal (mv-nth 2 (sx-list ss fr heap)) heap))
           (and (obj-at o s (mv-nth 1 (sx-list ss fr heap)) heap)
                (equal (okey o (mv-nth 1 (sx-list ss fr heap))) (okey o fr))))
  :hints (("Goal" :in-theory (e/d (obj-at okey) (sx-list)) :use (:instance sx-list-keeps-obj (o o)))))

; ---- the theorem

; the glue, on plain variables: the value statements, then the CALL
(defthm callst-glue
  (implies (and (equal (car (sx-list a fr heap)) :normal) (equal (mv-nth 2 (sx-list a fr heap)) heap)
                (equal (kar c) :call)
                (equal (s-call-val (kadr c) (kaddr c) (mv-nth 1 (sx-list a fr heap)) heap) (list nil fr1 h2)))
           (equal (sxc-list (append a (list c)) fr heap) (list :normal fr1 h2)))
  :hints (("Goal" :in-theory (disable sx-list sxc-list sxc-list-one-call)
           :use (:instance sxc-list-one-call (fr (mv-nth 1 (sx-list a fr heap)))))))

(defmacro cvs () '(g-cvals (g-obj (car x) st) (cdr x) st))
(defmacro gca (k) `(mv-nth ,k (g-sargs (cvs) em cnt locs sigs fnames st)))
(defmacro cks () '(mv-nth 1 (a-sx-list (cvs) env s st defs n)))
(defmacro cfr1 () '(mv-nth 1 (sx-list (gca 1) fr heap)))

(defthm a-stcall-parts
  (implies (not (car (a-stcall x env s st defs n)))
           (and (not (car (a-sx-list (cvs) env s st defs n)))
                (not (car (a-call-val (car x) (cks) s)))
                (equal (mv-nth 1 (a-stcall x env s st defs n)) (mv-nth 1 (a-call-val (car x) (cks) s)))))
  :rule-classes nil)

; the shape of g-callst's output, no stobj argument an update
(defthm callst-shape
  (implies (and (not (car (g-callst x em cnt locs sigs fnames st nil))) (not (g-upd (g-obj (car x) st) (cdr x) st)))
           (and (equal (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil))
                       (append (gca 1) (list (list :call (g-sym (car x) nil) (append (g-scs (g-obj (car x) st) (cdr x) st) (gca 2))))))
                (equal (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) (gca 5))
                (not (car (g-sargs (cvs) em cnt locs sigs fnames st)))
                (all-int64-ty (gca 3))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-callst g-sargs g-scall-args g-callst-noupd g-scall-args-is-g-sargs g-cvals g-scs g-upd)
           :use ((:instance g-callst-ok (dests nil))
                 (:instance g-callst-noupd (locs locs))
                 (:instance g-scall-args-is-g-sargs (formals (g-obj (car x) st)) (xs (cdr x)))))))

; the value arguments' statements, on any argument list xs
(defmacro gxa (k) `(mv-nth ,k (g-sargs xs em cnt locs sigs fnames st)))
(defmacro xks () '(mv-nth 1 (a-sx-list xs env s st defs n)))
(defmacro xfr () '(mv-nth 1 (sx-list (gxa 1) fr heap)))

(defthm callst-args-run
  (implies (and (not (car (g-sargs xs em cnt locs sigs fnames st))) (all-int64-ty (gxa 3))
                (not (car (a-sx-list xs env s st defs n)))
                (no-calls :list xs sigs nil) (em-ok em env fr) (decl-ok (gxa 5) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st))
           (and (equal (car (sx-list (gxa 1) fr heap)) :normal)
                (equal (mv-nth 2 (sx-list (gxa 1) fr heap)) heap)
                (svs-is (gxa 2) (xks) (xfr) heap) (int64s (xks))
                (obj-at o s (xfr) heap) (equal (okey o (xfr)) (okey o fr))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-sargs a-sx-list sx-list gsa-sem gsa-sem-use obj-at okey st-ok no-calls em-ok decl-ok
                               svs-ok svs-is obj-at-after-same svs-ok-is obj-at-is)
           :use ((:instance gs-sem-thm (flag :args) (x xs) (vars nil))
                 gsa-sem-use obj-at-is
                 (:instance obj-at-after-same (ss (gxa 1)))
                 (:instance svs-ok-is (cs (gxa 2)) (ts (gxa 3)) (ks (xks)) (fr (xfr)))))))

(defthm gst-callst
  (implies (and (eq (g-role (car x) st) :sub) (not (g-upd (g-obj (car x) st) (cdr x) st))
                (not (car (g-callst x em cnt locs sigs fnames st nil)))
                (not (car (a-stcall x env s st defs n))) (c-sorc o st) (a-call-ok st o)
                (no-calls :list (cvs) sigs nil) (em-ok em env fr)
                (decl-ok (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st))
           (and (equal (car (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap)) :normal)
                (equal (mv-nth 2 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap))
                       (put (okey o fr) (mv-nth 1 (a-stcall x env s st defs n)) heap))
                (st-ok st o (mv-nth 1 (a-stcall x env s st defs n)))
                (st-wf st (mv-nth 1 (a-stcall x env s st defs n)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable a-stcall g-role g-callst g-sargs a-sx-list sx-list sxc-list obj-at okey st-ok st-wf
                               no-calls em-ok decl-ok g-cvals g-scs g-sym svs-is put lkp g-upd g-obj
                               c-sorc-necc a-call-ok-necc callst-glue)
           :use (callst-shape a-stcall-parts (:instance g-callst-ok (dests nil))
                 (:instance callst-args-run (xs (cvs)))
                 (:instance c-sorc-necc (f (car x)) (xs (cdr x)) (cs (gca 2)) (fr (cfr1)) (ks (cks)))
                 (:instance a-call-ok-necc (f (car x)) (ks (cks)))
                 (:instance callst-glue (a (gca 1))
                            (c (list :call (g-sym (car x) nil) (append (g-scs (g-obj (car x) st) (cdr x) st) (gca 2))))
                            (fr1 (cfr1)) (h2 (put (okey o fr) (mv-nth 1 (a-call-val (car x) (cks) s)) heap)))))))
