; gen-stcalld: g-callst's CALL with OUT results (GEN.md 4 (4a) (2), first
; piece). The dests (the caller's int64 variables for f's value results, in
; order) are appended to the CALL's arguments; c-sorc-d is c-sorc with
; them: the Fortran oracle s-call-val answers the CALL by putting each dest
; to the matching value result of a-call-val (g-rvals: rs at the value
; outs), the heap's entry put to S'. gst-callst-d: gst-callst with dests
; (no stobj argument an update), the frame answered exactly.

(in-package "ACL2")

(include-book "gen-stcallst")

; rs's values at the value outs (nil outs), in order
(defun g-rvals (outs rs)
  (cond ((atom outs) nil)
        ((car outs) (g-rvals (cdr outs) (cdr rs)))
        (t (cons (car rs) (g-rvals (cdr outs) (cdr rs))))))

; each dest an int64 variable of the frame
(defun dests-ok (ds fr)
  (if (atom ds) t
    (and (equal (car ds) (list :var (kadr (car ds)))) (equal (dty (kadr (car ds)) fr) '(:int64))
         (dests-ok (cdr ds) fr))))

; the frame with each dest put to its value
(defun put-dests (ds vs fr)
  (if (or (atom ds) (atom vs)) fr
    (put-dests (cdr ds) (cdr vs) (put (kadr (car ds)) (cons :int64 (car vs)) fr))))

(defthm dests-ok-after-sx
  (equal (dests-ok ds (mv-nth 1 (sx-list s fr heap))) (dests-ok ds fr))
  :hints (("Goal" :induct (len ds) :in-theory (disable sx-list))))

; the Fortran oracle answers the emitted CALL, dests appended, as the source's does
(defun-sk c-sorc-d (o st)
  (forall (f xs cs ds fr heap ks s)
    (implies (and (eq (g-role f st) :sub) (equal (len xs) (len (g-obj f st))) (obj-at o s fr heap) (svs-is cs ks fr heap) (int64s ks)
                  (dests-ok ds fr) (not (mv-nth 0 (a-call-val f ks s))))
             (equal (s-call-val (g-sym f nil) (append (g-scs (g-obj f st) xs st) cs ds) fr heap)
                    (list nil (put-dests ds (g-rvals (g-comp f st) (mv-nth 2 (a-call-val f ks s))) fr)
                          (put (okey o fr) (mv-nth 1 (a-call-val f ks s)) heap))))))

(in-theory (disable c-sorc-d))

; g-callst with dests, no stobj argument an update
(defthm g-callst-noupd-d
  (implies (and (consp x) (true-listp x) (= (len (g-obj (car x) st)) (len (cdr x)))
                (not (g-upd (g-obj (car x) st) (cdr x) st))
                (not (mv-nth 0 (g-scall-args (g-obj (car x) st) (cdr x) t em cnt locs sigs fnames st))))
           (equal (g-callst x em cnt locs sigs fnames st dests)
                  (list nil
                        (append (gca 1)
                                (list (list :call (g-sym (car x) nil)
                                            (append (g-scs (g-obj (car x) st) (cdr x) st) (gca 2) (true-list-fix dests)))))
                        (gca 4) (gca 5))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-scall-args g-sargs g-sacts g-scall-args-is-g-sargs g-scall-args-true-list)
           :use ((:instance g-scall-args-is-g-sargs (formals (g-obj (car x) st)) (xs (cdr x)))
                 (:instance g-scall-args-true-list (formals (g-obj (car x) st)) (xs (cdr x)) (upd t)))
           :expand ((g-callst x em cnt locs sigs fnames st dests)))))

(defthm callst-shape-d
  (implies (and (not (car (g-callst x em cnt locs sigs fnames st dests))) (not (g-upd (g-obj (car x) st) (cdr x) st))
                (true-listp dests))
           (and (equal (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests))
                       (append (gca 1) (list (list :call (g-sym (car x) nil)
                                                   (append (g-scs (g-obj (car x) st) (cdr x) st) (gca 2) dests)))))
                (equal (mv-nth 3 (g-callst x em cnt locs sigs fnames st dests)) (gca 5))
                (not (car (g-sargs (cvs) em cnt locs sigs fnames st)))
                (all-int64-ty (gca 3))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-callst g-sargs g-scall-args g-scall-args-is-g-sargs g-cvals g-scs g-upd)
           :use ((:instance g-callst-ok)
                 g-callst-noupd-d
                 (:instance g-scall-args-is-g-sargs (formals (g-obj (car x) st)) (xs (cdr x)))))))

(defthm a-stcall-parts-d
  (implies (not (car (a-stcall x env s st defs n)))
           (and (not (car (a-sx-list (cvs) env s st defs n)))
                (not (car (a-call-val (car x) (cks) s)))
                (equal (mv-nth 1 (a-stcall x env s st defs n)) (mv-nth 1 (a-call-val (car x) (cks) s)))
                (equal (mv-nth 2 (a-stcall x env s st defs n)) (mv-nth 2 (a-call-val (car x) (cks) s)))))
  :rule-classes nil)

(defthm gst-callst-d
  (implies (and (eq (g-role (car x) st) :sub) (not (g-upd (g-obj (car x) st) (cdr x) st))
                (not (car (g-callst x em cnt locs sigs fnames st dests)))
                (not (car (a-stcall x env s st defs n))) (c-sorc-d o st) (a-call-ok st o)
                (true-listp dests) (dests-ok dests fr)
                (no-calls :list (cvs) sigs nil) (em-ok em env fr)
                (decl-ok (mv-nth 3 (g-callst x em cnt locs sigs fnames st dests)) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st))
           (and (equal (car (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap)) :normal)
                (equal (mv-nth 1 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap))
                       (put-dests dests (g-rvals (g-comp (car x) st) (mv-nth 2 (a-stcall x env s st defs n))) (cfr1)))
                (equal (mv-nth 2 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap))
                       (put (okey o fr) (mv-nth 1 (a-stcall x env s st defs n)) heap))
                (st-ok st o (mv-nth 1 (a-stcall x env s st defs n)))
                (st-wf st (mv-nth 1 (a-stcall x env s st defs n)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable a-stcall g-role g-callst g-sargs a-sx-list sx-list sxc-list obj-at okey st-ok st-wf
                               no-calls em-ok decl-ok g-cvals g-scs g-sym svs-is put lkp g-upd g-obj dests-ok put-dests g-rvals
                               c-sorc-d-necc a-call-ok-necc callst-glue)
           :use (callst-shape-d a-stcall-parts-d (:instance g-callst-ok)
                 (:instance callst-args-run (xs (cvs)))
                 (:instance dests-ok-after-sx (ds dests) (s (gca 1)))
                 (:instance c-sorc-d-necc (f (car x)) (xs (cdr x)) (cs (gca 2)) (ds dests) (fr (cfr1)) (ks (cks)))
                 (:instance a-call-ok-necc (f (car x)) (ks (cks)))
                 (:instance callst-glue (a (gca 1))
                            (c (list :call (g-sym (car x) nil) (append (g-scs (g-obj (car x) st) (cdr x) st) (gca 2) dests)))
                            (fr1 (put-dests dests (g-rvals (g-comp (car x) st) (mv-nth 2 (a-call-val (car x) (cks) s))) (cfr1)))
                            (h2 (put (okey o fr) (mv-nth 1 (a-call-val (car x) (cks) s)) heap)))))))
