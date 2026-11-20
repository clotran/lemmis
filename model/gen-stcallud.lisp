; gen-stcallud: g-callst's CALL with updated stobj arguments and OUT results
; (GEN.md 4 (4a) (2b), last piece): gst-callst-u with dests, as gen-stcalld's
; gst-callst-d is gst-callst with dests. The dests are appended to the CALL's
; arguments after the settled codes; c-sorc-d answers the CALL, the frame put
; to a-call-val's value results (g-rvals). Everything before the CALL is
; gen-stcallu's (its facts are stated for dests nil; g-callst's error, temporaries
; and locals do not depend on dests: g-callst-dests).

(in-package "ACL2")

(include-book "gen-stcallu")
(include-book "gen-stcalld")

(defthm g-callst-dests
  (and (equal (mv-nth 0 (g-callst x em cnt locs sigs fnames st dests)) (mv-nth 0 (g-callst x em cnt locs sigs fnames st nil)))
       (equal (mv-nth 3 (g-callst x em cnt locs sigs fnames st dests)) (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil))))
  :hints (("Goal" :in-theory (disable g-scall-args g-settle g-sacts g-flat g-upd)
           :expand ((g-callst x em cnt locs sigs fnames st dests) (g-callst x em cnt locs sigs fnames st nil)))))

(defmacro cu-call-d () '(list :call (g-sym (car x) nil) (append (g-scs (g-obj (car x) st) (cdr x) st) (cu-s 2) dests)))

(defthm callu-shape-d
  (implies (and (not (car (g-callst x em cnt locs sigs fnames st nil))) (g-upd (g-obj (car x) st) (cdr x) st) (true-listp dests))
           (equal (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) (append (cu-s 1) (cu-a 1) (list (cu-call-d)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-sargs g-scall-args g-settle g-sacts g-scall-args-is-g-sargs g-scall-args-sss g-cvals g-scs g-upd
                               g-sss g-callst-dests)
           :expand ((g-callst x em cnt locs sigs fnames st dests))
           :use ((:instance g-callst-ok (dests nil))
                 (:instance g-scall-args-is-g-sargs (formals (g-obj (car x) st)) (xs (cdr x)))
                 (:instance g-scall-args-sss (formals (g-obj (car x) st)) (xs (cdr x)))))))

(defthm a-stcall-u-rs
  (implies (not (car (a-stcall-u x env s st defs n)))
           (equal (mv-nth 2 (a-stcall-u x env s st defs n)) (mv-nth 2 (a-call-val (car x) (cuks) (cus1)))))
  :rule-classes nil)

(defmacro cufrd () '(put-dests dests (g-rvals (g-comp (car x) st) (mv-nth 2 (a-call-val (car x) (cuks) (cus1)))) (cufr2)))

(defthm gst-callst-u-d-core
  (implies (and (cuctx) (c-sorc-d o st) (true-listp dests) (dests-ok dests fr))
           (and (equal (car (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap)) :normal)
                (equal (mv-nth 1 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap))
                       (put-dests dests (g-rvals (g-comp (car x) st) (mv-nth 2 (a-stcall-u x env s st defs n))) (cufr2)))
                (equal (mv-nth 2 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap))
                       (put (okey o fr) (mv-nth 1 (a-stcall-u x env s st defs n)) heap))
                (st-ok st o (mv-nth 1 (a-stcall-u x env s st defs n)))
                (st-wf st (mv-nth 1 (a-stcall-u x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy cu-eq kar kdr kadr kaddr car-cons cdr-cons mv-nth-cons-k (equal) (consp)
                                                    (posp) (binary-+) (unary--) dests-ok-after-sx)
           :use (cu-0 cu-shape cu-run1 cu-run2 a-stcall-u-rs
                 (:instance callu-shape-d)
                 (:instance c-sorc-d-necc (f (car x)) (xs (cdr x)) (cs (cu-s 2)) (ds dests) (fr (cufr2)) (heap (cuh2))
                            (ks (cuks)) (s (cus1)))
                 (:instance a-call-ok-necc (f (car x)) (ks (cuks)) (s (cus1)))
                 (:instance callu-glue (a (cu-s 1)) (b (cu-a 1)) (c (cu-call-d)) (fr3 (cufrd))
                            (h3 (put (okey o (cufr2)) (mv-nth 1 (a-call-val (car x) (cuks) (cus1))) (cuh2))))
                 (:instance put-put-okey (k1 (okey o (cufr2))) (k (okey o fr)) (v (mv-nth 1 (a-call-val (car x) (cuks) (cus1))))
                            (w (cus1)) (h heap))))))

; gst-callst-u with dests: c-sorc-d for the CALL (c-sorc stays a hypothesis
; through callu-hyps; both are discharged on a table, c-sorc by gen-stdisch)
(defthm gst-callst-u-d
  (implies (and (callu-hyps) (c-sorc-d o st) (true-listp dests) (dests-ok dests fr))
           (and (equal (car (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap)) :normal)
                (equal (mv-nth 1 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap))
                       (put-dests dests (g-rvals (g-comp (car x) st) (mv-nth 2 (a-stcall-u x env s st defs n))) (cufr2)))
                (equal (mv-nth 2 (sxc-list (mv-nth 1 (g-callst x em cnt locs sigs fnames st dests)) fr heap))
                       (put (okey o fr) (mv-nth 1 (a-stcall-u x env s st defs n)) heap))
                (st-ok st o (mv-nth 1 (a-stcall-u x env s st defs n)))
                (st-wf st (mv-nth 1 (a-stcall-u x env s st defs n)))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy cu-ctxp) :use gst-callst-u-d-core)))
