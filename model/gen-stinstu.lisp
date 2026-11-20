; gen-stinstu: gst-callst-u's functional instance (GEN.md 4 (4a) (1)).
; a-stcall-u copied as a-stcall-u-h on gen-stdisch's ac-orc, and
; gen-stcallu's gst-callst-u instantiated as gen-stinst instantiates
; gst-callst: c-sorc and a-call-ok become c-sorc-h2/a-call-ok-h2, which
; tab-ok gives, so gst-callst-u-h has no oracle hypothesis past tab-ok.

(in-package "ACL2")

(include-book "gen-stinst")
(include-book "gen-stccallu")

(defun a-stcall-u-h (x env s st defs n tab st0 defs0 n0 o0)
  (mv-let (e ks) (a-sx-list (g-cvals (g-obj (car x) st) (cdr x) st) env s st defs n)
    (if e (mv e s nil)
      (mv-let (e s1) (a-sacts (g-obj (car x) st) (cdr x) env s st defs n)
        (if e (mv e s nil) (ac-orc (car x) ks s1 tab st0 defs0 n0 o0))))))

(in-theory (disable a-stcall-u-h))

(defthm gst-callst-u-generic
  (implies (and (eq (g-role (car x) st) :sub) (g-upd (g-obj (car x) st) (cdr x) st)
                (not (car (g-callst x em cnt locs sigs fnames st nil)))
                (not (car (a-stcall-u-h x env s st defs n tab0 st0 defs0 n0 o0))) (c-sorc-h2 o st tab0 st0 defs0 n0 o0) (a-call-ok-h2 st o tab0 st0 defs0 n0 o0)
                (no-calls :list (cdr x) sigs nil) (em-ok em env fr)
                (decl-ok (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
                (gsc-sem (g-obj (car x) st) (cdr x) em (cu-s 3) (cu-s 4) sigs fnames st env s defs n (cufr1) heap o)
                (stan-ok (g-obj (car x) st) (cdr x) em (cu-s 3) (cu-s 4) sigs fnames st))
           (and (equal (car (sxc-list-h (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap tab0 st0 defs0 n0 o0)) :normal)
                (equal (mv-nth 2 (sxc-list-h (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap tab0 st0 defs0 n0 o0))
                       (put (okey o fr) (mv-nth 1 (a-stcall-u-h x env s st defs n tab0 st0 defs0 n0 o0)) heap))
                (st-ok st o (mv-nth 1 (a-stcall-u-h x env s st defs n tab0 st0 defs0 n0 o0)))
                (st-wf st (mv-nth 1 (a-stcall-u-h x env s st defs n tab0 st0 defs0 n0 o0)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable sc-orc ac-orc c-sorc-h2 a-call-ok-h2 sxc-h sxc-list-h a-stcall-u-h g-callst g-role st-ok st-wf
                               gsc-sem stan-ok)
           :use ((:functional-instance gst-callst-u
                  (s-call-val (lambda (name args fr heap) (sc-orc name args fr heap tab0 st0 defs0 n0 o0)))
                  (sxc (lambda (x frame heap) (sxc-h x frame heap tab0 st0 defs0 n0 o0)))
                  (sxc-list (lambda (ss frame heap) (sxc-list-h ss frame heap tab0 st0 defs0 n0 o0)))
                  (a-call-val (lambda (f ks s) (ac-orc f ks s tab0 st0 defs0 n0 o0)))
                  (a-stcall-u (lambda (x env s st defs n) (a-stcall-u-h x env s st defs n tab0 st0 defs0 n0 o0)))
                  (c-sorc (lambda (o st) (c-sorc-h2 o st tab0 st0 defs0 n0 o0)))
                  (c-sorc-witness (lambda (o st) (c-sorc-h2-witness o st tab0 st0 defs0 n0 o0)))
                  (a-call-ok (lambda (st o) (a-call-ok-h2 st o tab0 st0 defs0 n0 o0)))
                  (a-call-ok-witness (lambda (st o) (a-call-ok-h2-witness st o tab0 st0 defs0 n0 o0))))))
          (stinst-hint id clause '(g-callst) '(c-sorc-h2-witness a-call-ok-h2-witness) '(c-sorc-h2 a-call-ok-h2)
           '(:in-theory (union-theories '(c-sorc-h2 a-call-ok-h2 kadr kaddr kadddr g-obj (:type-prescription st-ok) (:type-prescription st-wf)) (theory 'minimal-theory)))
           '(:in-theory (union-theories '(kadr kaddr kadddr g-obj) (theory 'minimal-theory))
             :use ((:instance c-sorc-h2-necc (tab tab0) (defs defs0) (n n0))
                   (:instance a-call-ok-h2-necc (tab tab0) (defs defs0) (n n0))))
           '(:in-theory (disable sc-orc ac-orc sxc-h sxc-list-h a-stcall-u-h)
             :expand ((:free (x frame heap) (sxc-h x frame heap tab0 st0 defs0 n0 o0))
                      (:free (ss frame heap) (sxc-list-h ss frame heap tab0 st0 defs0 n0 o0))
                      (:free (x env s st defs n) (a-stcall-u-h x env s st defs n tab0 st0 defs0 n0 o0)))))))

; gst-callst-u with no oracle hypothesis: for a table with tab-ok
(defthm gst-callst-u-h
  (implies (and (tab-ok tab gdefs tsigs st defs procs o b)
                (eq (g-role (car x) st) :sub) (g-upd (g-obj (car x) st) (cdr x) st)
                (not (car (g-callst x em cnt locs sigs fnames st nil)))
                (not (car (a-stcall-u-h x env s st defs n tab st defs n o)))  
                (no-calls :list (cdr x) sigs nil) (em-ok em env fr)
                (decl-ok (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
                (gsc-sem (g-obj (car x) st) (cdr x) em (cu-s 3) (cu-s 4) sigs fnames st env s defs n (cufr1) heap o)
                (stan-ok (g-obj (car x) st) (cdr x) em (cu-s 3) (cu-s 4) sigs fnames st))
           (and (equal (car (sxc-list-h (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap tab st defs n o)) :normal)
                (equal (mv-nth 2 (sxc-list-h (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap tab st defs n o))
                       (put (okey o fr) (mv-nth 1 (a-stcall-u-h x env s st defs n tab st defs n o)) heap))
                (st-ok st o (mv-nth 1 (a-stcall-u-h x env s st defs n tab st defs n o)))
                (st-wf st (mv-nth 1 (a-stcall-u-h x env s st defs n tab st defs n o)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable tab-ok c-sorc-h a-call-ok-h c-sorc-h2 a-call-ok-h2 c-sorc-h-holds a-call-ok-h-holds
                               sxc-list-h a-stcall-u-h g-callst gsc-sem stan-ok)
           :use ((:instance c-sorc-h-holds (sigs tsigs)) (:instance a-call-ok-h-holds (sigs tsigs))
                 (:instance c-sorc-h2-from-h (o0 o)) (:instance a-call-ok-h2-from-h (o0 o))
                 (:instance gst-callst-u-generic (tab0 tab) (st0 st) (defs0 defs) (n0 n) (o0 o))))))
