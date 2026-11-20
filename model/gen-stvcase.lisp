; gen-stvcase: gstv-sem's leaf, tuple and :sub call cases (GEN.md 4 (4a) (2b)).

(in-package "ACL2")

(include-book "gen-stv")

; ---- the leaves: the stobj, a field or element update (vs nil, dests nil)

(defthm errstp-normal (not (errstp :normal)) :hints (("Goal" :in-theory (enable errstp))))

(defthm svs-is-nil (svs-is nil nil fr h))

(defthm gstv-leaf-nil
  (implies (and (sn-hyps) (em-nostobj em st) (st-plain :term x nil st) (no-calls :term x sigs nil)
                (not (and (consp x) (eq (car x) 'cons)))
                (or (atom x) (eq (g-role (car x) st) :set) (eq (g-role (car x) st) :seti)))
           (and (gstv-sem x em cnt locs sigs fnames st outs nil env s defs n fr heap o)
                (stv-grow x em cnt locs sigs fnames st outs nil)))
  :hints (("Goal" :do-not-induct t
           :expand ((gstv-sem x em cnt locs sigs fnames st outs nil env s defs n fr heap o)
                    (stv-grow x em cnt locs sigs fnames st outs nil))
           :in-theory (union-theories '(a-stv-leaf errstp-normal svs-is-nil mv-nth-0-car mv-nth-cons-k car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (gst-sem-holds stn-ok-holds gst-sem-use stn-ok-use
                 (:instance sxc-list-is-sx-list (ss (mv-nth 1 (g-stmt x em cnt locs sigs fnames st outs nil nil))))))))

(defthm len-0-true-listp (implies (and (true-listp d) (equal (len d) 0)) (equal d nil)) :rule-classes nil)

(defthm gstv-dests-arity
  (implies (and (equal (nvals outs) 0) dests)
           (and (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
                (stv-grow x em cnt locs sigs fnames st outs dests)))
  :hints (("Goal" :do-not-induct t :expand ((gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
                                            (stv-grow x em cnt locs sigs fnames st outs dests))
           :in-theory (theory 'minimal-theory) :use ((:instance len-0-true-listp (d dests))))))

(defthm gstv-leaf
  (implies (and (sn-hyps) (em-nostobj em st) (st-plain :term x nil st) (no-calls :term x sigs nil) (equal (nvals outs) 0)
                (not (and (consp x) (eq (car x) 'cons)))
                (or (atom x) (eq (g-role (car x) st) :set) (eq (g-role (car x) st) :seti)))
           (and (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
                (stv-grow x em cnt locs sigs fnames st outs dests)))
  :hints (("Goal" :do-not-induct t :cases ((equal dests nil))
           :in-theory (union-theories '(gstv-leaf-nil gstv-dests-arity) (theory 'minimal-theory)))))

; ---- the tuple: gst-cons at one less fuel

(defthm cons-shape
  (implies (and (consp x) (true-listp x) (eq (car x) 'cons) (not (gvx 0)))
           (and (equal (len outs) (len (cmp))) (not (ct 0)) (not (csa 0)) (equal (gvx 3) (csa 3))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (e/d (g-stmt-cons) (g-tvals g-sacts g-conses g-moves g-stmt)))))

(defthm gstv-cons-sem
  (implies (and (consp x) (true-listp x) (eq (car x) 'cons) (sn-hyps) (em-nostobj em st)
                (st-plain :acts (g-conses x) outs st) (no-calls :list (g-conses x) sigs nil))
           (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((zp n))
           :expand ((gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
           :in-theory (union-theories '(a-stv-cons errstp-normal len-g-rvals mv-nth-0-car mv-nth-cons-k car-cons cdr-cons
                                        (equal) (zp) (binary-+) (unary--))
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance gst-cons (n (1- n)))
                 (:instance gst-sem-thm (flag :acts) (x (cmp)) (vars outs) (cnt (ct 3)) (locs (ct 4)) (n (1- n)) (fr (kf1)))
                 (:instance stan-ok-holds (vars outs) (xs (cmp)) (cnt (ct 3)) (locs (ct 4)))
                 (:instance sxc-list-is-sx-list (ss (gvx 1)))))))

(defthm gstv-cons-grow
  (implies (and (consp x) (true-listp x) (eq (car x) 'cons) (sn-hyps)
                (st-plain :acts (g-conses x) outs st) (no-calls :list (g-conses x) sigs nil))
           (stv-grow x em cnt locs sigs fnames st outs dests))
  :hints (("Goal" :do-not-induct t :expand ((stv-grow x em cnt locs sigs fnames st outs dests))
           :in-theory (union-theories '(subsetp-trans2 mv-nth-0-car mv-nth-cons-k car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (cons-shape
                 (:instance stan-ok-holds (vars outs) (xs (cmp)) (cnt (ct 3)) (locs (ct 4)))
                 (:instance stan-ok-use (vars outs) (xs (cmp)) (cnt (ct 3)) (locs (ct 4)))
                 (:instance tvn-thm (comps (cmp)) (tmp (cmv)))
                 (:instance tvn-ok-use (comps (cmp)) (tmp (cmv)))
                 (:instance no-calls-rvals (comps (cmp)))))))

(defthm gstv-cons
  (implies (and (consp x) (true-listp x) (eq (car x) 'cons) (sn-hyps) (em-nostobj em st)
                (st-plain :acts (g-conses x) outs st) (no-calls :list (g-conses x) sigs nil))
           (and (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
                (stv-grow x em cnt locs sigs fnames st outs dests)))
  :hints (("Goal" :in-theory (union-theories '(gstv-cons-sem gstv-cons-grow) (theory 'minimal-theory)))))

; ---- a :sub call: gst-callst-d / gst-callst-u-d at one less fuel, the dests
; then hold the value results

(defmacro gcx (k) `(mv-nth ,k (g-callst x em cnt locs sigs fnames st dests)))

(defthm sub-shape
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :sub) (not (g-role 'if st))
                (not (gvx 0)))
           (and (equal (g-comp (car x) st) outs) (not (gcx 0)) (equal (gvx 1) (gcx 1)) (equal (gvx 3) (gcx 3))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(g-stmt-sub-d) (theory 'minimal-theory)))))

(defthm g-callst-dests-r
  (implies (syntaxp (not (equal dests ''nil)))
           (and (equal (car (g-callst x em cnt locs sigs fnames st dests)) (car (g-callst x em cnt locs sigs fnames st nil)))
                (equal (mv-nth 3 (g-callst x em cnt locs sigs fnames st dests)) (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)))))
  :hints (("Goal" :in-theory (union-theories '(mv-nth-0-car) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use g-callst-dests)))

(defthm g-callst-locs-noupd
  (implies (and (not (g-upd (g-obj (car x) st) (cdr x) st)) (not (car (g-callst x em cnt locs sigs fnames st nil))))
           (equal (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) (gca 5)))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-callst g-scall-args g-sargs g-sacts g-upd g-cvals)
           :use ((:instance g-callst-ok (dests nil)) g-callst-noupd))))

(defthm g-callst-locs-upd
  (implies (and (g-upd (g-obj (car x) st) (cdr x) st) (not (car (g-callst x em cnt locs sigs fnames st nil))))
           (equal (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) (cu-a 3)))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory) :use callu-shape)))

(defthm g-callst-grow
  (implies (and (consp x) (sn-hyps) (eq (g-role (car x) st) :sub)
                (no-calls :list (g-cvals (g-obj (car x) st) (cdr x) st) sigs nil)
                (st-plain :acts (cdr x) (g-obj (car x) st) st) (no-calls :list (cdr x) sigs nil)
                (not (gcx 0)))
           (subsetp-equal locs (gcx 3)))
  :hints (("Goal" :do-not-induct t :cases ((g-upd (g-obj (car x) st) (cdr x) st))
           :in-theory (union-theories '(subsetp-trans2 g-callst-dests-r g-callst-locs-noupd g-callst-locs-upd mv-nth-0-car)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance g-callst-ok (dests nil))
                 (:instance callu-shape)
                 (:instance g-scall-args-is-g-sargs (formals (g-obj (car x) st)) (xs (cdr x)))
                 (:instance sna-ok-holds (xs (cvs)))
                 (:instance sna-ok-use (xs (cvs)))
                 (:instance g-settle-locs (sss (g-sss (cvs) em cnt locs sigs fnames st)) (cs (gca 2)) (cnt (gca 4)) (locs (gca 5))
                            (used (used)))
                 (:instance stan-ok-holds (vars (g-obj (car x) st)) (xs (cdr x)) (cnt (cu-s 3)) (locs (cu-s 4)))
                 (:instance stan-ok-use (vars (g-obj (car x) st)) (xs (cdr x)) (cnt (cu-s 3)) (locs (cu-s 4)))))))

(defmacro sub-hyps ()
  '(and (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :sub) (sn-hyps) (em-nostobj em st)
        (no-calls :list (cdr x) sigs nil) (no-calls :list (g-cvals (g-obj (car x) st) (cdr x) st) sigs nil)
        (st-plain :acts (cdr x) (g-obj (car x) st) st)))

(defthm gstv-sub-noupd
  (implies (and (sub-hyps) (not (g-upd (g-obj (car x) st) (cdr x) st)))
           (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((zp n))
           :expand ((gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
           :in-theory (union-theories '(gstv-sem a-stv-sub errstp-normal len-g-rvals mv-nth-0-car mv-nth-cons-k car-cons cdr-cons
                                        (equal) (zp) (binary-+) (unary--))
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (sub-shape
                 (:instance gst-callst-d (n (1- n)))
                 (:instance dests-ok-after-sx (ds dests) (s (gca 1)))
                 (:instance svs-is-put-dests (ds dests) (fr (cfr1)) (h (put (okey o fr) (mv-nth 1 (a-stcall x env s st defs (1- n))) heap))
                            (vs (g-rvals outs (mv-nth 2 (a-stcall x env s st defs (1- n))))))))))

(defthm gstv-sub-upd
  (implies (and (sub-hyps) (g-upd (g-obj (car x) st) (cdr x) st))
           (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((zp n))
           :expand ((gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o))
           :in-theory (union-theories '(gstv-sem a-stv-sub errstp-normal len-g-rvals mv-nth-0-car mv-nth-cons-k car-cons cdr-cons
                                        (equal) (zp) (binary-+) (unary--))
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (sub-shape g-callst-dests
                 (:instance gst-callst-u-d (n (1- n)))
                 (:instance gst-sem-thm (flag :acts) (x (cdr x)) (vars (g-obj (car x) st)) (cnt (cu-s 3)) (locs (cu-s 4))
                            (n (1- n)) (fr (cufr1)))
                 (:instance stan-ok-holds (vars (g-obj (car x) st)) (xs (cdr x)) (cnt (cu-s 3)) (locs (cu-s 4)))
                 (:instance dests-ok-after-sx (ds dests) (s (cu-a 1)) (fr (cufr1)))
                 (:instance dests-ok-after-sx (ds dests) (s (cu-s 1)))
                 (:instance svs-is-put-dests (ds dests) (fr (cufr2)) (h (put (okey o fr) (mv-nth 1 (a-stcall-u x env s st defs (1- n))) heap))
                            (vs (g-rvals outs (mv-nth 2 (a-stcall-u x env s st defs (1- n))))))))))

(defthm gstv-sub
  (implies (sub-hyps)
           (and (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
                (stv-grow x em cnt locs sigs fnames st outs dests)))
  :hints (("Goal" :do-not-induct t :cases ((g-upd (g-obj (car x) st) (cdr x) st))
           :in-theory (union-theories '(stv-grow gstv-sub-noupd gstv-sub-upd mv-nth-0-car mv-nth-cons-k)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (sub-shape g-callst-grow))))
