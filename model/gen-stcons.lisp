; gen-stcons: g-stmt's cons case (GEN.md 4 (4a) (2b)). The tuple of a
; function's results: its value components to the dests (g-tvals), then the
; stobj components' updates (g-sacts outs comps), then -- when a stobj result
; is moved (g-moves) -- the dests from the "r" temporaries the values went
; through, read before the updates. The source: the value components by
; a-sx-list on S (g-rvals outs comps), S' by a-sacts of the stobj ones.
;
; tv-thm (g-tvals run, gen-stsettle's stu-ind/stu-thm recipe): the
; statements answer :normal, the heap unchanged, and the dests (directly) or
; the r temporaries (tmp) answer the values. tvn-thm: its names.

(in-package "ACL2")

(include-book "gen-stcallu")
(include-book "gen-stcalld")

(defun dnames (ds) (if (atom ds) nil (cons (kadr (car ds)) (dnames (cdr ds)))))
(defun asn-rhs (as) (if (atom as) nil (cons (kaddr (car as)) (asn-rhs (cdr as)))))
(defun asn-gen (ds rs) (if (or (atom ds) (atom rs)) nil (cons (list :assign (car ds) (car rs)) (asn-gen (cdr ds) (cdr rs)))))

(defthm g-rvals-skip
  (implies (and (consp outs) (car outs)) (equal (g-rvals outs comps) (g-rvals (cdr outs) (cdr comps)))))
(defthm g-rvals-val
  (implies (and (consp outs) (not (car outs)))
           (equal (g-rvals outs comps) (cons (car comps) (g-rvals (cdr outs) (cdr comps))))))
(defthm g-rvals-atom (implies (atom outs) (equal (g-rvals outs comps) nil)))
(in-theory (disable g-rvals))

(defthm dests-ok-put-int
  (implies (dests-ok ds fr) (dests-ok ds (put k (cons :int64 v) fr)))
  :hints (("Goal" :induct (len ds) :in-theory (disable put))))

; ---- g-tvals' shape

(defmacro tvused () '(append fnames (em-names em)))
(defmacro tvg (k) `(mv-nth ,k (g-tvals outs comps dests tmp em cnt locs sigs fnames st)))
(defmacro t1 (k) `(mv-nth ,k (g-sexpr (car comps) em cnt locs sigs fnames st)))
(defmacro trv () '(g-tmp 'r (1+ (nfix (t1 4)))))
(defmacro trl () '(cons (cons (trv) :int64) (true-list-fix (t1 5))))
(defmacro tw (k) `(mv-nth ,k (g-tvals (cdr outs) (cdr comps) (cdr dests) tmp em (1+ (nfix (t1 4))) (trl) sigs fnames st)))
(defmacro tn (k) `(mv-nth ,k (g-tvals (cdr outs) (cdr comps) (cdr dests) tmp em (t1 4) (t1 5) sigs fnames st)))

(defthm g-tvals-atom
  (implies (or (atom outs) (atom comps)) (equal (g-tvals outs comps dests tmp em cnt locs sigs fnames st) (list nil nil nil cnt locs)))
  :hints (("Goal" :expand ((g-tvals outs comps dests tmp em cnt locs sigs fnames st)))))

(defthm g-tvals-skip
  (implies (and (consp outs) (consp comps) (car outs))
           (equal (g-tvals outs comps dests tmp em cnt locs sigs fnames st)
                  (g-tvals (cdr outs) (cdr comps) dests tmp em cnt locs sigs fnames st)))
  :hints (("Goal" :in-theory (disable g-sexpr g-fresh) :expand ((g-tvals outs comps dests tmp em cnt locs sigs fnames st)))))

(defthm tv-shape-tmp
  (implies (and (consp outs) (consp comps) (not (car outs)) tmp (not (tvg 0)))
           (and (not (t1 0)) (equal (t1 3) :int64) (consp dests) (not (tw 0))
                (not (car (g-fresh 'r :int64 (t1 4) (t1 5) (tvused))))
                (equal (tvg 1) (append (t1 1) (list (list :assign (list :var (trv)) (t1 2))) (tw 1)))
                (equal (tvg 2) (cons (list :assign (car dests) (list :var (trv))) (tw 2)))
                (equal (tvg 4) (tw 4))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable g-sexpr g-fresh g-tmp)
           :expand ((g-tvals outs comps dests tmp em cnt locs sigs fnames st))
           :use ((:instance g-fresh-out (b 'r) (ty :int64) (cnt (t1 4)) (locs (t1 5)) (used (tvused)))))))

(defthm tv-shape-dir
  (implies (and (consp outs) (consp comps) (not (car outs)) (not tmp) (not (tvg 0)))
           (and (not (t1 0)) (equal (t1 3) :int64) (consp dests) (not (tn 0))
                (equal (tvg 1) (append (t1 1) (list (list :assign (car dests) (t1 2))) (tn 1)))
                (equal (tvg 2) nil)
                (equal (tvg 4) (tn 4))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable g-sexpr g-fresh g-tmp)
           :expand ((g-tvals outs comps dests tmp em cnt locs sigs fnames st)))))

; ---- its names: the statements assign the new temporaries and (directly) the dests

(defun tvn-ok (outs comps dests tmp em cnt locs sigs fnames st)
  (mv-let (e ss as cnt2 locs2) (g-tvals outs comps dests tmp em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (implies (not e)
             (and (subsetp-equal locs locs2)
                  (subsetp-equal (asg :list ss) (if tmp (strip-cars locs2) (append (strip-cars locs2) (dnames dests))))
                  (implies (or tmp (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars locs2)))))
                           (not (intersectp-equal (asg :list ss) (append fnames (em-names em) (strip-cars locs)))))
                  (implies tmp (and (stables (asn-rhs as))
                                    (subsetp-equal (svs-names (asn-rhs as)) (strip-cars locs2))
                                    (not (intersectp-equal (svs-names (asn-rhs as)) (append fnames (em-names em) (strip-cars locs))))
                                    (implies (equal (len dests) (len (g-rvals outs comps)))
                                             (equal as (asn-gen dests (asn-rhs as))))))
                  (implies (not tmp) (equal as nil))))))

(defun-nx tv-ind (outs comps dests tmp em cnt locs sigs fnames st)
  (declare (xargs :measure (acl2-count comps)))
  (cond ((or (atom outs) (atom comps)) t)
        ((car outs) (tv-ind (cdr outs) (cdr comps) dests tmp em cnt locs sigs fnames st))
        (tmp (tv-ind (cdr outs) (cdr comps) (cdr dests) tmp em (1+ (nfix (t1 4))) (trl) sigs fnames st))
        (t (tv-ind (cdr outs) (cdr comps) (cdr dests) tmp em (t1 4) (t1 5) sigs fnames st))))

(defmacro tvn-dis ()
  ''(g-sexpr g-tvals g-fresh g-tmp sn-ok tvn-ok g-sargs g-stable stables svs-names asg asn-rhs asn-gen dnames em-names
     g-rvals sn-ok-holds g-used))

(defthm tvn-ok-use
  (implies (and (tvn-ok outs comps dests tmp em cnt locs sigs fnames st) (not (tvg 0)))
           (and (subsetp-equal locs (tvg 4))
                (subsetp-equal (asg :list (tvg 1)) (if tmp (strip-cars (tvg 4)) (append (strip-cars (tvg 4)) (dnames dests))))
                (implies (or tmp (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars (tvg 4))))))
                         (not (intersectp-equal (asg :list (tvg 1)) (append fnames (em-names em) (strip-cars locs)))))
                (implies tmp (and (stables (asn-rhs (tvg 2)))
                                  (subsetp-equal (svs-names (asn-rhs (tvg 2))) (strip-cars (tvg 4)))
                                  (not (intersectp-equal (svs-names (asn-rhs (tvg 2))) (append fnames (em-names em) (strip-cars locs))))
                                  (implies (equal (len dests) (len (g-rvals outs comps)))
                                           (equal (tvg 2) (asn-gen dests (asn-rhs (tvg 2)))))))
                (implies (not tmp) (equal (tvg 2) nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable g-tvals))))

(defthm tvn-atom
  (implies (or (atom outs) (atom comps)) (tvn-ok outs comps dests tmp em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (disable g-rvals-atom) :use g-rvals-atom
           :expand ((asg :list nil) (asn-rhs nil) (stables nil) (svs-names nil)))))

(defthm tvn-skip
  (implies (and (consp outs) (consp comps) (car outs) (tvn-ok (cdr outs) (cdr comps) dests tmp em cnt locs sigs fnames st))
           (tvn-ok outs comps dests tmp em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (mthy tvn-ok g-tvals-skip g-rvals-skip))))

; the set reasoning of a value component, abstractly
(defthm tvn-tmp-abs
  (implies (and (subsetp-equal lc l1c) (subsetp-equal l1c l2c) (member-equal r (strip-cars l2c))
                (subsetp-equal (strip-cars lc) (strip-cars l1c))
                (subsetp-equal a1 (strip-cars l1c)) (not (intersectp-equal a1 (append f e (strip-cars lc))))
                (not (member-equal r f)) (not (member-equal r e)) (not (member-equal r (strip-cars l1c)))
                (subsetp-equal ar (strip-cars l2c)) (not (intersectp-equal ar (append f e (cons r (strip-cars l1c)))))
                (subsetp-equal nr (strip-cars l2c)) (not (intersectp-equal nr (append f e (cons r (strip-cars l1c))))))
           (and (subsetp-equal lc l2c)
                (subsetp-equal (append a1 (cons r ar)) (strip-cars l2c))
                (not (intersectp-equal (append a1 (cons r ar)) (append f e (strip-cars lc))))
                (subsetp-equal (append (append a1 (list r)) ar) (strip-cars l2c))
                (subsetp-equal (append a1 (append (list r) ar)) (strip-cars l2c))
                (not (intersectp-equal (append a1 (append (list r) ar)) (append f e (strip-cars lc))))
                (not (intersectp-equal (append (append a1 (list r)) ar) (append f e (strip-cars lc))))
                (subsetp-equal (append (list r) nr) (strip-cars l2c))
                (not (intersectp-equal (append (list r) nr) (append f e (strip-cars lc))))
                (subsetp-equal (cons r nr) (strip-cars l2c))
                (not (intersectp-equal (cons r nr) (append f e (strip-cars lc))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable subsetp-equal intersectp-equal))))

(defthm tvn-dir-abs
  (implies (and (subsetp-equal lc l1c) (subsetp-equal l1c l2c) (subsetp-equal (strip-cars lc) (strip-cars l1c))
                (subsetp-equal (strip-cars l1c) (strip-cars l2c))
                (subsetp-equal a1 (strip-cars l1c)) (not (intersectp-equal a1 (append f e (strip-cars lc))))
                (subsetp-equal ar (append (strip-cars l2c) dn))
                (implies (not (intersectp-equal dn (append f e (strip-cars l2c))))
                         (not (intersectp-equal ar (append f e (strip-cars l1c))))))
           (and (subsetp-equal lc l2c)
                (subsetp-equal (append a1 (cons d ar)) (append (strip-cars l2c) (cons d dn)))
                (subsetp-equal (append a1 (append (list d) ar)) (append (strip-cars l2c) (cons d dn)))
                (implies (not (intersectp-equal (cons d dn) (append f e (strip-cars l2c))))
                         (and (not (intersectp-equal (append a1 (cons d ar)) (append f e (strip-cars lc))))
                              (not (intersectp-equal (append a1 (append (list d) ar)) (append f e (strip-cars lc))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable subsetp-equal intersectp-equal))))

(defthm tv-eq-tmp
  (implies (and (consp outs) (consp comps) (not (car outs)) tmp (not (tvg 0)))
           (and (equal (tvg 1) (append (t1 1) (list (list :assign (list :var (trv)) (t1 2))) (tw 1)))
                (equal (tvg 2) (cons (list :assign (car dests) (list :var (trv))) (tw 2)))
                (equal (tvg 4) (tw 4))))
  :hints (("Goal" :use tv-shape-tmp :in-theory (disable g-tvals g-sexpr g-tmp))))

(defthm tv-eq-dir
  (implies (and (consp outs) (consp comps) (not (car outs)) (not tmp) (not (tvg 0)))
           (and (equal (tvg 1) (append (t1 1) (list (list :assign (car dests) (t1 2))) (tn 1)))
                (equal (tvg 2) nil)
                (equal (tvg 4) (tn 4))))
  :hints (("Goal" :use tv-shape-dir :in-theory (disable g-tvals g-sexpr g-tmp))))
(in-theory (disable tv-eq-tmp tv-eq-dir))

(defthm plus-one-cancel (implies (and (natp a) (natp b)) (equal (equal (+ 1 a) (+ 1 b)) (equal a b))))

(defthm strip-cars-cons-pair (equal (strip-cars (cons (cons a b) l)) (cons a (strip-cars l))))

(defthm member-pair-strip-cars (implies (member-equal (cons a b) l) (member-equal a (strip-cars l))))
(defthm subsetp-cons-member (implies (subsetp-equal (cons a b) c) (member-equal a c)))

(defmacro tvn-hy (rest)
  `(and (consp outs) (consp comps) (not (car outs)) (sn-ok (car comps) em cnt locs sigs fnames st) ,rest))

; the facts of a value component's step, each a plain conjunct
(defthm tvn-tmp-facts
  (implies (and (tvn-hy (tvn-ok (cdr outs) (cdr comps) (cdr dests) tmp em (1+ (nfix (t1 4))) (trl) sigs fnames st)) tmp (not (tvg 0)))
           (and (consp dests) (not (tw 0))
                (subsetp-equal locs (t1 5)) (subsetp-equal (t1 5) (tw 4)) (subsetp-equal (trl) (tw 4))
                (member-equal (trv) (strip-cars (tw 4)))
                (subsetp-equal (strip-cars locs) (strip-cars (t1 5)))
                (subsetp-equal (asg :list (t1 1)) (strip-cars (t1 5)))
                (not (intersectp-equal (asg :list (t1 1)) (append fnames (em-names em) (strip-cars locs))))
                (not (member-equal (trv) fnames)) (not (member-equal (trv) (em-names em))) (not (member-equal (trv) (strip-cars (t1 5))))
                (subsetp-equal (asg :list (tw 1)) (strip-cars (tw 4)))
                (not (intersectp-equal (asg :list (tw 1)) (append fnames (em-names em) (cons (trv) (strip-cars (t1 5))))))
                (stables (asn-rhs (tw 2)))
                (subsetp-equal (svs-names (asn-rhs (tw 2))) (strip-cars (tw 4)))
                (not (intersectp-equal (svs-names (asn-rhs (tw 2))) (append fnames (em-names em) (cons (trv) (strip-cars (t1 5))))))
                (implies (equal (len (cdr dests)) (len (g-rvals (cdr outs) (cdr comps))))
                         (equal (tw 2) (asn-gen (cdr dests) (asn-rhs (tw 2)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (mthy strip-cars-cons-pair strip-cars-true-list-fix subsetp-cons-r subsetp-true-list-fix-r subsetp-refl
                            subsetp-trans2 member-append-eq intersectp-append-r tv-eq-tmp intersectp-cons-2 member-equal subsetp-equal)
           :use (tv-shape-tmp
                 (:instance sn-ok-use (x (car comps)))
                 (:instance tvn-ok-use (outs (cdr outs)) (comps (cdr comps)) (dests (cdr dests)) (cnt (1+ (nfix (t1 4)))) (locs (trl)))
                 (:instance g-fresh-out (b 'r) (ty :int64) (cnt (t1 4)) (locs (t1 5)) (used (tvused)))
                 (:instance subsetp-trans2 (a (t1 5)) (b (trl)) (c (tw 4)))
                 (:instance member-pair-strip-cars (a (trv)) (b :int64) (l (tw 4)))
                 (:instance subsetp-cons-member (a (cons (trv) :int64)) (b (true-list-fix (t1 5))) (c (tw 4)))
                 (:instance subsetp-strip-cars (a locs) (b (t1 5)))))))

(defthm tvn-tmp
  (implies (and (tvn-hy (tvn-ok (cdr outs) (cdr comps) (cdr dests) tmp em (1+ (nfix (t1 4))) (trl) sigs fnames st)) tmp)
           (tvn-ok outs comps dests tmp em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t
           :in-theory (mthy tvn-ok tv-eq-tmp asg-append asg-cons asg-assign-var asn-rhs asn-gen stables svs-names sv-names-var
                            g-stable-var kaddr kadr kar kdr car-cons cdr-cons g-rvals-val len plus-one-cancel natp (:type-prescription len) subsetp-trans2
                            subsetp-strip-cars strip-cars-cons-pair strip-cars-true-list-fix)
           :use (tvn-tmp-facts
                 (:instance tvn-tmp-abs (lc locs) (l1c (t1 5)) (l2c (tw 4)) (a1 (asg :list (t1 1))) (r (trv))
                            (f fnames) (e (em-names em)) (ar (asg :list (tw 1))) (nr (svs-names (asn-rhs (tw 2)))))))))

(defthm asg-assign-any (equal (asg :list (list (list :assign a c))) (list (kadr a)))
  :hints (("Goal" :expand ((asg :list (list (list :assign a c)))))))

(defthm tvn-dir-facts
  (implies (and (tvn-hy (tvn-ok (cdr outs) (cdr comps) (cdr dests) tmp em (t1 4) (t1 5) sigs fnames st)) (not tmp) (not (tvg 0)))
           (and (consp dests) (not (tn 0))
                (subsetp-equal locs (t1 5)) (subsetp-equal (t1 5) (tn 4))
                (subsetp-equal (strip-cars locs) (strip-cars (t1 5))) (subsetp-equal (strip-cars (t1 5)) (strip-cars (tn 4)))
                (subsetp-equal (asg :list (t1 1)) (strip-cars (t1 5)))
                (not (intersectp-equal (asg :list (t1 1)) (append fnames (em-names em) (strip-cars locs))))
                (subsetp-equal (asg :list (tn 1)) (append (strip-cars (tn 4)) (dnames (cdr dests))))
                (implies (not (intersectp-equal (dnames (cdr dests)) (append fnames (em-names em) (strip-cars (tn 4)))))
                         (not (intersectp-equal (asg :list (tn 1)) (append fnames (em-names em) (strip-cars (t1 5))))))
                (equal (tn 2) nil)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy intersectp-append-r tv-eq-dir)
           :use (tv-shape-dir
                 (:instance sn-ok-use (x (car comps)))
                 (:instance tvn-ok-use (outs (cdr outs)) (comps (cdr comps)) (dests (cdr dests)) (cnt (t1 4)) (locs (t1 5)))
                 (:instance subsetp-strip-cars (a locs) (b (t1 5)))
                 (:instance subsetp-strip-cars (a (t1 5)) (b (tn 4)))))))

(defthm tvn-dir
  (implies (and (tvn-hy (tvn-ok (cdr outs) (cdr comps) (cdr dests) tmp em (t1 4) (t1 5) sigs fnames st)) (not tmp))
           (tvn-ok outs comps dests tmp em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t
           :in-theory (mthy tvn-ok tv-eq-dir asg-append asg-assign-any dnames)
           :use (tvn-dir-facts
                 (:instance tvn-dir-abs (lc locs) (l1c (t1 5)) (l2c (tn 4)) (a1 (asg :list (t1 1))) (d (kadr (car dests)))
                            (dn (dnames (cdr dests))) (f fnames) (e (em-names em)) (ar (asg :list (tn 1))))))))

(defthm tvn-thm
  (implies (and (sn-hyps) (no-calls :list (g-rvals outs comps) sigs nil))
           (tvn-ok outs comps dests tmp em cnt locs sigs fnames st))
  :hints (("Goal" :induct (tv-ind outs comps dests tmp em cnt locs sigs fnames st)
           :in-theory (union-theories '(tv-ind tvn-atom tvn-skip tvn-tmp tvn-dir sn-ok-holds no-calls-cons g-rvals-val g-rvals-skip
                                        car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

; ---- the run

(defmacro tvv () '(g-rvals outs comps))
(defmacro tvr () '(g-rvals (cdr outs) (cdr comps)))
(defmacro tv-hyps ()
  '(and (not (tvg 0)) (equal (len outs) (len comps)) (not (car (a-sx-list (tvv) env s st defs n)))
        (no-calls :list (tvv) sigs nil) (em-ok em env fr) (decl-ok (tvg 4) fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (obj-is o s fr heap)
        (dests-ok dests fr) (equal (len dests) (len (tvv))) (no-duplicatesp-equal (dnames dests))
        (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars (tvg 4)))))))
(defmacro tv-concl ()
  '(and (equal (car (sx-list (tvg 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (tvg 1) fr heap)) heap)
        (svs-is (if tmp (asn-rhs (tvg 2)) dests) (mv-nth 1 (a-sx-list (tvv) env s st defs n)) (mv-nth 1 (sx-list (tvg 1) fr heap)) heap)
        (int64s (mv-nth 1 (a-sx-list (tvv) env s st defs n)))))

(defun-nx tv-sem (outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o)
  (implies (tv-hyps) (tv-concl)))

(defthm tv-sem-use
  (implies (and (tv-sem outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o) (tv-hyps)) (tv-concl))
  :rule-classes nil
  :hints (("Goal" :in-theory '(tv-sem))))
(defthm tv-sem-intro
  (implies (implies (tv-hyps) (tv-concl)) (tv-sem outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory '(tv-sem))))
(in-theory (disable tv-sem))

(defthm len-0-atom (implies (equal (len x) 0) (not (consp x))) :rule-classes nil)

(defthm tv-atom
  (implies (or (atom outs) (atom comps)) (tv-sem outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (enable tv-sem asn-rhs len) :use ((:instance len-0-atom (x dests)) (:instance len-0-atom (x outs)))
           :expand ((a-sx-list nil env s st defs n) (sx-list nil fr heap) (svs-is nil nil fr heap) (svs-is dests nil fr heap)))))

(defthm tv-skip
  (implies (and (consp outs) (consp comps) (car outs)
                (tv-sem (cdr outs) (cdr comps) dests tmp em cnt locs sigs fnames st env s defs n fr heap o))
           (tv-sem outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (mthy tv-sem g-tvals-skip g-rvals-skip len-cons-eq))))

(defmacro uk () '(mv-nth 1 (a-sx (car comps) env s st defs (1- n))))
(defmacro uks () '(mv-nth 1 (a-sx-list (tvr) env s st defs (1- n))))
(defmacro tfr1 () '(mv-nth 1 (sx-list (t1 1) fr heap)))
(defmacro tfrr () '(put (trv) (cons :int64 (uk)) (tfr1)))
(defmacro dnm () '(kadr (car dests)))
(defmacro tfrd () '(put (dnm) (cons :int64 (uk)) (tfr1)))

(defun-nx tv-tctx (outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o)
  (and (consp outs) (consp comps) (not (car outs)) tmp (tv-hyps) (sn-hyps) (em-nostobj em st)))
(defun-nx tv-dctx (outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o)
  (and (consp outs) (consp comps) (not (car outs)) (not tmp) (tv-hyps) (sn-hyps) (em-nostobj em st)))
(in-theory (disable tv-tctx tv-dctx))
(defmacro ttx () '(tv-tctx outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o))
(defmacro tdx () '(tv-dctx outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o))

(defthm tv-t0
  (implies (ttx) (and (consp outs) (consp comps) (not (car outs)) tmp (tv-hyps) (sn-hyps) (em-nostobj em st)))
  :rule-classes nil :hints (("Goal" :in-theory (mthy tv-tctx))))
(defthm tv-d0
  (implies (tdx) (and (consp outs) (consp comps) (not (car outs)) (not tmp) (tv-hyps) (sn-hyps) (em-nostobj em st)))
  :rule-classes nil :hints (("Goal" :in-theory (mthy tv-dctx))))

(defthm tv-ashape
  (implies (and (consp outs) (consp comps) (not (car outs)) (not (car (a-sx-list (tvv) env s st defs n))))
           (and (not (zp n)) (not (car (a-sx (car comps) env s st defs (1- n))))
                (not (car (a-sx-list (tvr) env s st defs (1- n))))
                (equal (mv-nth 1 (a-sx-list (tvv) env s st defs n)) (cons (uk) (uks)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable a-sx a-sx-list)
           :use ((:instance stu-ashape (xs (tvv)))))))

(defthm tv-ta
  (implies (ttx)
           (and (not (t1 0)) (not (tw 0)) (not (zp n)) (consp dests)
                (not (car (a-sx (car comps) env s st defs (1- n)))) (not (car (a-sx-list (tvr) env s st defs (1- n))))
                (equal (t1 3) :int64) (no-calls :term (car comps) sigs nil) (no-calls :list (tvr) sigs nil)
                (equal (len (cdr outs)) (len (cdr comps)))
                (not (car (g-fresh 'r :int64 (t1 4) (t1 5) (tvused))))
                (equal (tvg 1) (append (t1 1) (list (list :assign (list :var (trv)) (t1 2))) (tw 1)))
                (equal (tvg 2) (cons (list :assign (car dests) (list :var (trv))) (tw 2)))
                (equal (tvg 4) (tw 4))
                (equal (mv-nth 1 (a-sx-list (tvv) env s st defs n)) (cons (uk) (uks)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy g-rvals-val car-cons cdr-cons)
           :use (tv-t0 tv-shape-tmp tv-ashape (:instance no-calls-cons (xs (tvv)) (cs nil)) (:instance len-cons-eq (a outs) (b comps))))))

(defthm tv-ta-eq
  (implies (ttx)
           (and (equal (tvg 1) (append (t1 1) (list (list :assign (list :var (trv)) (t1 2))) (tw 1)))
                (equal (tvg 2) (cons (list :assign (car dests) (list :var (trv))) (tw 2)))
                (equal (tvg 4) (tw 4)) (equal (t1 3) :int64)
                (equal (mv-nth 1 (a-sx-list (tvv) env s st defs n)) (cons (uk) (uks)))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy) :use tv-ta)))

(defthm tv-da
  (implies (tdx)
           (and (not (t1 0)) (not (tn 0)) (not (zp n)) (consp dests)
                (not (car (a-sx (car comps) env s st defs (1- n)))) (not (car (a-sx-list (tvr) env s st defs (1- n))))
                (equal (t1 3) :int64) (no-calls :term (car comps) sigs nil) (no-calls :list (tvr) sigs nil)
                (equal (len (cdr outs)) (len (cdr comps)))
                (equal (tvg 1) (append (t1 1) (list (list :assign (car dests) (t1 2))) (tn 1)))
                (equal (tvg 4) (tn 4))
                (equal (mv-nth 1 (a-sx-list (tvv) env s st defs n)) (cons (uk) (uks)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy g-rvals-val car-cons cdr-cons)
           :use (tv-d0 tv-shape-dir tv-ashape (:instance no-calls-cons (xs (tvv)) (cs nil)) (:instance len-cons-eq (a outs) (b comps))))))

(defthm tv-da-eq
  (implies (tdx)
           (and (equal (tvg 1) (append (t1 1) (list (list :assign (car dests) (t1 2))) (tn 1)))
                (equal (tvg 4) (tn 4)) (equal (t1 3) :int64)
                (equal (mv-nth 1 (a-sx-list (tvv) env s st defs n)) (cons (uk) (uks)))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy) :use tv-da)))
(in-theory (disable tv-ta-eq tv-da-eq))

(defthm dests-ok-cdr
  (implies (and (consp ds) (dests-ok ds fr))
           (and (dests-ok (cdr ds) fr) (equal (car ds) (list :var (kadr (car ds)))) (equal (dty (kadr (car ds)) fr) '(:int64))))
  :rule-classes nil)

(defthm dnames-cdr
  (implies (and (consp ds) (no-duplicatesp-equal (dnames ds)) (not (intersectp-equal (dnames ds) x)))
           (and (no-duplicatesp-equal (dnames (cdr ds))) (not (intersectp-equal (dnames (cdr ds)) x))
                (not (member-equal (kadr (car ds)) (dnames (cdr ds)))) (not (member-equal (kadr (car ds)) x))))
  :rule-classes nil)

(defthm tv-glue
  (let ((fr1 (mv-nth 1 (sx-list s1 fr heap))))
    (implies (and (equal dt (list :var v))
                  (equal (car (sx-list s1 fr heap)) :normal) (equal (mv-nth 2 (sx-list s1 fr heap)) heap)
                  (not (car (sv c1 fr1 heap))) (equal (mv-nth 1 (sv c1 fr1 heap)) k1) (int64p k1)
                  (equal (dty v fr1) '(:int64))
                  (equal (car (sx-list tr (put v (cons :int64 k1) fr1) heap)) :normal)
                  (equal (mv-nth 2 (sx-list tr (put v (cons :int64 k1) fr1) heap)) heap)
                  (svs-is cr ks (mv-nth 1 (sx-list tr (put v (cons :int64 k1) fr1) heap)) heap)
                  (not (member-equal v (asg :list tr))))
             (let ((r (sx-list (append s1 (list (list :assign dt c1)) tr) fr heap)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap)
                    (svs-is (cons dt cr) (cons k1 ks) (mv-nth 1 r) heap)))))
  :rule-classes nil
  :hints (("Goal" :use settle-tmp-glue :in-theory (disable svs-is sx-list sv int64p dty))))

(defthm tv-not-mem-sub
  (implies (and (subsetp-equal a (append b c)) (not (member-equal x b)) (not (member-equal x c))) (not (member-equal x a)))
  :rule-classes nil)

(defthm tv-mem-int (implies (and (member-equal x a) (not (intersectp-equal b a))) (not (member-equal x b))))

(defthm tv-tsn
  (implies (ttx) (and (sn-ok (car comps) em cnt locs sigs fnames st)
                      (tvn-ok (cdr outs) (cdr comps) (cdr dests) tmp em (1+ (nfix (t1 4))) (trl) sigs fnames st)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy)
           :use (tv-t0 tv-ta (:instance sn-ok-holds (x (car comps)))
                 (:instance tvn-thm (outs (cdr outs)) (comps (cdr comps)) (dests (cdr dests)) (cnt (1+ (nfix (t1 4)))) (locs (trl)))))))
(defthm tv-dsn
  (implies (tdx) (and (sn-ok (car comps) em cnt locs sigs fnames st)
                      (tvn-ok (cdr outs) (cdr comps) (cdr dests) tmp em (t1 4) (t1 5) sigs fnames st)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy)
           :use (tv-d0 tv-da (:instance sn-ok-holds (x (car comps)))
                 (:instance tvn-thm (outs (cdr outs)) (comps (cdr comps)) (dests (cdr dests)) (cnt (t1 4)) (locs (t1 5)))))))

(defmacro tv-set-thy (&rest rs)
  `(union-theories (list* ,@rs 'strip-cars-cons-pair 'tv-mem-int 'intersectp-append-r 'intersectp-cons-2 (set-rules))
                   (set-difference-theories (theory 'minimal-theory) '(mv-nth))))

(defthm tv-tb
  (implies (ttx)
           (and (subsetp-equal (t1 5) (tvg 4)) (member-equal (cons (trv) :int64) (tw 4))
                (not (member-equal (trv) (em-names em)))
                (not (intersectp-equal (asg :list (t1 1)) (em-names em)))
                (not (member-equal (trv) (asg :list (tw 1))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (tv-set-thy 'tv-ta-eq)
           :use (tv-t0 tv-ta tv-tsn
                 (:instance sn-ok-use (x (car comps)))
                 (:instance tvn-ok-use (outs (cdr outs)) (comps (cdr comps)) (dests (cdr dests)) (cnt (1+ (nfix (t1 4)))) (locs (trl)))
                 (:instance g-fresh-out (b 'r) (ty :int64) (cnt (t1 4)) (locs (t1 5)) (used (tvused)))
                 (:instance subsetp-trans2 (a (t1 5)) (b (trl)) (c (tw 4)))
                 (:instance subsetp-cons-member (a (cons (trv) :int64)) (b (true-list-fix (t1 5))) (c (tw 4)))))))

(defthm tv-db
  (implies (tdx)
           (and (subsetp-equal (t1 5) (tvg 4))
                (not (member-equal (dnm) (em-names em)))
                (not (intersectp-equal (asg :list (t1 1)) (em-names em)))
                (not (member-equal (dnm) (asg :list (tn 1))))
                (equal (car dests) (list :var (dnm))) (equal (dty (dnm) fr) '(:int64)) (dests-ok (cdr dests) fr)
                (equal (len (cdr dests)) (len (tvr))) (no-duplicatesp-equal (dnames (cdr dests)))
                (not (intersectp-equal (dnames (cdr dests)) (append fnames (em-names em) (strip-cars (tn 4)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (tv-set-thy 'tv-da-eq 'dnames 'len-cons-eq 'g-rvals-val)
           :use (tv-d0 tv-da tv-dsn
                 (:instance sn-ok-use (x (car comps)))
                 (:instance tvn-ok-use (outs (cdr outs)) (comps (cdr comps)) (dests (cdr dests)) (cnt (t1 4)) (locs (t1 5)))
                 (:instance dests-ok-cdr (ds dests))
                 (:instance tv-not-mem-sub (x (dnm)) (a (asg :list (tn 1))) (b (strip-cars (tn 4))) (c (dnames (cdr dests))))
                 (:instance dnames-cdr (ds dests) (x (append fnames (em-names em) (strip-cars (tn 4)))))
                 (:instance len-cons-eq (a dests) (b (tvv)))))))

(defthm tv-te
  (implies (ttx)
           (and (dests-ok (cdr dests) fr)
                (equal (len (cdr dests)) (len (tvr))) (no-duplicatesp-equal (dnames (cdr dests)))
                (not (intersectp-equal (dnames (cdr dests)) (append fnames (em-names em) (strip-cars (tw 4)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (tv-set-thy 'tv-ta-eq 'dnames 'len-cons-eq 'g-rvals-val)
           :use (tv-t0 tv-ta
                 (:instance dests-ok-cdr (ds dests))
                 (:instance dnames-cdr (ds dests) (x (append fnames (em-names em) (strip-cars (tw 4)))))
                 (:instance len-cons-eq (a dests) (b (tvv)))))))

(defmacro tv-first ()
  '(and (equal (car (sx-list (t1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (t1 1) fr heap)) heap)
        (not (car (sv (t1 2) (tfr1) heap))) (equal (mv-nth 1 (sv (t1 2) (tfr1) heap)) (uk)) (int64p (uk))))

(defthm tv-tc
  (implies (ttx) (tv-first))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy tv-ta-eq scalar-ok)
           :use (tv-t0 tv-ta tv-tb
                 (:instance gs-sem-holds (x (car comps)) (n (1- n)))
                 (:instance gs-sem-use (x (car comps)) (n (1- n)))
                 (:instance decl-ok-subset (a (t1 5)) (b (tvg 4)))))))
(defthm tv-dc
  (implies (tdx) (tv-first))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy tv-da-eq scalar-ok)
           :use (tv-d0 tv-da tv-db
                 (:instance gs-sem-holds (x (car comps)) (n (1- n)))
                 (:instance gs-sem-use (x (car comps)) (n (1- n)))
                 (:instance decl-ok-subset (a (t1 5)) (b (tvg 4)))))))

(defthm tv-td
  (implies (ttx)
           (and (equal (dty (trv) (tfr1)) '(:int64))
                (em-ok em env (tfrr)) (decl-ok (tw 4) (tfrr)) (obj-is o s (tfrr) heap) (dests-ok (cdr dests) (tfrr))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy tv-ta-eq decl-ok-after-sx dests-ok-after-sx)
           :use (tv-t0 tv-ta tv-tb tv-tc tv-te
                 (:instance decl-ok-member-dty (l (tw 4)) (fr (tfr1)) (v (trv)) (ty :int64))
                 (:instance em-ok-after-sx (s (t1 1)))
                 (:instance em-ok-put (fr (tfr1)) (k (trv)) (v (cons :int64 (uk))))
                 (:instance decl-ok-put-int (locs (tw 4)) (fr (tfr1)) (k (trv)) (v (uk)))
                 (:instance obj-is-after-sx (ss (t1 1)))
                 (:instance obj-is-put-int (fr (tfr1)) (k (trv)) (v (uk)))
                 (:instance dests-ok-put-int (ds (cdr dests)) (fr (tfr1)) (k (trv)) (v (uk)))))))

(defthm tv-dd
  (implies (tdx)
           (and (equal (dty (dnm) (tfr1)) '(:int64))
                (em-ok em env (tfrd)) (decl-ok (tn 4) (tfrd)) (obj-is o s (tfrd) heap) (dests-ok (cdr dests) (tfrd))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy tv-da-eq decl-ok-after-sx dests-ok-after-sx dty-after-sx)
           :use (tv-d0 tv-da tv-db tv-dc
                 (:instance em-ok-after-sx (s (t1 1)))
                 (:instance em-ok-put (fr (tfr1)) (k (dnm)) (v (cons :int64 (uk))))
                 (:instance decl-ok-put-int (locs (tn 4)) (fr (tfr1)) (k (dnm)) (v (uk)))
                 (:instance obj-is-after-sx (ss (t1 1)))
                 (:instance obj-is-put-int (fr (tfr1)) (k (dnm)) (v (uk)))
                 (:instance dests-ok-put-int (ds (cdr dests)) (fr (tfr1)) (k (dnm)) (v (uk)))))))

(defthm tv-tmp-core
  (implies (and (ttx)
                (tv-sem (cdr outs) (cdr comps) (cdr dests) tmp em (1+ (nfix (t1 4))) (trl) sigs fnames st env s defs (1- n) (tfrr) heap o))
           (tv-concl))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy tv-ta-eq asn-rhs kaddr kar kdr car-cons cdr-cons int64s)
           :use (tv-t0 tv-ta tv-tb tv-tc tv-td tv-te
                 (:instance tv-sem-use (outs (cdr outs)) (comps (cdr comps)) (dests (cdr dests)) (cnt (1+ (nfix (t1 4)))) (locs (trl))
                            (n (1- n)) (fr (tfrr)))
                 (:instance tv-glue (dt (list :var (trv))) (s1 (t1 1)) (c1 (t1 2)) (k1 (uk)) (v (trv)) (tr (tw 1))
                            (cr (asn-rhs (tw 2))) (ks (uks)))))))

(defthm tv-dir-core
  (implies (and (tdx)
                (tv-sem (cdr outs) (cdr comps) (cdr dests) tmp em (t1 4) (t1 5) sigs fnames st env s defs (1- n) (tfrd) heap o))
           (tv-concl))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy tv-da-eq cons-car-cdr int64s car-cons cdr-cons)
           :use (tv-d0 tv-da tv-db tv-dc tv-dd
                 (:instance tv-sem-use (outs (cdr outs)) (comps (cdr comps)) (dests (cdr dests)) (cnt (t1 4)) (locs (t1 5))
                            (n (1- n)) (fr (tfrd)))
                 (:instance tv-glue (dt (car dests)) (s1 (t1 1)) (c1 (t1 2)) (k1 (uk)) (v (dnm)) (tr (tn 1))
                            (cr (cdr dests)) (ks (uks)))))))

(defthm tv-tmp
  (implies (and (consp outs) (consp comps) (not (car outs)) tmp (sn-hyps) (em-nostobj em st)
                (tv-sem (cdr outs) (cdr comps) (cdr dests) tmp em (1+ (nfix (t1 4))) (trl) sigs fnames st env s defs (1- n) (tfrr) heap o))
           (tv-sem outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (mthy tv-tctx) :use (tv-tmp-core tv-sem-intro))))

(defthm tv-dir
  (implies (and (consp outs) (consp comps) (not (car outs)) (not tmp) (sn-hyps) (em-nostobj em st)
                (tv-sem (cdr outs) (cdr comps) (cdr dests) tmp em (t1 4) (t1 5) sigs fnames st env s defs (1- n) (tfrd) heap o))
           (tv-sem outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (mthy tv-dctx) :use (tv-dir-core tv-sem-intro))))

(defun-nx tv-ind2 (outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap)
  (declare (xargs :measure (acl2-count comps)))
  (cond ((or (atom outs) (atom comps)) t)
        ((car outs) (tv-ind2 (cdr outs) (cdr comps) dests tmp em cnt locs sigs fnames st env s defs n fr heap))
        (tmp (tv-ind2 (cdr outs) (cdr comps) (cdr dests) tmp em (1+ (nfix (t1 4))) (trl) sigs fnames st env s defs (1- n) (tfrr) heap))
        (t (tv-ind2 (cdr outs) (cdr comps) (cdr dests) tmp em (t1 4) (t1 5) sigs fnames st env s defs (1- n) (tfrd) heap))))

(defthm tv-thm
  (implies (and (sn-hyps) (em-nostobj em st))
           (tv-sem outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :induct (tv-ind2 outs comps dests tmp em cnt locs sigs fnames st env s defs n fr heap)
           :in-theory (union-theories '(tv-ind2 tv-atom tv-skip tv-tmp tv-dir) (theory 'minimal-theory)))))

; ---- the dests from the r temporaries: as = (asn-gen dests rs)

(defun dvars (dn) (if (atom dn) nil (cons (list :var (car dn)) (dvars (cdr dn)))))
(defun dtys-ok (dn fr) (if (atom dn) t (and (equal (dty (car dn) fr) '(:int64)) (dtys-ok (cdr dn) fr))))

(defthm dests-ok-dvars
  (implies (dests-ok ds fr) (and (equal (dvars (dnames ds)) (true-list-fix ds)) (dtys-ok (dnames ds) fr)))
  :hints (("Goal" :induct (len ds) :in-theory (disable dty))))

(defthm asn-gen-tlf (equal (asn-gen (true-list-fix ds) rs) (asn-gen ds rs)))
(defthm svs-is-tlf (equal (svs-is (true-list-fix cs) ks fr heap) (svs-is cs ks fr heap)) :hints (("Goal" :in-theory (disable sv))))

(defthm lkp-agree-put
  (implies (not (member-equal k ns)) (lkp-agree ns fr (put k v fr)))
  :hints (("Goal" :induct (lkp-agree-ind ns))))

(defthm sv-put-other
  (implies (not (member-equal k (sv-names e))) (equal (sv e (put k v fr) heap) (sv e fr heap)))
  :hints (("Goal" :in-theory (disable sv put sv-agree) :use ((:instance sv-agree (fr2 (put k v fr)))))))

(defthm svs-is-put
  (implies (and (svs-is cs ks fr heap) (not (member-equal k (svs-names cs)))) (svs-is cs ks (put k v fr) heap))
  :hints (("Goal" :induct (svs-is cs ks fr heap) :in-theory (disable sv put sv-agree))))

(defun dn-ind (dn rs) (if (or (atom dn) (atom rs)) t (dn-ind (cdr dn) (cdr rs))))
(defthm asgv-asn-gen (subsetp-equal (asgv :list (asn-gen (dvars dn) rs)) dn)
  :hints (("Goal" :induct (dn-ind dn rs))))

(defthm not-member-asgv-asn-gen
  (implies (not (member-equal d dn)) (not (member-equal d (asgv :list (asn-gen (dvars dn) rs)))))
  :hints (("Goal" :in-theory (disable asgv-asn-gen) :use asgv-asn-gen)))

(defthm dtys-ok-put-int
  (implies (dtys-ok dn fr) (dtys-ok dn (put k (cons :int64 v) fr)))
  :hints (("Goal" :in-theory (disable put))))

(defun-nx asn-ind (dn rs vs fr heap)
  (if (or (atom dn) (atom rs)) (list vs fr heap)
    (asn-ind (cdr dn) (cdr rs) (cdr vs) (put (car dn) (cons :int64 (mv-nth 1 (sv (car rs) fr heap))) fr) heap)))

(defthm asn-run
  (implies (and (dtys-ok dn fr) (no-duplicatesp-equal dn) (svs-is rs vs fr heap) (int64s vs)
                (not (intersectp-equal dn (svs-names rs))) (equal (len dn) (len rs)))
           (and (equal (car (sx-list (asn-gen (dvars dn) rs) fr heap)) :normal)
                (equal (mv-nth 2 (sx-list (asn-gen (dvars dn) rs) fr heap)) heap)
                (svs-is (dvars dn) vs (mv-nth 1 (sx-list (asn-gen (dvars dn) rs) fr heap)) heap)))
  :hints (("Goal" :induct (asn-ind dn rs vs fr heap) :in-theory (disable sv put dty sx asgv-asn-gen)
           :expand ((sx-list (asn-gen (dvars dn) rs) fr heap) (sx-list nil fr heap)))))

; ---- g-stmt's cons case

; the source: the value components on S, then the stobj components' updates
(defun a-tuple (outs comps env s st defs n)
  (mv-let (e vs) (a-sx-list (g-rvals outs comps) env s st defs n)
    (if e (mv e s nil)
      (mv-let (e s1) (a-sacts outs comps env s st defs n)
        (if e (mv e s nil) (mv nil s1 vs))))))

(defthm g-stmt-cons
  (implies (and (consp x) (true-listp x) (eq (car x) 'cons))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests nil)
                  (if (not (= (len (g-conses x)) (len outs))) (mv :arity nil cnt locs)
                    (mv-let (e s as cnt locs) (g-tvals outs (g-conses x) dests (g-moves outs (g-conses x)) em cnt locs sigs fnames st)
                      (if e (mv e nil cnt locs)
                        (mv-let (e sm cnt locs) (g-sacts outs (g-conses x) em cnt locs sigs fnames st)
                          (if e (mv e nil cnt locs) (mv nil (append s sm as) cnt locs))))))))
  :hints (("Goal" :expand ((g-stmt x em cnt locs sigs fnames st outs dests nil))
           :in-theory (disable g-tvals g-sacts g-conses g-moves g-sexpr g-callst g-role))))

(defthm no-calls-rvals
  (implies (no-calls :list comps sigs nil) (no-calls :list (g-rvals outs comps) sigs nil))
  :hints (("Goal" :induct (g-rvals outs comps) :in-theory (enable g-rvals)
           :expand ((no-calls :list comps sigs nil) (:free (a b) (no-calls :list (cons a b) sigs nil))))))

(defthm stables-dests (implies (dests-ok ds fr) (and (stables ds) (equal (svs-names ds) (dnames ds))))
  :hints (("Goal" :induct (len ds) :in-theory (disable dty))))

(defthm len-dnames (equal (len (dnames ds)) (len ds)))
(defthm svs-is-len2 (implies (svs-is cs ks fr heap) (equal (len cs) (len ks))) :rule-classes nil
  :hints (("Goal" :in-theory (disable sv))))
(defun lal-ind (xs n) (if (or (zp n) (atom xs)) t (lal-ind (cdr xs) (1- n))))
(defthm len-a-sx-list
  (implies (not (car (a-sx-list xs env s st defs n))) (equal (len (mv-nth 1 (a-sx-list xs env s st defs n))) (len xs)))
  :hints (("Goal" :induct (lal-ind xs n) :in-theory (disable a-sx) :expand ((a-sx-list xs env s st defs n)))))

(defmacro cmp () '(g-conses x))
(defmacro cmv () '(g-moves outs (cmp)))
(defmacro ct (k) `(mv-nth ,k (g-tvals outs (cmp) dests (cmv) em cnt locs sigs fnames st)))
(defmacro csa (k) `(mv-nth ,k (g-sacts outs (cmp) em (ct 3) (ct 4) sigs fnames st)))
(defmacro kvs () '(mv-nth 1 (a-sx-list (g-rvals outs (cmp)) env s st defs n)))
(defmacro ks1 () '(mv-nth 1 (a-sacts outs (cmp) env s st defs n)))
(defmacro kf1 () '(mv-nth 1 (sx-list (ct 1) fr heap)))
(defmacro kf2 () '(mv-nth 1 (sx-list (csa 1) (kf1) heap)))
(defmacro kh2 () '(put (okey o fr) (ks1) heap))
(defmacro krs () '(if (cmv) (asn-rhs (ct 2)) dests))

(defmacro cons-hyps ()
  '(and (equal (len outs) (len (cmp))) (not (ct 0)) (not (csa 0))
        (not (car (a-sx-list (g-rvals outs (cmp)) env s st defs n))) (not (car (a-sacts outs (cmp) env s st defs n)))
        (no-calls :list (cmp) sigs nil) (em-ok em env fr) (decl-ok (csa 3) fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
        (dests-ok dests fr) (equal (len dests) (len (g-rvals outs (cmp)))) (no-duplicatesp-equal (dnames dests))
        (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars (csa 3)))))
        (gsc-sem outs (cmp) em (ct 3) (ct 4) sigs fnames st env s defs n (kf1) heap o)
        (stan-ok outs (cmp) em (ct 3) (ct 4) sigs fnames st)))

(defun-nx cons-ctxp (x em cnt locs sigs fnames st outs dests env s defs n fr heap o) (cons-hyps))
(in-theory (disable cons-ctxp))
(defmacro cnx () '(cons-ctxp x em cnt locs sigs fnames st outs dests env s defs n fr heap o))

(defthm cn-0 (implies (cnx) (cons-hyps)) :rule-classes nil :hints (("Goal" :in-theory (mthy cons-ctxp))))

; the names
(defthm cn-names
  (implies (cnx)
           (and (subsetp-equal (ct 4) (csa 3))
                (not (intersectp-equal (asg :list (ct 1)) (em-names em)))
                (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars (ct 4)))))
                (not (intersectp-equal (svs-names (krs)) (asgv :list (csa 1))))
                (implies (cmv) (and (stables (asn-rhs (ct 2)))
                                    (not (intersectp-equal (dnames dests) (svs-names (asn-rhs (ct 2)))))
                                    (equal (ct 2) (asn-gen dests (asn-rhs (ct 2))))))
                (implies (not (cmv)) (equal (ct 2) nil))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (intersectp-append-r) (g-tvals g-sacts tvn-ok stan-ok g-conses g-moves asg asgv dnames svs-names asn-rhs asn-gen))
           :use (cn-0
                 (:instance tvn-thm (comps (cmp)) (tmp (cmv)))
                 (:instance no-calls-rvals (comps (cmp)))
                 (:instance tvn-ok-use (comps (cmp)) (tmp (cmv)))
                 (:instance stan-ok-use (vars outs) (xs (cmp)) (cnt (ct 3)) (locs (ct 4)))
                 (:instance subsetp-strip-cars (a (ct 4)) (b (csa 3)))))))

(defthm cn-run1
  (implies (cnx)
           (and (equal (car (sx-list (ct 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (ct 1) fr heap)) heap)
                (implies (cmv) (svs-is (asn-rhs (ct 2)) (kvs) (kf1) heap))
                (implies (not (cmv)) (svs-is dests (kvs) (kf1) heap))
                (int64s (kvs))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy obj-at-is)
           :use (cn-0 cn-names
                 (:instance tv-thm (comps (cmp)) (tmp (cmv)))
                 (:instance tv-sem-use (comps (cmp)) (tmp (cmv)))
                 (:instance no-calls-rvals (comps (cmp)))
                 (:instance decl-ok-subset (a (ct 4)) (b (csa 3)))))))

(defthm cn-run2
  (implies (cnx)
           (and (equal (car (sx-list (csa 1) (kf1) heap)) :normal) (equal (mv-nth 2 (sx-list (csa 1) (kf1) heap)) (kh2))
                (st-ok st o (ks1)) (st-wf st (ks1)) (dests-ok dests (kf2))
                (implies (cmv) (svs-is (asn-rhs (ct 2)) (kvs) (kf2) (kh2)))
                (implies (not (cmv)) (svs-is dests (kvs) (kf2) (kh2)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (mthy decl-ok-after-sx dests-ok-after-sx okey-after obj-at-cadr put-okey-same obj-at-after cn-run1)
           :cases ((cmv))
           :use (cn-0 cn-names cn-run1
                 (:instance gsc-sem-use (vars outs) (xs (cmp)) (cnt (ct 3)) (locs (ct 4)) (fr (kf1)))
                 (:instance em-ok-after-sx (s (ct 1)))
                 (:instance obj-at-after (ss (ct 1)) (s2 s))
                 (:instance stables-dests (ds dests))
                 (:instance svs-is-after (cs (krs)) (ks (kvs)) (fr (kf1)) (ss (csa 1)) (h2 (kh2)))))))

(defthm sx-list-nil-run (equal (sx-list nil fr heap) (list :normal fr heap)) :hints (("Goal" :expand ((sx-list nil fr heap)))))

(defthm cn-final
  (implies (cnx)
           (and (equal (car (sx-list (ct 2) (kf2) (kh2))) :normal) (equal (mv-nth 2 (sx-list (ct 2) (kf2) (kh2))) (kh2))
                (svs-is dests (kvs) (mv-nth 1 (sx-list (ct 2) (kf2) (kh2))) (kh2))))
  :hints (("Goal" :do-not-induct t :in-theory (mthy cn-run1 cn-run2 dests-ok-dvars asn-gen-tlf svs-is-tlf sx-list-nil-run car-cons cdr-cons)
           :cases ((cmv))
           :use (cn-0 cn-names cn-run1 cn-run2
                 (:instance svs-is-len2 (cs (asn-rhs (ct 2))) (ks (kvs)) (fr (kf2)) (heap (kh2)))
                 (:instance len-a-sx-list (xs (g-rvals outs (cmp))))
                 (:instance len-dnames (ds dests))
                 (:instance dests-ok-dvars (ds dests) (fr (kf2)))
                 (:instance asn-run (dn (dnames dests)) (rs (asn-rhs (ct 2))) (vs (kvs)) (fr (kf2)) (heap (kh2)))))))

(in-theory (disable cn-run1 cn-run2 cn-final))

(defthm gst-cons-core
  (implies (cnx)
           (and (equal (car (sx-list (append (ct 1) (csa 1) (ct 2)) fr heap)) :normal)
                (equal (mv-nth 2 (sx-list (append (ct 1) (csa 1) (ct 2)) fr heap)) (kh2))
                (svs-is dests (kvs) (mv-nth 1 (sx-list (append (ct 1) (csa 1) (ct 2)) fr heap)) (kh2))
                (st-ok st o (ks1)) (st-wf st (ks1))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (mthy cn-run1 cn-run2 cn-final sx-list-append))))

(defthm gst-cons
  (implies (and (consp x) (true-listp x) (eq (car x) 'cons)
                (not (car (g-stmt x em cnt locs sigs fnames st outs dests nil)))
                (not (car (a-tuple outs (cmp) env s st defs n)))
                (no-calls :list (cmp) sigs nil) (em-ok em env fr) (decl-ok (mv-nth 3 (g-stmt x em cnt locs sigs fnames st outs dests nil)) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
                (dests-ok dests fr) (equal (len dests) (len (g-rvals outs (cmp)))) (no-duplicatesp-equal (dnames dests))
                (not (intersectp-equal (dnames dests)
                                       (append fnames (em-names em) (strip-cars (mv-nth 3 (g-stmt x em cnt locs sigs fnames st outs dests nil))))))
                (gsc-sem outs (cmp) em (ct 3) (ct 4) sigs fnames st env s defs n (kf1) heap o)
                (stan-ok outs (cmp) em (ct 3) (ct 4) sigs fnames st))
           (let ((r (sx-list (mv-nth 1 (g-stmt x em cnt locs sigs fnames st outs dests nil)) fr heap)))
             (and (equal (car r) :normal)
                  (equal (mv-nth 2 r) (put (okey o fr) (mv-nth 1 (a-tuple outs (cmp) env s st defs n)) heap))
                  (svs-is dests (mv-nth 2 (a-tuple outs (cmp) env s st defs n)) (mv-nth 1 r)
                          (put (okey o fr) (mv-nth 1 (a-tuple outs (cmp) env s st defs n)) heap))
                  (st-ok st o (mv-nth 1 (a-tuple outs (cmp) env s st defs n)))
                  (st-wf st (mv-nth 1 (a-tuple outs (cmp) env s st defs n))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (cons-ctxp) (g-tvals g-sacts g-conses g-moves g-stmt a-sx-list a-sacts sx-list svs-is
                                        gsc-sem stan-ok no-calls em-ok decl-ok st-ok st-wf obj-at dests-ok g-role))
           :use gst-cons-core)))
