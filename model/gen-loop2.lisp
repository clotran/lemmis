; gen-loop2: the remaining cases of the loop body's run (gen-loop.lisp): an
; if, a case chain's SELECT and its arms, as gen-ret's gr-if, gr-chain and
; gsel-*, with lp-ok for the conclusion; then the induction grt-sem-thm.

(in-package "ACL2")

(include-book "gen-loop")

(set-irrelevant-formals-ok t)

; ge-sem is used through ge-sem-use (its env, defs and n bound from the fact)
(in-theory (disable ge-sem-t))

(defthm grt-if
  (implies (and (consp x) (not (<= 3 (g-chain x nil nil))) (eq (car x) 'if) (true-listp x) (= (len x) 4)
                (grt-sem (caddr x) em (gc1 4) (gc1 5) self sigs fnames env defs cs (1- n) (fr-after (gc1 1) fr))
                (grt-sem (cadddr x) em (gi1 2) (gi1 3) self sigs fnames env defs cs (1- n) (fr-after (gc1 1) fr)))
           (grt-sem x em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((g-ret x em cnt locs self sigs fnames))
           :in-theory (e/d (grt-sem)
                           (g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p a-ev fx-list fv
                               tail-only no-calls em-ok scalar-ok dty fx decl-ok-ret-locs tail-only-if))
           :use ((:instance ge-sem-all (x (cadr x)) (n (1- n)))
                 (:instance tail-only-if)
                 (:instance decl-ok-ret-locs (x (caddr x)) (cnt (gc1 4)) (locs (gc1 5)))
                 (:instance decl-ok-ret-locs (x (cadddr x)) (cnt (gi1 2)) (locs (gi1 3)))))))

(defthm grt-chain
  (implies (and (consp x) (<= 3 (g-chain x nil nil))
                (grt-sem (caddr x) em cnt locs self sigs fnames env defs cs (1- n) fr)
                (gselt-sem (cadddr x) (1- (g-chain x nil nil)) em (gr1 2) (gr1 3) self sigs fnames env defs cs (1- n) fr))
           (grt-sem x em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((g-ret x em cnt locs self sigs fnames))
           :in-theory (e/d (var-ok grt-sem)
                           (g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p a-ev fx-list fv
                                    tail-only no-calls em-ok scalar-ok dty fx decl-ok-ret-locs decl-ok-sel-locs em-ok-necc
                                    case-key-test fx-arms))
           :use (g-chain-first
                 (:instance g-chain-on (x (cadddr x)) (v (chain-v x)) (keys (list (mv-nth 1 (g-case-key (cadr x)))))
                            (k (1- (g-chain x nil nil))))
                 (:instance em-ok-necc (x (chain-v x)))
                 (:instance case-key-test (c (cadr x)) (n (1- n)))
                 (:instance decl-ok-sel-locs (x (cadddr x)) (k (1- (g-chain x nil nil))) (cnt (gr1 2)) (locs (gr1 3)))))))

(defthm gselt-zp
  (implies (and (zp k) (grt-sem x em cnt locs self sigs fnames env defs cs n fr))
           (gselt-sem x k em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((g-select x k em cnt locs self sigs fnames))
           :in-theory (e/d (gselt-sem) (g-ret g-select a-ev fx-list tail-only em-ok dty)))))

(defthm gselt-bad
  (implies (and (not (zp k)) (not (and (consp x) (true-listp x) (= (len x) 4))))
           (gselt-sem x k em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((g-select x k em cnt locs self sigs fnames))
           :in-theory (e/d (gselt-sem) (g-ret g-select a-ev fx-list tail-only em-ok dty)))))

(defthm gselt-cons
  (implies (and (not (zp k)) (consp x) (true-listp x) (= (len x) 4)
                (grt-sem (caddr x) em cnt locs self sigs fnames env defs cs (1- n) fr)
                (gselt-sem (cadddr x) (1- k) em (gr1 2) (gr1 3) self sigs fnames env defs cs (1- n) fr))
           (gselt-sem x k em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :cases ((zp (1- k)))
           :expand ((g-select x k em cnt locs self sigs fnames) (g-select x 1 em cnt locs self sigs fnames) (chain-on (chain-v x) x k))
           :in-theory (e/d (gselt-sem)
                           (g-ret g-select g-case-key int-lit-p a-ev fx-list fv tail-only no-calls em-ok scalar-ok dty fx
                               decl-ok-ret-locs decl-ok-sel-locs case-key-test fx-arms))
           :use ((:instance case-key-test (c (cadr x)) (n (1- n)))
                 (:instance decl-ok-sel-locs (x (cadddr x)) (k (1- k)) (cnt (gr1 2)) (locs (gr1 3)))))))

(defthm grt-sem-thm
  (if (eq flag :sel) (gselt-sem x k em cnt locs self sigs fnames env defs cs n fr)
    (grt-sem x em cnt locs self sigs fnames env defs cs n fr))
  :rule-classes nil
  :hints (("Goal" :induct (gr-ind flag x k em cnt locs self sigs fnames env defs cs n fr) :do-not-induct t
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p fr-after))
          (and stable-under-simplificationp '(:cases ((and (consp x) (equal (car x) self)))))))

; ---- the output on tail-only source: call-free statements (CYCLE allowed),
; the temporaries fresh (as gen-retout's grc-ok)

(defmacro grct-hyps ()
  '(and (tail-only x self sigs nil) (lf-ok locs fnames) (consp (lkp self sigs)) (symbolp self)
        (not (equal self 'quote)) (not (equal self 'if))))

(defun grct-ok (flag x k em cnt locs self sigs fnames)
  (declare (xargs :verify-guards nil))
  (if (eq flag :sel)
      (mv-let (e arms dflt cnt2 locs2) (g-select x k em cnt locs self sigs fnames)
        (declare (ignore cnt2))
        (implies (and (not e) (grct-hyps) (ifs x k))
                 (and (cf-arms arms) (cf-stmts dflt) (lf-ok locs2 fnames))))
    (mv-let (e s cnt2 locs2) (g-ret x em cnt locs self sigs fnames)
      (declare (ignore cnt2))
      (implies (and (not e) (grct-hyps)) (and (cf-stmts s) (lf-ok locs2 fnames))))))

(defthm grct-ok-flag
  (implies (and (syntaxp (not (equal flag '':ret))) (not (equal flag :sel)))
           (equal (grct-ok flag x k em cnt locs self sigs fnames) (grct-ok :ret x k em cnt locs self sigs fnames)))
  :hints (("Goal" :in-theory (e/d (grct-ok) (g-ret g-select)))))

(defthm grct-use
  (implies (and (grct-ok :ret x k em cnt locs self sigs fnames) (not (gro 0)) (grct-hyps))
           (and (cf-stmts (gro 1)) (lf-ok (gro 3) fnames)))
  :hints (("Goal" :in-theory (e/d (grct-ok) (g-ret g-select tail-only lf-ok cf-stmts)))))

(defthm grcts-use
  (implies (and (grct-ok :sel x k em cnt locs self sigs fnames) (not (gso 0)) (grct-hyps) (ifs x k))
           (and (cf-arms (gso 1)) (cf-stmts (gso 2)) (lf-ok (gso 4) fnames)))
  :hints (("Goal" :in-theory (e/d (grct-ok) (g-ret g-select tail-only lf-ok cf-stmts cf-arms ifs)))))

(in-theory (disable grct-ok))

(defthm grct-chain
  (implies (and (consp x) (<= 3 (g-chain x nil nil))
                (grct-ok :ret (caddr x) 0 em cnt locs self sigs fnames)
                (grct-ok :sel (cadddr x) (1- (g-chain x nil nil)) em (gr1 2) (gr1 3) self sigs fnames))
           (grct-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grct-ok :ret x k em cnt locs self sigs fnames) (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p tail-only no-calls lf-ok
                               chain-on-ifs ifs)
           :use (g-chain-first
                 (:instance chain-on-ifs (x (cadddr x)) (v (chain-v x)) (k (1- (g-chain x nil nil))))
                 (:instance g-chain-on (x (cadddr x)) (v (chain-v x)) (keys (list (mv-nth 1 (g-case-key (cadr x)))))
                            (k (1- (g-chain x nil nil))))))))

(defthm grct-if
  (implies (and (consp x) (not (<= 3 (g-chain x nil nil))) (eq (car x) 'if) (true-listp x) (= (len x) 4)
                (grct-ok :ret (caddr x) 0 em (gc1 4) (gc1 5) self sigs fnames)
                (grct-ok :ret (cadddr x) 0 em (gi1 2) (gi1 3) self sigs fnames))
           (grct-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grct-ok :ret x k em cnt locs self sigs fnames) (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p tail-only no-calls lf-ok))))

(defthm grct-plain
  (implies (and (not (and (consp x) (or (<= 3 (g-chain x nil nil))
                                        (and (eq (car x) 'if) (true-listp x) (= (len x) 4)))))
                (or (atom x) (not (equal (car x) self))))
           (grct-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (grct-ok) (g-ret g-select g-expr g-tail g-case-key g-chain
                                                              int-lit-p tail-only no-calls lf-ok grc-use))
           :use ((:instance grc-other) (:instance grc-use)))))

(defthm cf-stmts-cycle (cf-stmts (list '(:cycle))) :hints (("Goal" :expand ((cf-stmts (list '(:cycle))) (cf-stmt '(:cycle))))))

(defthm g-tail-atom
  (implies (or (atom vars) (atom xs)) (equal (g-tail vars xs em cnt locs sigs fnames) (list nil nil nil cnt locs)))
  :hints (("Goal" :expand ((g-tail vars xs em cnt locs sigs fnames)))))

(defthm grct-tail
  (implies (and (consp x) (equal (car x) self))
           (grct-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (grct-ok gt-cf gt-lf) (g-ret g-select g-expr g-tail tail-only no-calls lf-ok gt-cf-thm gt-lf-thm))
           :use ((:instance gt-cf-thm (vars (kar (cdr (lkp self sigs)))) (xs (cdr x)))
                 (:instance gt-lf-thm (vars (kar (cdr (lkp self sigs)))) (xs (cdr x)))))))

(defthm grct-sel-zp
  (implies (and (zp k) (grct-ok :ret x 0 em cnt locs self sigs fnames))
           (grct-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grct-ok :sel x k em cnt locs self sigs fnames) (g-select x k em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select tail-only lf-ok))))

(defthm grct-sel-bad
  (implies (and (not (zp k)) (not (and (consp x) (true-listp x) (= (len x) 4))))
           (grct-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grct-ok :sel x k em cnt locs self sigs fnames) (g-select x k em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select tail-only lf-ok))))

(defthm grct-sel-cons
  (implies (and (not (zp k))
                (grct-ok :ret (caddr x) 0 em cnt locs self sigs fnames)
                (grct-ok :sel (cadddr x) (1- k) em (gr1 2) (gr1 3) self sigs fnames))
           (grct-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grct-ok :sel x k em cnt locs self sigs fnames) (g-select x k em cnt locs self sigs fnames)
                                            (ifs x k) (tail-only x self sigs nil))
           :in-theory (disable g-ret g-select g-case-key int-lit-p tail-only no-calls lf-ok))))

(defthm grct-ok-thm
  (grct-ok flag x k em cnt locs self sigs fnames)
  :rule-classes nil
  :hints (("Goal" :induct (gr-ind flag x k em cnt locs self sigs fnames env defs cs n fr) :do-not-induct t
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p fr-after))
          (and stable-under-simplificationp '(:cases ((and (consp x) (equal (car x) self)))))))

(defthm g-ret-tail-cf
  (implies (and (not (mv-nth 0 (g-ret x em cnt locs self sigs fnames))) (grct-hyps))
           (and (cf-stmts (mv-nth 1 (g-ret x em cnt locs self sigs fnames)))
                (lf-ok (mv-nth 3 (g-ret x em cnt locs self sigs fnames)) fnames)))
  :hints (("Goal" :in-theory (disable grct-use) :use ((:instance grct-ok-thm (flag :ret)) (:instance grct-use)))))
