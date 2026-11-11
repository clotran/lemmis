; gen-loopcc: gen-loop2's code-shape induction (grct-ok) again, on tail-only
; source that also calls functions in cs (not the function itself): g-ret's
; statements are cc-stmts (gen-callev; CYCLE allowed), the temporaries
; fresh. With gen-ccout's g-expr-cc in place of g-expr-cf.

(in-package "ACL2")

(include-book "gen-loop2")
(include-book "gen-ccout")

(set-irrelevant-formals-ok t)

; ---- g-tail's statements and assignments

(defthm cc-stmts-assign-var
  (equal (cc-stmts (cons (list :assign (list :var a) c) ss)) (and (ce-ok :one c) (cc-stmts ss)))
  :hints (("Goal" :expand ((cc-stmts (cons (list :assign (list :var a) c) ss))
                           (cc-stmt (list :assign (list :var a) c))))))

(defthm ce-ok-var (ce-ok :one (list :var v)) :hints (("Goal" :expand ((ce-ok :one (list :var v))))))

(defthm gt-cc
  (implies (and (not (car (g-tail vars xs em cnt locs sigs fnames))) (no-calls :list xs sigs cs))
           (and (cc-stmts (mv-nth 1 (g-tail vars xs em cnt locs sigs fnames)))
                (cc-stmts (mv-nth 2 (g-tail vars xs em cnt locs sigs fnames)))))
  :hints (("Goal" :induct (g-tail vars xs em cnt locs sigs fnames)
           :in-theory (disable g-expr g-fresh g-tmp g-formal no-calls))
          ("Subgoal *1/2" :use ((:instance g-tail-open)) :in-theory (disable g-expr g-fresh g-tmp g-formal no-calls g-tail))
          ("Subgoal *1/1" :expand ((g-tail vars xs em cnt locs sigs fnames)))))

; ---- g-ret's output

(defmacro grcc-hyps ()
  '(and (tail-only x self sigs cs) (not (member-equal self cs)) (lf-ok locs fnames) (consp (lkp self sigs))
        (symbolp self) (not (equal self 'quote)) (not (equal self 'if))))

(defun grcc-ok (flag x k em cnt locs self sigs fnames cs)
  (declare (xargs :verify-guards nil))
  (if (eq flag :sel)
      (mv-let (e arms dflt cnt2 locs2) (g-select x k em cnt locs self sigs fnames)
        (declare (ignore cnt2))
        (implies (and (not e) (grcc-hyps) (ifs x k))
                 (and (cc-arms arms) (cc-stmts dflt) (lf-ok locs2 fnames))))
    (mv-let (e s cnt2 locs2) (g-ret x em cnt locs self sigs fnames)
      (declare (ignore cnt2))
      (implies (and (not e) (grcc-hyps)) (and (cc-stmts s) (lf-ok locs2 fnames))))))

(defthm grcc-ok-flag
  (implies (and (syntaxp (not (equal flag '':ret))) (not (equal flag :sel)))
           (equal (grcc-ok flag x k em cnt locs self sigs fnames cs) (grcc-ok :ret x k em cnt locs self sigs fnames cs)))
  :hints (("Goal" :in-theory (e/d (grcc-ok) (g-ret g-select)))))

(defthm grcc-use
  (implies (and (grcc-ok :ret x k em cnt locs self sigs fnames cs) (not (gro 0)) (grcc-hyps))
           (and (cc-stmts (gro 1)) (lf-ok (gro 3) fnames)))
  :hints (("Goal" :in-theory (e/d (grcc-ok) (g-ret g-select tail-only lf-ok cc-stmts)))))

(defthm grccs-use
  (implies (and (grcc-ok :sel x k em cnt locs self sigs fnames cs) (not (gso 0)) (grcc-hyps) (ifs x k))
           (and (cc-arms (gso 1)) (cc-stmts (gso 2)) (lf-ok (gso 4) fnames)))
  :hints (("Goal" :in-theory (e/d (grcc-ok) (g-ret g-select tail-only lf-ok cc-stmts cc-arms ifs)))))

(in-theory (disable grcc-ok))

(defthm cc-stmts-ret-tail
  (equal (cc-stmts (append s (list (list :assign '(:var "r") c) '(:return))))
         (and (cc-stmts s) (ce-ok :one c)))
  :hints (("Goal" :expand ((cc-stmts (list (list :assign '(:var "r") c) '(:return)))
                           (cc-stmts (list '(:return))) (cc-stmt '(:return))))))

(defthm cc-stmts-select
  (equal (cc-stmts (list (list :select c arms dflt)))
         (and (ce-ok :one c) (cc-arms arms) (cc-stmts dflt)))
  :hints (("Goal" :expand ((cc-stmt (list :select c arms dflt))))))

(defthm cc-stmts-if1
  (equal (cc-stmts (list (list :if c a b))) (and (ce-ok :one c) (cc-stmts a) (cc-stmts b))))

(defthm cc-arms-cons-arm
  (equal (cc-arms (cons (list key sa) arms)) (and (cc-stmts sa) (cc-arms arms)))
  :hints (("Goal" :expand ((cc-arms (cons (list key sa) arms))))))

(defthm cc-arms-nil (cc-arms nil) :hints (("Goal" :expand ((cc-arms nil)))))

(defthm cc-stmts-cycle (cc-stmts (list '(:cycle))) :hints (("Goal" :expand ((cc-stmts (list '(:cycle))) (cc-stmt '(:cycle))))))

(defthm grcc-chain
  (implies (and (consp x) (<= 3 (g-chain x nil nil))
                (grcc-ok :ret (caddr x) 0 em cnt locs self sigs fnames cs)
                (grcc-ok :sel (cadddr x) (1- (g-chain x nil nil)) em (gr1 2) (gr1 3) self sigs fnames cs))
           (grcc-ok :ret x k em cnt locs self sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((grcc-ok :ret x k em cnt locs self sigs fnames cs) (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p tail-only no-calls lf-ok
                               chain-on-ifs ifs)
           :use (g-chain-first
                 (:instance chain-on-ifs (x (cadddr x)) (v (chain-v x)) (k (1- (g-chain x nil nil))))
                 (:instance g-chain-on (x (cadddr x)) (v (chain-v x)) (keys (list (mv-nth 1 (g-case-key (cadr x)))))
                            (k (1- (g-chain x nil nil))))))))

(defthm grcc-if
  (implies (and (consp x) (not (<= 3 (g-chain x nil nil))) (eq (car x) 'if) (true-listp x) (= (len x) 4)
                (grcc-ok :ret (caddr x) 0 em (gc1 4) (gc1 5) self sigs fnames cs)
                (grcc-ok :ret (cadddr x) 0 em (gi1 2) (gi1 3) self sigs fnames cs))
           (grcc-ok :ret x k em cnt locs self sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((grcc-ok :ret x k em cnt locs self sigs fnames cs) (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p tail-only no-calls lf-ok)
           :use ((:instance tail-only-if)))))

(defthm grcc-plain
  (implies (and (not (and (consp x) (or (<= 3 (g-chain x nil nil))
                                        (and (eq (car x) 'if) (true-listp x) (= (len x) 4)))))
                (or (atom x) (not (equal (car x) self))))
           (grcc-ok :ret x k em cnt locs self sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((grcc-ok :ret x k em cnt locs self sigs fnames cs) (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p tail-only no-calls lf-ok)
           :use ((:instance tail-only-plain)))))

(defthm grcc-tail
  (implies (and (consp x) (equal (car x) self))
           (grcc-ok :ret x k em cnt locs self sigs fnames cs))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (grcc-ok gt-lf) (g-ret g-select g-expr g-tail tail-only no-calls lf-ok gt-lf-thm))
           :use ((:instance gt-cc (vars (kar (cdr (lkp self sigs)))) (xs (cdr x)))
                 (:instance tail-only-self)
                 (:instance gt-lf-thm (vars (kar (cdr (lkp self sigs)))) (xs (cdr x)))))))

(defthm grcc-sel-zp
  (implies (and (zp k) (grcc-ok :ret x 0 em cnt locs self sigs fnames cs))
           (grcc-ok :sel x k em cnt locs self sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((grcc-ok :sel x k em cnt locs self sigs fnames cs) (g-select x k em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select tail-only lf-ok))))

(defthm grcc-sel-bad
  (implies (and (not (zp k)) (not (and (consp x) (true-listp x) (= (len x) 4))))
           (grcc-ok :sel x k em cnt locs self sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((grcc-ok :sel x k em cnt locs self sigs fnames cs) (g-select x k em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select tail-only lf-ok))))

(defthm grcc-sel-cons
  (implies (and (not (zp k))
                (grcc-ok :ret (caddr x) 0 em cnt locs self sigs fnames cs)
                (grcc-ok :sel (cadddr x) (1- k) em (gr1 2) (gr1 3) self sigs fnames cs))
           (grcc-ok :sel x k em cnt locs self sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((grcc-ok :sel x k em cnt locs self sigs fnames cs) (g-select x k em cnt locs self sigs fnames)
                                            (ifs x k) (tail-only x self sigs cs))
           :in-theory (disable g-ret g-select g-case-key int-lit-p tail-only no-calls lf-ok))))

(defthm grcc-ok-thm
  (grcc-ok flag x k em cnt locs self sigs fnames cs)
  :rule-classes nil
  :hints (("Goal" :induct (gr-ind flag x k em cnt locs self sigs fnames env defs cs n fr) :do-not-induct t
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p fr-after))
          (and stable-under-simplificationp '(:cases ((and (consp x) (equal (car x) self)))))))

(defthm g-ret-tail-cc
  (implies (and (not (mv-nth 0 (g-ret x em cnt locs self sigs fnames))) (grcc-hyps))
           (and (cc-stmts (mv-nth 1 (g-ret x em cnt locs self sigs fnames)))
                (lf-ok (mv-nth 3 (g-ret x em cnt locs self sigs fnames)) fnames)))
  :hints (("Goal" :in-theory (disable grcc-use) :use ((:instance grcc-ok-thm (flag :ret)) (:instance grcc-use)))))
