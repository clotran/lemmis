; gen-retout: on source that calls no translated function (no-calls), g-ret's
; statements are call-free and loop-free (cf-stmts: no CYCLE, no DO), and its
; temporaries stay fresh (lf-ok, gen-fresh.lisp). Its own induction over
; gr-ind, as grl-ok's in gen-ret.lisp.

(in-package "ACL2")

(include-book "gen-ret")
(include-book "gen-fresh")

; a case chain's else part is an if, k deep
(defun ifs (x k)
  (if (zp k) t (and (consp x) (eq (car x) 'if) (ifs (cadddr x) (1- k)))))

(defthm chain-on-ifs (implies (chain-on v x k) (ifs x k)))

(defmacro grc-hyps ()
  '(and (no-calls :term x sigs nil) (lf-ok locs fnames) (consp (lkp self sigs)) (symbolp self) (not (equal self 'quote))))

(defun grc-ok (flag x k em cnt locs self sigs fnames)
  (declare (xargs :verify-guards nil))
  (if (eq flag :sel)
      (mv-let (e arms dflt cnt2 locs2) (g-select x k em cnt locs self sigs fnames)
        (declare (ignore cnt2))
        (implies (and (not e) (grc-hyps) (ifs x k))
                 (and (cf-arms arms) (cf-stmts dflt) (lf-ok locs2 fnames))))
    (mv-let (e s cnt2 locs2) (g-ret x em cnt locs self sigs fnames)
      (declare (ignore cnt2))
      (implies (and (not e) (grc-hyps)) (and (cf-stmts s) (lf-ok locs2 fnames))))))

(defthm grc-ok-flag
  (implies (and (syntaxp (not (equal flag '':ret))) (not (equal flag :sel)))
           (equal (grc-ok flag x k em cnt locs self sigs fnames) (grc-ok :ret x k em cnt locs self sigs fnames)))
  :hints (("Goal" :in-theory (e/d (grc-ok) (g-ret g-select)))))

(defthm grc-use
  (implies (and (grc-ok :ret x k em cnt locs self sigs fnames) (not (gro 0)) (grc-hyps))
           (and (cf-stmts (gro 1)) (lf-ok (gro 3) fnames)))
  :hints (("Goal" :in-theory (e/d (grc-ok) (g-ret g-select no-calls lf-ok cf-stmts)))))

(defthm grcs-use
  (implies (and (grc-ok :sel x k em cnt locs self sigs fnames) (not (gso 0)) (grc-hyps) (ifs x k))
           (and (cf-arms (gso 1)) (cf-stmts (gso 2)) (lf-ok (gso 4) fnames)))
  :hints (("Goal" :in-theory (e/d (grc-ok) (g-ret g-select no-calls lf-ok cf-stmts cf-arms ifs)))))

(in-theory (disable grc-ok))

(defthm nc-parts
  (implies (and (no-calls :term x sigs nil) (consp x) (symbolp (car x)) (not (equal (car x) 'quote)))
           (and (no-calls :term (cadr x) sigs nil) (no-calls :term (caddr x) sigs nil) (no-calls :term (cadddr x) sigs nil)))
  :hints (("Goal" :expand ((no-calls :term x sigs nil) (no-calls :list (cdr x) sigs nil)
                           (no-calls :list (cddr x) sigs nil) (no-calls :list (cdddr x) sigs nil)))))

(defthm nc-self
  (implies (and (consp x) (equal (car x) self) (symbolp self) (not (equal self 'quote)) (consp (lkp self sigs)))
           (not (no-calls :term x sigs nil)))
  :hints (("Goal" :expand ((no-calls :term x sigs nil)))))

(defthm cf-stmts-ret-tail
  (equal (cf-stmts (append s (list (list :assign '(:var "r") c) '(:return))))
         (and (cf-stmts s) (cf-expr c)))
  :hints (("Goal" :expand ((cf-stmts (list (list :assign '(:var "r") c) '(:return)))
                           (cf-stmts (list '(:return))) (cf-stmt '(:return))))))

(defthm cf-stmts-select
  (equal (cf-stmts (list (list :select c arms dflt)))
         (and (cf-expr c) (cf-arms arms) (cf-stmts dflt)))
  :hints (("Goal" :expand ((cf-stmt (list :select c arms dflt))))))

(defthm cf-arms-cons-arm
  (equal (cf-arms (cons (list key sa) arms)) (and (cf-stmts sa) (cf-arms arms)))
  :hints (("Goal" :expand ((cf-arms (cons (list key sa) arms))))))

(defthm cf-arms-nil (cf-arms nil) :hints (("Goal" :expand ((cf-arms nil)))))

(defthm grc-chain
  (implies (and (consp x) (<= 3 (g-chain x nil nil))
                (grc-ok :ret (caddr x) 0 em cnt locs self sigs fnames)
                (grc-ok :sel (cadddr x) (1- (g-chain x nil nil)) em (gr1 2) (gr1 3) self sigs fnames))
           (grc-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grc-ok :ret x k em cnt locs self sigs fnames) (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p no-calls lf-ok chain-on-ifs ifs)
           :use (g-chain-first
                 (:instance chain-on-ifs (x (cadddr x)) (v (chain-v x)) (k (1- (g-chain x nil nil))))
                 (:instance g-chain-on (x (cadddr x)) (v (chain-v x)) (keys (list (mv-nth 1 (g-case-key (cadr x)))))
                            (k (1- (g-chain x nil nil))))))))

(defthm grc-if
  (implies (and (consp x) (not (<= 3 (g-chain x nil nil))) (eq (car x) 'if) (true-listp x) (= (len x) 4)
                (grc-ok :ret (caddr x) 0 em (gc1 4) (gc1 5) self sigs fnames)
                (grc-ok :ret (cadddr x) 0 em (gi1 2) (gi1 3) self sigs fnames))
           (grc-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grc-ok :ret x k em cnt locs self sigs fnames) (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p no-calls lf-ok))))

(defthm grc-other
  (implies (not (and (consp x) (or (<= 3 (g-chain x nil nil))
                                   (and (eq (car x) 'if) (true-listp x) (= (len x) 4)))))
           (grc-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grc-ok :ret x k em cnt locs self sigs fnames) (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p no-calls lf-ok))))

(defthm grc-sel-zp
  (implies (and (zp k) (grc-ok :ret x 0 em cnt locs self sigs fnames))
           (grc-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grc-ok :sel x k em cnt locs self sigs fnames) (g-select x k em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select no-calls lf-ok))))

(defthm grc-sel-bad
  (implies (and (not (zp k)) (not (and (consp x) (true-listp x) (= (len x) 4))))
           (grc-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grc-ok :sel x k em cnt locs self sigs fnames) (g-select x k em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select no-calls lf-ok))))

(defthm grc-sel-cons
  (implies (and (not (zp k))
                (grc-ok :ret (caddr x) 0 em cnt locs self sigs fnames)
                (grc-ok :sel (cadddr x) (1- k) em (gr1 2) (gr1 3) self sigs fnames))
           (grc-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((grc-ok :sel x k em cnt locs self sigs fnames) (g-select x k em cnt locs self sigs fnames)
                                            (ifs x k))
           :in-theory (disable g-ret g-select g-case-key int-lit-p no-calls lf-ok))))

(defthm grc-ok-thm
  (grc-ok flag x k em cnt locs self sigs fnames)
  :rule-classes nil
  :hints (("Goal" :induct (gr-ind flag x k em cnt locs self sigs fnames env defs n fr) :do-not-induct t
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p fr-after))))

(defthm g-ret-cf
  (implies (and (not (mv-nth 0 (g-ret x em cnt locs self sigs fnames))) (grc-hyps))
           (and (cf-stmts (mv-nth 1 (g-ret x em cnt locs self sigs fnames)))
                (lf-ok (mv-nth 3 (g-ret x em cnt locs self sigs fnames)) fnames)))
  :hints (("Goal" :in-theory (disable grc-use) :use ((:instance grc-ok-thm (flag :ret)) (:instance grc-use)))))
