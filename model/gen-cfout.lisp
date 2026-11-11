; gen-cfout: on source that calls no translated function (no-calls),
; g-expr's statements are call-free and loop-free (cf-stmts) and its code is
; a call-free expression (cf-expr), so fx-is-f-ex applies to them. Its own
; induction over g-ind, kept apart from ge-sem's.

(in-package "ACL2")

(include-book "gen-proof2")

(defun gc-ok (flag x vars em cnt locs sigs fnames)
  (declare (xargs :verify-guards nil))
  (case flag
    (:args (mv-let (e s cs ts cnt2 locs2) (g-args x em cnt locs sigs fnames)
             (declare (ignore ts cnt2 locs2))
             (implies (and (not e) (no-calls :list x sigs nil)) (and (cf-stmts s) (cf-exprs cs)))))
    (:binds (mv-let (e s binds cnt2 locs2) (g-binds vars x em cnt locs sigs fnames)
              (declare (ignore binds cnt2 locs2))
              (implies (and (not e) (no-calls :list x sigs nil)) (cf-stmts s))))
    (otherwise (mv-let (e s c ty cnt2 locs2) (g-expr x em cnt locs sigs fnames)
                 (declare (ignore ty cnt2 locs2))
                 (implies (and (not e) (no-calls :term x sigs nil)) (and (cf-stmts s) (cf-expr c)))))))

(defthm gc-use
  (implies (and (gc-ok :expr x vars em cnt locs sigs fnames)
                (not (mv-nth 0 (g-expr x em cnt locs sigs fnames))) (no-calls :term x sigs nil))
           (and (cf-stmts (mv-nth 1 (g-expr x em cnt locs sigs fnames)))
                (cf-expr (mv-nth 2 (g-expr x em cnt locs sigs fnames)))))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds no-calls cf-stmts cf-expr cf-exprs))))

(defthm gkind-if-facts
  (implies (equal (gkind x) :if) (and (consp x) (or (equal (car x) 'if) (equal (car x) 'implies))))
  :rule-classes :forward-chaining)

(defthm gca-use
  (implies (and (gc-ok :args x vars em cnt locs sigs fnames)
                (not (mv-nth 0 (g-args x em cnt locs sigs fnames))) (no-calls :list x sigs nil))
           (and (cf-stmts (mv-nth 1 (g-args x em cnt locs sigs fnames)))
                (cf-exprs (mv-nth 2 (g-args x em cnt locs sigs fnames)))))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds no-calls cf-stmts cf-expr cf-exprs))))

(defthm gcb-use
  (implies (and (gc-ok :binds x vars em cnt locs sigs fnames)
                (not (mv-nth 0 (g-binds vars x em cnt locs sigs fnames))) (no-calls :list x sigs nil))
           (cf-stmts (mv-nth 1 (g-binds vars x em cnt locs sigs fnames))))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds no-calls cf-stmts cf-expr cf-exprs))))

(in-theory (disable gc-ok))

(defmacro c1 (k) `(mv-nth ,k (g-expr (kadr x) em cnt locs sigs fnames)))
(defmacro c2 (k) `(mv-nth ,k (g-expr (kaddr x) em (c1 4) (c1 5) sigs fnames)))

(defthm cf-stmts-cons-assign
  (equal (cf-stmts (cons (list :assign (list :var v) c) ss)) (and (cf-expr c) (cf-stmts ss)))
  :hints (("Goal" :expand ((cf-stmts (cons (list :assign (list :var v) c) ss))
                           (cf-stmt (list :assign (list :var v) c))))))

(defthm cf-stmt-if
  (equal (cf-stmt (list :if c a b)) (and (cf-expr c) (cf-stmts a) (cf-stmts b)))
  :hints (("Goal" :expand ((cf-stmt (list :if c a b))))))

(defthm cf-exprs-parts
  (and (implies (and (cf-exprs cs) (consp cs)) (cf-expr (car cs)))
       (implies (and (cf-exprs cs) (consp (cdr cs))) (cf-expr (cadr cs))))
  :hints (("Goal" :expand ((cf-exprs cs) (cf-exprs (cdr cs))))))

(defthm no-calls-list-atom (implies (atom x) (no-calls :list x sigs nil)))

(defthm no-calls-list-len0 (implies (equal (len x) 0) (no-calls :list x sigs nil)))

(defthm gc-base
  (implies (member-eq (gkind x) '(:sym :atom :quote)) (gc-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((gc-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames)))))

(defthm gc-if
  (implies (and (equal (gkind x) :if)
                (gc-ok :expr (kadr x) nil em cnt locs sigs fnames)
                (gc-ok :expr (kaddr x) nil em (c1 4) (c1 5) sigs fnames)
                (gc-ok :expr (kadddr x) nil em (c2 4) (c2 5) sigs fnames))
           (gc-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gc-ok :expr x vars em cnt locs sigs fnames))
           :in-theory (disable gc-base g-expr g-args g-binds no-calls gkind gc-ok g-if-out g-tmp nfix))))

(defthm gc-big
  (implies (and (equal (gkind x) :big)
                (gc-ok :expr (if (g-big (kadr x)) (kaddr x) (kadr x)) nil em cnt locs sigs fnames))
           (gc-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :cases ((g-big (kadr x))) :expand ((gc-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames) (no-calls :term x sigs nil))
           :in-theory (disable gc-base g-expr g-args g-binds no-calls))))

(defthm gc-the-check
  (implies (and (consp x) (eq (car x) 'the-check) (gc-ok :expr (kadddr x) nil em cnt locs sigs fnames))
           (gc-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gc-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames) (no-calls :term x sigs nil))
           :in-theory (disable gc-base g-expr g-args g-binds no-calls))))

(defthm gc-call
  (implies (and (equal (gkind x) :call) (gc-ok :args (cdr x) nil em cnt locs sigs fnames))
           (gc-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((gc-ok :expr x vars em cnt locs sigs fnames)) :do-not-induct t
           :in-theory (disable gc-base gkind g-expr g-args g-binds no-calls g-unop g-binop))))

(defmacro cb (k) `(mv-nth ,k (g-binds (kadr (car x)) (cdr x) em cnt locs sigs fnames)))

(defthm gc-lambda
  (implies (and (equal (gkind x) :lambda)
                (gc-ok :binds (cdr x) (kadr (car x)) em cnt locs sigs fnames)
                (gc-ok :expr (kaddr (car x)) nil (append (cb 2) em) (cb 3) (cb 4) sigs fnames))
           (gc-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gc-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames) (no-calls :term x sigs nil))
           :in-theory (disable gc-base g-expr g-args g-binds no-calls))))

(defthm gc-args-nil
  (implies (atom x) (gc-ok :args x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((gc-ok :args x vars em cnt locs sigs fnames) (g-args x em cnt locs sigs fnames)))))

(defthm gc-args-cons
  (implies (and (consp x)
                (gc-ok :expr (car x) nil em cnt locs sigs fnames)
                (gc-ok :args (cdr x) nil em (mv-nth 4 (g-expr (car x) em cnt locs sigs fnames))
                       (mv-nth 5 (g-expr (car x) em cnt locs sigs fnames)) sigs fnames))
           (gc-ok :args x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gc-ok :args x vars em cnt locs sigs fnames) (g-args x em cnt locs sigs fnames))
           :in-theory (disable gc-base g-expr g-args g-binds no-calls))))

(defthm gc-binds-nil
  (implies (or (atom vars) (atom x)) (gc-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((gc-ok :binds x vars em cnt locs sigs fnames) (g-binds vars x em cnt locs sigs fnames)))))

(defthm gc-binds-self
  (implies (and (consp vars) (consp x) (eq (car vars) (car x))
                (gc-ok :binds (cdr x) (cdr vars) em cnt locs sigs fnames))
           (gc-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gc-ok :binds x vars em cnt locs sigs fnames) (g-binds vars x em cnt locs sigs fnames))
           :in-theory (disable gc-base g-expr g-args g-binds no-calls))))

(defmacro cf-l (k)
  `(mv-nth ,k (g-fresh (car vars) (mv-nth 3 (g-expr (car x) em cnt locs sigs fnames))
                       (mv-nth 4 (g-expr (car x) em cnt locs sigs fnames))
                       (mv-nth 5 (g-expr (car x) em cnt locs sigs fnames)) (append fnames (em-names em)))))

(defthm gc-binds-cons
  (implies (and (consp vars) (consp x) (not (eq (car vars) (car x)))
                (gc-ok :expr (car x) nil em cnt locs sigs fnames)
                (gc-ok :binds (cdr x) (cdr vars) em (cf-l 2) (cf-l 3) sigs fnames))
           (gc-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gc-ok :binds x vars em cnt locs sigs fnames) (g-binds vars x em cnt locs sigs fnames))
           :in-theory (disable gc-base g-expr g-args g-binds no-calls g-fresh))))

(defthm gc-ok-thm
  (if (eq flag :args) (gc-ok :args x vars em cnt locs sigs fnames)
    (if (eq flag :binds) (gc-ok :binds x vars em cnt locs sigs fnames)
      (gc-ok :expr x vars em cnt locs sigs fnames)))
  :rule-classes nil
  :hints (("Goal" :induct (g-ind flag x vars em cnt locs sigs fnames env defs n fr) :do-not-induct t
           :in-theory (disable gc-ok g-expr g-args g-binds g-big kadr kaddr kadddr g-fresh fr-after a-vals))))

(defthm g-expr-cf
  (implies (and (not (mv-nth 0 (g-expr x em cnt locs sigs fnames))) (no-calls :term x sigs nil))
           (and (cf-stmts (mv-nth 1 (g-expr x em cnt locs sigs fnames)))
                (cf-expr (mv-nth 2 (g-expr x em cnt locs sigs fnames)))))
  :hints (("Goal" :use (:instance gc-ok-thm (flag :expr) (vars nil)))))
