; gen-fresh: the temporaries g-expr makes are distinct, none is "r" and none
; is a formal's name (g-fresh's check, every g-fresh call seeing the formals'
; names). The function's frame (gen-fn.lisp) declares them all, so this is
; what keeps a declaration from overwriting a formal or another temporary.
; Its own induction over g-ind, as gen-cfout's.

(in-package "ACL2")

(include-book "gen-cfout")

(defun lf-ok (locs fnames)
  (and (alistp locs) (no-duplicatesp-equal (strip-cars locs))
       (not (member-equal "r" (strip-cars locs)))
       (not (intersectp-equal (strip-cars locs) fnames))))

(defthm alistp-tlf (implies (alistp l) (equal (true-list-fix l) l)))

(defthm lf-ok-g-fresh
  (implies (and (lf-ok locs fnames) (not (car (g-fresh base ty cnt locs (append fnames rest)))))
           (lf-ok (mv-nth 3 (g-fresh base ty cnt locs (append fnames rest))) fnames))
  :hints (("Goal" :in-theory (disable g-tmp))))

(defthm lf-ok-g-if
  (implies (and (lf-ok locs fnames)
                (not (car (g-if sc cc tc sa ca ta sb cb tb cnt locs (append fnames rest)))))
           (lf-ok (mv-nth 5 (g-if sc cc tc sa ca ta sb cb tb cnt locs (append fnames rest))) fnames))
  :hints (("Goal" :in-theory (disable g-fresh lf-ok)
           :use (:instance lf-ok-g-fresh (base 't) (ty ta)))))

(defun gf-ok (flag x vars em cnt locs sigs fnames)
  (declare (xargs :verify-guards nil))
  (case flag
    (:args (mv-let (e s cs ts cnt2 locs2) (g-args x em cnt locs sigs fnames)
             (declare (ignore s cs ts cnt2))
             (implies (and (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames))))
    (:binds (mv-let (e s binds cnt2 locs2) (g-binds vars x em cnt locs sigs fnames)
              (declare (ignore s binds cnt2))
              (implies (and (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames))))
    (otherwise (mv-let (e s c ty cnt2 locs2) (g-expr x em cnt locs sigs fnames)
                 (declare (ignore s c ty cnt2))
                 (implies (and (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames))))))

(defthm gf-use
  (implies (and (gf-ok :expr x vars em cnt locs sigs fnames)
                (not (mv-nth 0 (g-expr x em cnt locs sigs fnames))) (lf-ok locs fnames))
           (lf-ok (mv-nth 5 (g-expr x em cnt locs sigs fnames)) fnames))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds lf-ok))))

(defthm gfa-use
  (implies (and (gf-ok :args x vars em cnt locs sigs fnames)
                (not (mv-nth 0 (g-args x em cnt locs sigs fnames))) (lf-ok locs fnames))
           (lf-ok (mv-nth 5 (g-args x em cnt locs sigs fnames)) fnames))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds lf-ok))))

(defthm gfb-use
  (implies (and (gf-ok :binds x vars em cnt locs sigs fnames)
                (not (mv-nth 0 (g-binds vars x em cnt locs sigs fnames))) (lf-ok locs fnames))
           (lf-ok (mv-nth 4 (g-binds vars x em cnt locs sigs fnames)) fnames))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds lf-ok))))

(in-theory (disable gf-ok lf-ok))

(defthm gf-base
  (implies (member-eq (gkind x) '(:sym :atom :quote)) (gf-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((gf-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames)))))

(defthm gf-if
  (implies (and (equal (gkind x) :if)
                (gf-ok :expr (kadr x) nil em cnt locs sigs fnames)
                (gf-ok :expr (kaddr x) nil em (c1 4) (c1 5) sigs fnames)
                (gf-ok :expr (kadddr x) nil em (c2 4) (c2 5) sigs fnames))
           (gf-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gf-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames))
           :in-theory (disable gf-base g-expr g-args g-binds gkind g-if g-if-out g-tmp nfix))))

(defthm gf-big
  (implies (and (equal (gkind x) :big)
                (gf-ok :expr (if (g-big (kadr x)) (kaddr x) (kadr x)) nil em cnt locs sigs fnames))
           (gf-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :cases ((g-big (kadr x)))
           :expand ((gf-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames))
           :in-theory (disable gf-base g-expr g-args g-binds))))

(defthm gf-the-check
  (implies (and (consp x) (eq (car x) 'the-check) (gf-ok :expr (kadddr x) nil em cnt locs sigs fnames))
           (gf-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gf-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames))
           :in-theory (disable gf-base g-expr g-args g-binds))))

(defthm gf-call
  (implies (and (equal (gkind x) :call) (gf-ok :args (cdr x) nil em cnt locs sigs fnames))
           (gf-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((gf-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames)) :do-not-induct t
           :in-theory (disable gf-base gkind g-expr g-args g-binds g-unop g-binop))))

(defthm gf-lambda
  (implies (and (equal (gkind x) :lambda)
                (gf-ok :binds (cdr x) (kadr (car x)) em cnt locs sigs fnames)
                (gf-ok :expr (kaddr (car x)) nil (append (cb 2) em) (cb 3) (cb 4) sigs fnames))
           (gf-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gf-ok :expr x vars em cnt locs sigs fnames) (g-expr x em cnt locs sigs fnames))
           :in-theory (disable gf-base g-expr g-args g-binds))))

(defthm gf-args-nil
  (implies (atom x) (gf-ok :args x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((gf-ok :args x vars em cnt locs sigs fnames) (g-args x em cnt locs sigs fnames)))))

(defthm gf-args-cons
  (implies (and (consp x)
                (gf-ok :expr (car x) nil em cnt locs sigs fnames)
                (gf-ok :args (cdr x) nil em (mv-nth 4 (g-expr (car x) em cnt locs sigs fnames))
                       (mv-nth 5 (g-expr (car x) em cnt locs sigs fnames)) sigs fnames))
           (gf-ok :args x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gf-ok :args x vars em cnt locs sigs fnames) (g-args x em cnt locs sigs fnames))
           :in-theory (disable gf-base g-expr g-args g-binds))))

(defthm gf-binds-nil
  (implies (or (atom vars) (atom x)) (gf-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((gf-ok :binds x vars em cnt locs sigs fnames) (g-binds vars x em cnt locs sigs fnames)))))

(defthm gf-binds-self
  (implies (and (consp vars) (consp x) (eq (car vars) (car x))
                (gf-ok :binds (cdr x) (cdr vars) em cnt locs sigs fnames))
           (gf-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gf-ok :binds x vars em cnt locs sigs fnames) (g-binds vars x em cnt locs sigs fnames))
           :in-theory (disable gf-base g-expr g-args g-binds))))

(defthm gf-binds-cons
  (implies (and (consp vars) (consp x) (not (eq (car vars) (car x)))
                (gf-ok :expr (car x) nil em cnt locs sigs fnames)
                (gf-ok :binds (cdr x) (cdr vars) em (cf-l 2) (cf-l 3) sigs fnames))
           (gf-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((gf-ok :binds x vars em cnt locs sigs fnames) (g-binds vars x em cnt locs sigs fnames))
           :in-theory (disable gf-base g-expr g-args g-binds g-fresh))))

(defthm gf-ok-thm
  (if (eq flag :args) (gf-ok :args x vars em cnt locs sigs fnames)
    (if (eq flag :binds) (gf-ok :binds x vars em cnt locs sigs fnames)
      (gf-ok :expr x vars em cnt locs sigs fnames)))
  :rule-classes nil
  :hints (("Goal" :induct (g-ind flag x vars em cnt locs sigs fnames env defs n fr) :do-not-induct t
           :in-theory (disable gf-ok g-expr g-args g-binds g-big kadr kaddr kadddr g-fresh fr-after a-vals))))

(defthm g-expr-fresh
  (implies (and (not (mv-nth 0 (g-expr x em cnt locs sigs fnames))) (lf-ok locs fnames))
           (lf-ok (mv-nth 5 (g-expr x em cnt locs sigs fnames)) fnames))
  :hints (("Goal" :use (:instance gf-ok-thm (flag :expr) (vars nil)))))
