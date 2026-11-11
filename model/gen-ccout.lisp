; gen-ccout: gen-cfout's induction again, on source that calls only functions
; in cs (no-calls ... cs): g-expr's statements are cc-stmts and its code
; ce-ok, so gen-callev's fx-is-f-ex-c applies to them.

(in-package "ACL2")

(include-book "gen-cfout")
(include-book "gen-callev")

(defthm cf-expr-ce-ok (implies (cf-expr e) (ce-ok :one e))
  :hints (("Goal" :induct (cf-expr e) :expand ((ce-ok :one e)))))

(defthm ce-ok-list-cons
  (implies (consp cs) (equal (ce-ok :list cs) (and (ce-ok :one (car cs)) (ce-ok :list (cdr cs)))))
  :hints (("Goal" :expand ((ce-ok :list cs)))))

(defthm ce-ok-fcall (equal (ce-ok :one (list :fcall f cs)) (ce-ok :list cs))
  :hints (("Goal" :expand ((ce-ok :one (list :fcall f cs))))))

(defthm cc-stmts-append (equal (cc-stmts (append a b)) (and (cc-stmts a) (cc-stmts b))))

(defthm g-unop-cc
  (implies (and (not (car (g-unop op c ty))) (ce-ok :one c)) (ce-ok :one (mv-nth 1 (g-unop op c ty))))
  :hints (("Goal" :in-theory (enable g-unop)
           :expand ((:free (a) (ce-ok :one (list :neg a))) (:free (a) (ce-ok :one (list :not a)))
                    (:free (a b) (ce-ok :one (list :max a b))) (:free (a b) (ce-ok :one (list :le a b)))
                    (:free (a b) (ce-ok :one (list :ge a b))) (ce-ok :one (quote (:true))) (ce-ok :one (quote (:int 0)))))))

(defthm g-binop-cc
  (implies (and (not (car (g-binop op a ta b tb))) (ce-ok :one a) (ce-ok :one b))
           (ce-ok :one (mv-nth 1 (g-binop op a ta b tb))))
  :hints (("Goal" :in-theory (enable g-binop)
           :expand ((:free (a b) (ce-ok :one (list :add a b))) (:free (a b) (ce-ok :one (list :mul a b)))
                    (:free (a b) (ce-ok :one (list :eq a b))) (:free (a b) (ce-ok :one (list :lt a b)))))))

(defun gcc-ok (flag x vars em cnt locs sigs fnames cs)
  (declare (xargs :verify-guards nil))
  (case flag
    (:args (mv-let (e s codes ts cnt2 locs2) (g-args x em cnt locs sigs fnames)
             (declare (ignore ts cnt2 locs2))
             (implies (and (not e) (no-calls :list x sigs cs)) (and (cc-stmts s) (ce-ok :list codes)))))
    (:binds (mv-let (e s binds cnt2 locs2) (g-binds vars x em cnt locs sigs fnames)
              (declare (ignore binds cnt2 locs2))
              (implies (and (not e) (no-calls :list x sigs cs)) (cc-stmts s))))
    (otherwise (mv-let (e s c ty cnt2 locs2) (g-expr x em cnt locs sigs fnames)
                 (declare (ignore ty cnt2 locs2))
                 (implies (and (not e) (no-calls :term x sigs cs)) (and (cc-stmts s) (ce-ok :one c)))))))

(defthm gcc-use
  (implies (and (gcc-ok :expr x vars em cnt locs sigs fnames cs)
                (not (mv-nth 0 (g-expr x em cnt locs sigs fnames))) (no-calls :term x sigs cs))
           (and (cc-stmts (mv-nth 1 (g-expr x em cnt locs sigs fnames)))
                (ce-ok :one (mv-nth 2 (g-expr x em cnt locs sigs fnames)))))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds no-calls cc-stmts ce-ok))))

(defthm gcca-use
  (implies (and (gcc-ok :args x vars em cnt locs sigs fnames cs)
                (not (mv-nth 0 (g-args x em cnt locs sigs fnames))) (no-calls :list x sigs cs))
           (and (cc-stmts (mv-nth 1 (g-args x em cnt locs sigs fnames)))
                (ce-ok :list (mv-nth 2 (g-args x em cnt locs sigs fnames)))))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds no-calls cc-stmts ce-ok))))

(defthm gccb-use
  (implies (and (gcc-ok :binds x vars em cnt locs sigs fnames cs)
                (not (mv-nth 0 (g-binds vars x em cnt locs sigs fnames))) (no-calls :list x sigs cs))
           (cc-stmts (mv-nth 1 (g-binds vars x em cnt locs sigs fnames))))
  :hints (("Goal" :in-theory (disable g-expr g-args g-binds no-calls cc-stmts ce-ok))))

(in-theory (disable gcc-ok))


(defthm cc-stmts-cons-assign
  (equal (cc-stmts (cons (list :assign (list :var v) c) ss)) (and (ce-ok :one c) (cc-stmts ss)))
  :hints (("Goal" :expand ((cc-stmts (cons (list :assign (list :var v) c) ss))
                           (cc-stmt (list :assign (list :var v) c))))))

(defthm cc-stmt-if
  (equal (cc-stmt (list :if c a b)) (and (ce-ok :one c) (cc-stmts a) (cc-stmts b)))
  :hints (("Goal" :expand ((cc-stmt (list :if c a b))))))

(defthm ce-ok-list-parts2
  (and (implies (and (ce-ok :list cs) (consp cs)) (ce-ok :one (car cs)))
       (implies (and (ce-ok :list cs) (consp (cdr cs))) (ce-ok :one (cadr cs))))
  :hints (("Goal" :expand ((ce-ok :list cs) (ce-ok :list (cdr cs))))))

(defthm no-calls-list-atom-cs (implies (atom x) (no-calls :list x sigs cs)))

(defthm no-calls-list-len0-cs (implies (equal (len x) 0) (no-calls :list x sigs cs)))

(defthm gcc-base
  (implies (member-eq (gkind x) '(:sym :atom :quote)) (gcc-ok :expr x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :expand ((gcc-ok :expr x vars em cnt locs sigs fnames cs) (g-expr x em cnt locs sigs fnames)))))

(defthm gcc-if
  (implies (and (equal (gkind x) :if)
                (gcc-ok :expr (kadr x) nil em cnt locs sigs fnames cs)
                (gcc-ok :expr (kaddr x) nil em (c1 4) (c1 5) sigs fnames cs)
                (gcc-ok :expr (kadddr x) nil em (c2 4) (c2 5) sigs fnames cs))
           (gcc-ok :expr x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((gcc-ok :expr x vars em cnt locs sigs fnames cs))
           :in-theory (disable gcc-base g-expr g-args g-binds no-calls gkind gcc-ok g-if-out g-tmp nfix))))

(defthm gcc-big
  (implies (and (equal (gkind x) :big)
                (gcc-ok :expr (if (g-big (kadr x)) (kaddr x) (kadr x)) nil em cnt locs sigs fnames cs))
           (gcc-ok :expr x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :do-not-induct t :cases ((g-big (kadr x))) :expand ((gcc-ok :expr x vars em cnt locs sigs fnames cs) (g-expr x em cnt locs sigs fnames) (no-calls :term x sigs cs))
           :in-theory (disable gcc-base g-expr g-args g-binds no-calls))))

(defthm gcc-the-check
  (implies (and (consp x) (eq (car x) 'the-check) (gcc-ok :expr (kadddr x) nil em cnt locs sigs fnames cs))
           (gcc-ok :expr x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((gcc-ok :expr x vars em cnt locs sigs fnames cs) (g-expr x em cnt locs sigs fnames) (no-calls :term x sigs cs))
           :in-theory (disable gcc-base g-expr g-args g-binds no-calls))))

(defthm gcc-call
  (implies (and (equal (gkind x) :call) (gcc-ok :args (cdr x) nil em cnt locs sigs fnames cs))
           (gcc-ok :expr x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :expand ((gcc-ok :expr x vars em cnt locs sigs fnames cs)) :do-not-induct t
           :in-theory (disable gcc-base gkind g-expr g-args g-binds no-calls g-unop g-binop))))


(defthm gcc-lambda
  (implies (and (equal (gkind x) :lambda)
                (gcc-ok :binds (cdr x) (kadr (car x)) em cnt locs sigs fnames cs)
                (gcc-ok :expr (kaddr (car x)) nil (append (cb 2) em) (cb 3) (cb 4) sigs fnames cs))
           (gcc-ok :expr x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((gcc-ok :expr x vars em cnt locs sigs fnames cs) (g-expr x em cnt locs sigs fnames) (no-calls :term x sigs cs))
           :in-theory (disable gcc-base g-expr g-args g-binds no-calls))))

(defthm gcc-args-nil
  (implies (atom x) (gcc-ok :args x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :expand ((gcc-ok :args x vars em cnt locs sigs fnames cs) (g-args x em cnt locs sigs fnames)))))

(defthm gcc-args-cons
  (implies (and (consp x)
                (gcc-ok :expr (car x) nil em cnt locs sigs fnames cs)
                (gcc-ok :args (cdr x) nil em (mv-nth 4 (g-expr (car x) em cnt locs sigs fnames))
                       (mv-nth 5 (g-expr (car x) em cnt locs sigs fnames)) sigs fnames cs))
           (gcc-ok :args x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((gcc-ok :args x vars em cnt locs sigs fnames cs) (g-args x em cnt locs sigs fnames))
           :in-theory (disable gcc-base g-expr g-args g-binds no-calls))))

(defthm gcc-binds-nil
  (implies (or (atom vars) (atom x)) (gcc-ok :binds x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :expand ((gcc-ok :binds x vars em cnt locs sigs fnames cs) (g-binds vars x em cnt locs sigs fnames)))))

(defthm gcc-binds-self
  (implies (and (consp vars) (consp x) (eq (car vars) (car x))
                (gcc-ok :binds (cdr x) (cdr vars) em cnt locs sigs fnames cs))
           (gcc-ok :binds x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((gcc-ok :binds x vars em cnt locs sigs fnames cs) (g-binds vars x em cnt locs sigs fnames))
           :in-theory (disable gcc-base g-expr g-args g-binds no-calls))))


(defthm gcc-binds-cons
  (implies (and (consp vars) (consp x) (not (eq (car vars) (car x)))
                (gcc-ok :expr (car x) nil em cnt locs sigs fnames cs)
                (gcc-ok :binds (cdr x) (cdr vars) em (cf-l 2) (cf-l 3) sigs fnames cs))
           (gcc-ok :binds x vars em cnt locs sigs fnames cs))
  :hints (("Goal" :do-not-induct t :expand ((gcc-ok :binds x vars em cnt locs sigs fnames cs) (g-binds vars x em cnt locs sigs fnames))
           :in-theory (disable gcc-base g-expr g-args g-binds no-calls g-fresh))))

(defthm gcc-ok-thm
  (if (eq flag :args) (gcc-ok :args x vars em cnt locs sigs fnames cs)
    (if (eq flag :binds) (gcc-ok :binds x vars em cnt locs sigs fnames cs)
      (gcc-ok :expr x vars em cnt locs sigs fnames cs)))
  :rule-classes nil
  :hints (("Goal" :induct (g-ind flag x vars em cnt locs sigs fnames env defs n fr) :do-not-induct t
           :in-theory (disable gcc-ok g-expr g-args g-binds g-big kadr kaddr kadddr g-fresh fr-after a-vals))))

(defthm g-expr-cc
  (implies (and (not (mv-nth 0 (g-expr x em cnt locs sigs fnames))) (no-calls :term x sigs cs))
           (and (cc-stmts (mv-nth 1 (g-expr x em cnt locs sigs fnames)))
                (ce-ok :one (mv-nth 2 (g-expr x em cnt locs sigs fnames)))))
  :hints (("Goal" :use (:instance gcc-ok-thm (flag :expr) (vars nil)))))
