; gen-proof2: the rest of ge-sem's cases (if, implies, a lambda's bindings
; and body), and the induction that assembles them. gen-proof.lisp has the
; invariants, the other cases, and the definitions (ge-sem, ga-sem, gb-sem).

(in-package "ACL2")

(include-book "gen-proof")

; ---- small facts

(defthm decl-ok-tlf (equal (decl-ok (true-list-fix l) fr) (decl-ok l fr)))

(defthm a-ev-if
  (implies (and (consp x) (equal (car x) 'if))
           (equal (a-ev x env defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e c) (a-ev (kadr x) env defs (1- n))
                      (cond (e (mv e nil))
                            (c (a-ev (kaddr x) env defs (1- n)))
                            (t (a-ev (kadddr x) env defs (1- n))))))))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm g-expr-if
  (implies (equal (gkind x) :if)
           (equal (g-expr x em cnt locs sigs fnames)
                  (mv-let (e sc cc tc cnt locs) (g-expr (kadr x) em cnt locs sigs fnames)
                    (if e (mv e nil nil nil cnt locs)
                      (mv-let (e sa ca ta cnt locs) (g-expr (kaddr x) em cnt locs sigs fnames)
                        (if e (mv e nil nil nil cnt locs)
                          (mv-let (e sb cb tb cnt locs)
                            (if (eq (car x) 'if) (g-expr (kadddr x) em cnt locs sigs fnames)
                              (mv nil nil '(:true) :logical cnt locs))
                            (if (or e (not (true-listp x)) (not (= (len x) (if (eq (car x) 'if) 4 3))))
                                (mv (or e :syntax) nil nil nil cnt locs)
                              (g-if sc cc tc sa ca ta sb cb tb cnt locs (append fnames (em-names em)))))))))))
  :hints (("Goal" :expand ((g-expr x em cnt locs sigs fnames)) :in-theory (disable g-args g-binds))))

(defthm fv-var-put
  (implies (scalar-ok ty v) (equal (fv (list :var k) (put k (cons ty v) fr)) (mv nil v))))

; a temporary assigned
(defthm assign-run
  (implies (and (not (car (fv ca fr))) (consp (dty tmp fr)) (scalar-ok (car (dty tmp fr)) (mv-nth 1 (fv ca fr))))
           (equal (fx (list :assign (list :var tmp) ca) fr)
                  (mv :normal (put tmp (cons (car (dty tmp fr)) (mv-nth 1 (fv ca fr))) fr))))
  :hints (("Goal" :in-theory (e/d (dty) (fv)) :expand ((fx (list :assign (list :var tmp) ca) fr)))))

(defthm fx-if-stmt
  (implies (and (not (car (fv c fr))) (booleanp (mv-nth 1 (fv c fr))))
           (equal (fx (list :if c a b) fr)
                  (if (mv-nth 1 (fv c fr)) (fx-list a fr) (fx-list b fr))))
  :hints (("Goal" :expand ((fx (list :if c a b) fr)) :in-theory (disable fx-list fv))))


; ---- if and implies: g-if's temporary gets the branch's value

(defun if-stmts (sc cc sa ca sb cb tmp)
  (append sc (list (list :if cc (append sa (list (list :assign (list :var tmp) ca)))
                         (append sb (list (list :assign (list :var tmp) cb)))))))

(defmacro gif () '(g-if sc cc tc sa ca ta sb cb tb cnt locs used))

(defthm g-if-out
  (implies (not (car (gif)))
           (and (equal (mv-nth 1 (gif)) (if-stmts sc cc sa ca sb cb (g-tmp 't (1+ (nfix cnt)))))
                (equal (mv-nth 2 (gif)) (list :var (g-tmp 't (1+ (nfix cnt)))))
                (equal (mv-nth 3 (gif)) ta)
                (equal (mv-nth 5 (gif)) (cons (cons (g-tmp 't (1+ (nfix cnt))) ta) (true-list-fix locs))))))

(defthm g-if-types
  (implies (not (car (gif))) (and (equal tc :logical) (equal tb ta)))
  :rule-classes :forward-chaining)

(defthm if-glue
  (let ((fr1 (mv-nth 1 (fx-list sc fr))))
    (implies (and (equal (car (fx-list sc fr)) :normal) (not (car (fv cc fr1)))
                  (equal (mv-nth 1 (fv cc fr1)) c) (booleanp c) (equal (dty tmp fr) (list ta))
                  (if c (and (equal (car (fx-list sa fr1)) :normal)
                             (not (car (fv ca (mv-nth 1 (fx-list sa fr1)))))
                             (equal (mv-nth 1 (fv ca (mv-nth 1 (fx-list sa fr1)))) v) (scalar-ok ta v))
                    (and (equal (car (fx-list sb fr1)) :normal)
                         (not (car (fv cb (mv-nth 1 (fx-list sb fr1)))))
                         (equal (mv-nth 1 (fv cb (mv-nth 1 (fx-list sb fr1)))) v) (scalar-ok ta v))))
             (and (equal (car (fx-list (if-stmts sc cc sa ca sb cb tmp) fr)) :normal)
                  (equal (fv (list :var tmp) (mv-nth 1 (fx-list (if-stmts sc cc sa ca sb cb tmp) fr)))
                         (mv nil v)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fx fv fx-list dty))))

; ge-sem used by backchaining (env, defs, n bound from the ge-sem fact), so a
; case's proof does not split on each part's hypotheses
(defmacro ge (k) `(mv-nth ,k (g-expr x em cnt locs sigs fnames)))

(defthm ge-sem-use
  (implies (and (ge-sem x em cnt locs sigs fnames env defs n fr cs)
                (not (ge 0)) (not (car (a-ev x env defs n))) (no-calls :term x sigs cs) (a-orc defs sigs cs) (em-ok em env fr)
                (decl-ok (ge 5) fr) (no-prim-defs defs))
           (and (equal (car (fx-list (ge 1) fr)) :normal)
                (not (car (fv (ge 2) (mv-nth 1 (fx-list (ge 1) fr)))))
                (equal (mv-nth 1 (fv (ge 2) (mv-nth 1 (fx-list (ge 1) fr)))) (mv-nth 1 (a-ev x env defs n)))
                (scalar-ok (ge 3) (mv-nth 1 (a-ev x env defs n)))
                (implies (equal (ge 3) :logical) (booleanp (mv-nth 1 (a-ev x env defs n))))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (ge-sem) (g-expr a-ev fx-list fv no-calls em-ok decl-ok scalar-ok)))))

(in-theory (disable ge-sem))

(defmacro i1 (k) `(mv-nth ,k (g-expr (kadr x) em cnt locs sigs fnames)))
(defmacro i2 (k) `(mv-nth ,k (g-expr (kaddr x) em (i1 4) (i1 5) sigs fnames)))
(defmacro i3 (k) `(mv-nth ,k (g-expr (kadddr x) em (i2 4) (i2 5) sigs fnames)))

(defthm ge-if
  (implies (and (equal (gkind x) :if) (equal (car x) 'if)
                (ge-sem (kadr x) em cnt locs sigs fnames env defs (1- n) fr cs)
                (ge-sem (kaddr x) em (i1 4) (i1 5) sigs fnames env defs (1- n) (mv-nth 1 (fx-list (i1 1) fr)) cs)
                (ge-sem (kadddr x) em (i2 4) (i2 5) sigs fnames env defs (1- n) (mv-nth 1 (fx-list (i1 1) fr)) cs))
           (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t :expand ((ge-sem x em cnt locs sigs fnames env defs n fr cs))
           :in-theory (disable g-expr g-args g-binds no-calls a-ev fx fv fx-list decl-ok-subset gkind g-tmp nfix
                               if-glue fx-list-append g-if-out scalar-ok)
           :use ((:instance if-glue (sc (i1 1)) (cc (i1 2)) (sa (i2 1)) (ca (i2 2)) (sb (i3 1)) (cb (i3 2))
                            (tmp (g-tmp 't (1+ (nfix (i3 4))))) (ta (i2 3))
                            (c (mv-nth 1 (a-ev (kadr x) env defs (1- n))))
                            (v (if (mv-nth 1 (a-ev (kadr x) env defs (1- n)))
                                   (mv-nth 1 (a-ev (kaddr x) env defs (1- n)))
                                 (mv-nth 1 (a-ev (kadddr x) env defs (1- n))))))
                 (:instance decl-ok-subset (a (i1 5)) (b (i2 5)))
                 (:instance decl-ok-subset (a (i2 5)) (b (i3 5)))))))

(defthm fv-true (equal (fv '(:true) fr) (mv nil t)))

(defthm scalar-ok-logical (equal (scalar-ok :logical v) (booleanp v)))

; (implies a b) is (if a b t); a-ev runs both, the code only what it needs
(defthm ge-implies
  (implies (and (equal (gkind x) :if) (equal (car x) 'implies)
                (ge-sem (kadr x) em cnt locs sigs fnames env defs (- n 2) fr cs)
                (ge-sem (kaddr x) em (i1 4) (i1 5) sigs fnames env defs (- n 3) (mv-nth 1 (fx-list (i1 1) fr)) cs))
           (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t :cases ((booleanp (mv-nth 1 (a-ev (kaddr x) env defs (- n 3)))))
           :expand ((ge-sem x em cnt locs sigs fnames env defs n fr cs))
           :in-theory (disable g-expr g-args g-binds no-calls a-ev fx fv fx-list decl-ok-subset gkind g-tmp nfix
                               if-glue fx-list-append g-if-out scalar-ok)
           :use ((:instance if-glue (sc (i1 1)) (cc (i1 2)) (sa (i2 1)) (ca (i2 2)) (sb nil) (cb '(:true))
                            (tmp (g-tmp 't (1+ (nfix (i2 4))))) (ta (i2 3))
                            (c (mv-nth 1 (a-ev (kadr x) env defs (- n 2))))
                            (v (if (mv-nth 1 (a-ev (kadr x) env defs (- n 2)))
                                   (mv-nth 1 (a-ev (kaddr x) env defs (- n 3)))
                                 t)))
                 (:instance decl-ok-subset (a (i1 5)) (b (i2 5)))))))

; ---- a lambda's bindings: each temporary holds its argument's value

(defmacro gbo (k) `(mv-nth ,k (g-binds vars xs em cnt locs sigs fnames)))

(defthm gb-sem-use
  (implies (and (gb-sem vars xs em cnt locs sigs fnames env defs n fr cs)
                (not (gbo 0)) (not (car (a-ev-list xs env defs n))) (no-calls :list xs sigs cs) (a-orc defs sigs cs) (em-ok em env fr)
                (decl-ok (gbo 4) fr) (no-prim-defs defs) (symbol-listp vars) (no-duplicatesp-equal vars)
                (equal (len vars) (len xs)))
           (and (equal (car (fx-list (gbo 1) fr)) :normal)
                (subsetp-equal (strip-cars (gbo 2)) vars)
                (em-ok em env (mv-nth 1 (fx-list (gbo 1) fr)))
                (em-ok (append (gbo 2) em) (pairlis$ vars (mv-nth 1 (a-ev-list xs env defs n)))
                       (mv-nth 1 (fx-list (gbo 1) fr)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (gb-sem) (g-binds a-ev-list fx-list fv no-calls em-ok decl-ok)))))

(defthm em-ok-bind
  (implies (and (em-ok em2 env2 fr) (equal (cdr (lkp tmp fr)) (cons ty v)) (scalar-ok ty v))
           (em-ok (cons (list* k tmp ty) em2) (cons (cons k v) env2) fr))
  :hints (("Goal" :expand ((em-ok (cons (list* k tmp ty) em2) (cons (cons k v) env2) fr))
           :in-theory (e/d (var-ok) (em-ok-necc scalar-ok))
           :use ((:instance em-ok-necc (em em2) (env env2)
                            (x (em-ok-witness (cons (list* k tmp ty) em2) (cons (cons k v) env2) fr)))))))

(defthm lkp-append-not-key
  (implies (not (member-equal k (strip-cars a))) (equal (lkp k (append a b)) (lkp k b))))

(defthm em-ok-self
  (implies (and (em-ok (append binds em) env2 fr) (em-ok em env fr)
                (not (member-equal k (strip-cars binds))) (consp (lkp k env)))
           (em-ok (append binds em) (cons (cons k (cdr (lkp k env))) env2) fr))
  :hints (("Goal" :expand ((em-ok (append binds em) (cons (cons k (cdr (lkp k env))) env2) fr))
           :in-theory (e/d (var-ok) (em-ok-necc))
           :use ((:instance em-ok-necc (em (append binds em)) (env env2)
                            (x (em-ok-witness (append binds em) (cons (cons k (cdr (lkp k env))) env2) fr)))
                 (:instance em-ok-necc (x k))))))

(defthm a-ev-sym
  (implies (symbolp x)
           (equal (a-ev x env defs n)
                  (cond ((zp n) (mv :fuel nil)) ((consp (lkp x env)) (mv nil (cdr (lkp x env)))) (t (mv :unbound nil)))))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm member-subset-not
  (implies (and (subsetp-equal a b) (not (member-equal k b))) (not (member-equal k a))))

(defthm ge-binds-self
  (implies (and (consp vars) (consp xs) (eq (car vars) (car xs))
                (gb-sem (cdr vars) (cdr xs) em cnt locs sigs fnames env defs (1- n) fr cs))
           (gb-sem vars xs em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t :expand ((gb-sem vars xs em cnt locs sigs fnames env defs n fr cs)
                                            (g-binds vars xs em cnt locs sigs fnames))
           :in-theory (disable g-expr g-binds g-args a-ev fx-list fv no-calls em-ok decl-ok member-subset-not)
           :use ((:instance member-subset-not (k (car vars)) (b (cdr vars))
                            (a (strip-cars (mv-nth 2 (g-binds (cdr vars) (cdr xs) em cnt locs sigs fnames)))))))))

; a bound argument: its statements, then its temporary assigned
(defthm bind-glue
  (let ((fra (mv-nth 1 (fx-list s fr))))
    (implies (and (equal (car (fx-list s fr)) :normal) (not (car (fv c fra)))
                  (consp (dty tmp fr)) (scalar-ok (car (dty tmp fr)) (mv-nth 1 (fv c fra))))
             (and (equal (fx-list (append s (list (list :assign (list :var tmp) c))) fr)
                         (mv :normal (put tmp (cons (car (dty tmp fr)) (mv-nth 1 (fv c fra))) fra)))
                  (equal (fx-list (append s (cons (list :assign (list :var tmp) c) ss)) fr)
                         (fx-list ss (put tmp (cons (car (dty tmp fr)) (mv-nth 1 (fv c fra))) fra))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fx fv fx-list dty scalar-ok)
           :expand ((fx-list (cons (list :assign (list :var tmp) c) ss)
                             (mv-nth 1 (fx-list s fr)))))))

(defthm decl-ok-binds-locs
  (implies (and (not (car (g-binds vars xs em cnt locs sigs fnames)))
                (decl-ok (mv-nth 4 (g-binds vars xs em cnt locs sigs fnames)) fr))
           (decl-ok locs fr))
  :hints (("Goal" :in-theory (disable g-binds decl-ok)
           :use ((:instance decl-ok-subset (a locs) (b (mv-nth 4 (g-binds vars xs em cnt locs sigs fnames))))))))

(defthm decl-ok-expr-locs
  (implies (and (not (car (g-expr x em cnt locs sigs fnames)))
                (decl-ok (mv-nth 5 (g-expr x em cnt locs sigs fnames)) fr))
           (decl-ok locs fr))
  :hints (("Goal" :in-theory (disable g-expr decl-ok)
           :use ((:instance decl-ok-subset (a locs) (b (mv-nth 5 (g-expr x em cnt locs sigs fnames))))))))

; a temporary made before is not assigned after
(defthm g-binds-keeps-locs
  (implies (and (not (car (g-binds vars xs em cnt locs sigs fnames))) (member-equal k (strip-cars locs)))
           (not (member-equal k (asg :list (mv-nth 1 (g-binds vars xs em cnt locs sigs fnames))))))
  :hints (("Goal" :in-theory (disable g-binds not-member-intersect)
           :use ((:instance not-member-intersect (y k) (a (strip-cars locs))
                            (b (asg :list (mv-nth 1 (g-binds vars xs em cnt locs sigs fnames)))))))))

(defthm g-expr-keeps-locs
  (implies (and (not (car (g-expr x em cnt locs sigs fnames))) (member-equal k (strip-cars locs)))
           (not (member-equal k (asg :list (mv-nth 1 (g-expr x em cnt locs sigs fnames))))))
  :hints (("Goal" :in-theory (disable g-expr not-member-intersect)
           :use ((:instance not-member-intersect (y k) (a (strip-cars locs))
                            (b (asg :list (mv-nth 1 (g-expr x em cnt locs sigs fnames)))))))))

(defmacro gb1 (k) `(mv-nth ,k (g-expr (car xs) em cnt locs sigs fnames)))
(defmacro gbf (k)
  `(mv-nth ,k (g-fresh (car vars) (gb1 3) (gb1 4) (gb1 5) (append fnames (em-names em)))))
(defmacro gbr (k) `(mv-nth ,k (g-binds (cdr vars) (cdr xs) em (gbf 2) (gbf 3) sigs fnames)))

(defthm ge-binds-cons
  (implies (and (consp vars) (consp xs) (not (eq (car vars) (car xs)))
                (ge-sem (car xs) em cnt locs sigs fnames env defs (1- n) fr cs)
                (gb-sem (cdr vars) (cdr xs) em (gbf 2) (gbf 3) sigs fnames env defs (1- n)
                        (fr-after (append (gb1 1) (list (list :assign (list :var (gbf 1)) (gb1 2)))) fr) cs))
           (gb-sem vars xs em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t :expand ((gb-sem vars xs em cnt locs sigs fnames env defs n fr cs)
                                            (g-binds vars xs em cnt locs sigs fnames))
           :in-theory (disable g-expr g-binds g-args a-ev fx-list fv no-calls em-ok decl-ok-subset fx-list-append
                               g-tmp nfix scalar-ok dty)
           :use ((:instance decl-ok-binds-locs (vars (cdr vars)) (xs (cdr xs)) (cnt (gbf 2)) (locs (gbf 3)))))))

; ---- a lambda: the bindings, then the body in the new scope

(defthm g-expr-lambda
  (implies (equal (gkind x) :lambda)
           (equal (g-expr x em cnt locs sigs fnames)
                  (let ((vars (kadr (car x))) (body (kaddr (car x))))
                    (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                                  (no-duplicatesp-eq vars) (true-listp x) (= (len vars) (len (cdr x)))))
                        (mv :syntax nil nil nil cnt locs)
                      (mv-let (e s binds cnt locs) (g-binds vars (cdr x) em cnt locs sigs fnames)
                        (if e (mv e nil nil nil cnt locs)
                          (mv-let (e sb cb tb cnt locs) (g-expr body (append binds em) cnt locs sigs fnames)
                            (if e (mv e nil nil nil cnt locs)
                              (mv nil (append s sb) cb tb cnt locs)))))))))
  :hints (("Goal" :expand ((g-expr x em cnt locs sigs fnames)) :in-theory (disable g-args g-binds))))

(defthm a-ev-lambda
  (implies (and (consp x) (consp (car x)))
           (equal (a-ev x env defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e vs) (a-ev-list (cdr x) env defs (1- n))
                      (if e (mv e nil)
                        (a-ev (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) defs (1- n)))))))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm no-calls-lambda
  (implies (and (consp x) (consp (car x)))
           (equal (no-calls :term x sigs cs) (and (no-calls :term (kaddr (car x)) sigs cs) (no-calls :list (cdr x) sigs cs))))
  :hints (("Goal" :expand ((no-calls :term x sigs cs)))))

(defthm tlf-true-listp (implies (true-listp x) (equal (true-list-fix x) x)))

(defmacro gl (k) `(mv-nth ,k (g-binds (kadr (car x)) (cdr x) em cnt locs sigs fnames)))

(defthm ge-lambda
  (implies (and (equal (gkind x) :lambda)
                (gb-sem (kadr (car x)) (cdr x) em cnt locs sigs fnames env defs (1- n) fr cs)
                (ge-sem (kaddr (car x)) (append (gl 2) em) (gl 3) (gl 4) sigs fnames
                        (pairlis$ (true-list-fix (kadr (car x))) (a-vals (cdr x) env defs (1- n)))
                        defs (1- n) (fr-after (gl 1) fr) cs))
           (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t :expand ((ge-sem x em cnt locs sigs fnames env defs n fr cs))
           :in-theory (disable g-expr g-binds g-args a-ev a-ev-list fx-list fv no-calls em-ok gkind scalar-ok)
           :use ((:instance decl-ok-expr-locs (x (kaddr (car x))) (em (append (gl 2) em)) (cnt (gl 3)) (locs (gl 4)))))))

; ---- the induction: it only dispatches to the cases

(defthm ge-atom-any
  (implies (atom x) (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :cases ((symbolp x)) :in-theory (disable ge-sem))))

(defthm ge-sem-thm
  (if (eq flag :args) (ga-sem x em cnt locs sigs fnames env defs n fr cs)
    (if (eq flag :binds) (gb-sem vars x em cnt locs sigs fnames env defs n fr cs)
      (ge-sem x em cnt locs sigs fnames env defs n fr cs)))
  :rule-classes nil
  :hints (("Goal" :induct (g-ind flag x vars em cnt locs sigs fnames env defs n fr) :do-not-induct t
           :in-theory (disable ge-sem ga-sem gb-sem g-expr g-args g-binds g-big kadr kaddr kadddr
                               g-fresh a-vals fx-list-append bind-glue))))
