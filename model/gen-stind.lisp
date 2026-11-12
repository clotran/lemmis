; gen-stind: the inductions over g-stmt/g-sacts (GEN.md "What remains" 4
; (a), step (2'')): stn-ok, the names fact, then gst-sem, from the case
; lemmas of gen-stst, gen-stcase and gen-stlst.
;
; Both are proved for `st-plain` statements: the stobj itself, field and
; element updates, if, and a lambda without mv whose stobj updates are
; plain -- the call-free, loop-free subset. cons (the results' tuple), a
; :sub call, the mv lambda and a tail self-call are not plain.

(in-package "ACL2")

(include-book "gen-stcase")
(include-book "gen-stlst")

(defun st-plain (flag x vars st)
  (declare (xargs :measure (acl2-count x)))
  (if (eq flag :acts)
      (cond ((or (atom vars) (atom x)) t)
            ((and (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car x))) (not (g-mvnth (car x))))
             (and (st-plain :term (car x) nil st) (st-plain :acts (cdr x) (cdr vars) st)))
            (t (st-plain :acts (cdr x) (cdr vars) st)))
    (cond ((symbolp x) t)
          ((or (atom x) (not (true-listp x)) (eq (car x) 'cons) (eq (car x) 'quote)) nil)
          ((eq (g-role (car x) st) :set) (st-plain :term (caddr x) nil st))
          ((eq (g-role (car x) st) :seti) (st-plain :term (cadddr x) nil st))
          ((eq (car x) 'if) (and (st-plain :term (caddr x) nil st) (st-plain :term (cadddr x) nil st)))
          ((consp (car x)) (and (not (member-equal 'mv (cadr (car x))))
                                (st-plain :acts (cdr x) (cadr (car x)) st) (st-plain :term (caddr (car x)) nil st)))
          (t nil))))

; ---- names: nmk, the names fact on its own (a: the names assigned)

(defun nmk (a f e l0 l1)
  (and (subsetp-equal l0 l1) (subsetp-equal a (strip-cars l1)) (not (intersectp-equal a (append f e (strip-cars l0))))))

(defthm nmk-app
  (implies (and (nmk a1 f e l0 l1) (nmk a2 f e l1 l2)) (nmk (append a1 a2) f e l0 l2))
  :hints (("Goal" :use ((:instance subsetp-trans (a l0) (b l1) (c l2)) (:instance subsetp-strip-cars (a l0) (b l1))
                        (:instance subsetp-strip-cars (a l1) (b l2))
                        (:instance subsetp-trans (a a1) (b (strip-cars l1)) (c (strip-cars l2)))))))

(defthm nmk-sub
  (implies (and (nmk a f e l0 l1) (subsetp-equal b a)) (nmk b f e l0 l1))
  :rule-classes nil
  :hints (("Goal" :use ((:instance subsetp-trans (a b) (b a) (c (strip-cars l1)))))))

(defthm nmk-e
  (implies (and (nmk a f e2 l0 l1) (subsetp-equal e e2)) (nmk a f e l0 l1))
  :rule-classes nil)

(defthm nmk-nil (equal (nmk nil f e l0 l1) (subsetp-equal l0 l1)))

(defthm nmk-fresh
  (implies (and (not (member-equal k f)) (not (member-equal k e)) (not (member-equal k (strip-cars l))))
           (nmk (list k) f e l (cons (cons k ty) (true-list-fix l)))))

(defthm nmk-cons-fresh
  (implies (and (not (member-equal k f)) (not (member-equal k e)) (not (member-equal k (strip-cars l0)))
                (nmk rest f e (cons (cons k ty) (true-list-fix l0)) l2))
           (nmk (cons k rest) f e l0 l2))
  :hints (("Goal" :in-theory (disable nmk nmk-app nmk-fresh true-list-fix)
           :use ((:instance nmk-fresh (l l0)) (:instance nmk-app (a1 (list k)) (a2 rest) (l1 (cons (cons k ty) (true-list-fix l0))) (l2 l2))))))

(in-theory (disable nmk))

(defthm asgv-assign-var (equal (asgv :list (list (list :assign (list :var k) c))) (list k))
  :hints (("Goal" :expand ((asgv :list (list (list :assign (list :var k) c))) (asgv :list nil)))))
(defthm asgv-assign-comp (equal (asgv :list (list (list :assign (list :comp o k) c))) nil)
  :hints (("Goal" :expand ((asgv :list (list (list :assign (list :comp o k) c))) (asgv :list nil)))))
(defthm asgv-assign-elem (equal (asgv :list (list (list :assign (list :elem o k i) c))) nil)
  :hints (("Goal" :expand ((asgv :list (list (list :assign (list :elem o k i) c))) (asgv :list nil)))))
(defthm asgv-if (equal (asgv :list (list (list :if c sa sb))) (append (asgv :list sa) (asgv :list sb)))
  :hints (("Goal" :expand ((asgv :list (list (list :if c sa sb))) (asgv :list nil)))))
(defthm asgv-nil (equal (asgv :list nil) nil))
(defthm true-listp-asgv (true-listp (asgv flag x)) :rule-classes :type-prescription)
(defthm append-nil-tl (implies (true-listp a) (equal (append a nil) a)))

(defthm stn-ok-nmk
  (equal (stn-ok x em cnt locs sigs fnames st outs)
         (implies (not (gtx 0)) (nmk (asgv :list (gtx 1)) fnames (em-names em) locs (gtx 3))))
  :hints (("Goal" :in-theory (e/d (stn-ok nmk) (g-stmt)))))

(defthm stan-ok-nmk
  (equal (stan-ok vars xs em cnt locs sigs fnames st)
         (implies (not (gac 0)) (nmk (asgv :list (gac 1)) fnames (em-names em) locs (gac 3))))
  :hints (("Goal" :in-theory (e/d (stan-ok nmk) (g-sacts)))))

(defthm asgv-nmk
  (implies (nmk (asg :list ss) f e l0 l1) (nmk (asgv :list ss) f e l0 l1))
  :rule-classes nil
  :hints (("Goal" :use (:instance nmk-sub (a (asg :list ss)) (b (asgv :list ss))))))

(defthm sn-ok-nmk-asg
  (implies (and (sn-ok x em cnt locs sigs fnames st) (not (gsx 0)))
           (nmk (asg :list (gsx 1)) fnames (em-names em) locs (gsx 5)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(nmk intersectp-app-r) (theory 'minimal-theory)) :use sn-ok-use)))

(defthm sn-ok-nmk
  (implies (and (sn-ok x em cnt locs sigs fnames st) (not (gsx 0)))
           (nmk (asgv :list (gsx 1)) fnames (em-names em) locs (gsx 5)))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-sexpr sn-ok)
           :use (sn-ok-nmk-asg (:instance asgv-nmk (ss (gsx 1)) (f fnames) (e (em-names em)) (l0 locs) (l1 (gsx 5)))))))

(defthm snv-ok-nmk
  (implies (and (snv-ok vars xs em cnt locs sigs fnames st) (not (gsv 0)))
           (nmk (asg :list (gsv 1)) fnames (em-names em) locs (gsv 4)))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(nmk intersectp-app-r) (theory 'minimal-theory)) :use snv-ok-use)))

(in-theory (disable stn-ok-nmk stan-ok-nmk))

; ---- stn-ok, case by case

(defmacro stn-dis ()
  ''(sn-ok-nmk sn-ok-holds g-stmt g-sacts g-sexpr g-svals g-settle g-fresh g-stable g-role g-obj g-comp g-tmp nfix sn-ok snv-ok em-names
     no-calls g-mvnth g-acts-place))

(defthm stn-set-sym
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :set) (symbolp (caddr x)) (sn-hyps) (no-calls :term x sigs nil))
           (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (current-theory :here) '(stn-ok-nmk))
                                                                     (stn-dis))
           :use ((:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-nmk (x (cadr x))) (:instance no-calls-set (cs nil))))))

(defthm stn-set-stable
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :set) (not (symbolp (caddr x))) (g-stable (k1 2)) (sn-hyps) (no-calls :term x sigs nil)
                (stn-ok (caddr x) em (k1 4) (k1 5) sigs fnames st outs))
           (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (current-theory :here) '(stn-ok-nmk))
                                                                     (stn-dis))
           :use ((:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-nmk (x (cadr x))) (:instance no-calls-set (cs nil))))))

(defthm stn-set-tmp
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :set) (not (symbolp (caddr x))) (not (g-stable (k1 2))) (sn-hyps)
                (no-calls :term x sigs nil)
                (stn-ok (caddr x) em (1+ (nfix (k1 4))) (locv) sigs fnames st outs))
           (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (current-theory :here) '(stn-ok-nmk))
                                                                     (cons 'g-fresh-out (stn-dis)))
           :use ((:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-nmk (x (cadr x))) (:instance no-calls-set (cs nil))
                 (:instance g-fresh-out (b 'v) (ty :int64) (cnt (k1 4)) (locs (k1 5)) (used (append fnames (em-names em))))))))

(defthm stn-sym
  (implies (symbolp x) (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) '(stn-ok-nmk)) (stn-dis)))))

; the element update: its names in the temporaries' order (i, v after both values)
(defthm nmk-seti-glue
  (implies (and (nmk a1 f e l0 l1) (nmk a2 f e l1 l2)
                (not (member-equal ki f)) (not (member-equal ki e)) (not (member-equal ki (strip-cars l2)))
                (not (member-equal kv f)) (not (member-equal kv e))
                (not (member-equal kv (strip-cars (cons (cons ki ty) (true-list-fix l2)))))
                (nmk a3 f e (cons (cons kv ty) (true-list-fix (cons (cons ki ty) (true-list-fix l2)))) l3))
           (nmk (append a1 (cons ki (append a2 (cons kv a3)))) f e l0 l3))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nmk-app nmk-cons-fresh true-list-fix)
           :use ((:instance nmk-sub (a (append a1 (append a2 (cons ki (cons kv a3))))) (b (append a1 (cons ki (append a2 (cons kv a3)))))
                            (l1 l3))
                 (:instance nmk-app (a1 a2) (a2 (cons ki (cons kv a3))) (l0 l1) (l1 l2) (l2 l3))
                 (:instance nmk-app (a1 a1) (a2 (append a2 (cons ki (cons kv a3)))) (l0 l0) (l1 l1) (l2 l3))
                 (:instance nmk-cons-fresh (k ki) (rest (cons kv a3)) (l0 l2) (l2 l3))
                 (:instance nmk-cons-fresh (k kv) (rest a3) (l0 (cons (cons ki ty) (true-list-fix l2))) (l2 l3))))))

(defthm stn-seti
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :seti) (sn-hyps) (no-calls :term x sigs nil)
                (stn-ok (cadddr x) em (c3) (locw) sigs fnames st outs))
           (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (current-theory :here) '(stn-ok-nmk))
                                                                     (list* 'g-fresh-out 'nmk-app 'nmk-cons-fresh (stn-dis)))
           :use ((:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-nmk (x (cadr x)))
                 (:instance sn-ok-holds (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance sn-ok-nmk (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance no-calls-set (cs nil))
                 (:instance g-fresh-out (b 'i) (ty :int64) (cnt (e2 4)) (locs (e2 5)) (used (append fnames (em-names em))))
                 (:instance g-fresh-out (b 'v) (ty :int64) (cnt (1+ (nfix (e2 4)))) (locs (loci))
                            (used (append fnames (em-names em))))
                 (:instance nmk-seti-glue (a1 (asgv :list (e1 1))) (a2 (asgv :list (e2 1))) (a3 (asgv :list (e3 1)))
                            (f fnames) (e (em-names em)) (l0 locs) (l1 (e1 5)) (l2 (e2 5)) (l3 (e3 3)) (ki (tmi)) (kv (tmv))
                            (ty :int64))))))

(defthm stn-if
  (implies (and (consp x) (true-listp x) (eq (car x) 'if) (sn-hyps) (no-calls :term x sigs nil)
                (stn-ok (caddr x) em (e1 4) (e1 5) sigs fnames st outs)
                (stn-ok (cadddr x) em (ia 2) (ia 3) sigs fnames st outs))
           (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (current-theory :here) '(stn-ok-nmk))
                                                                     (stn-dis))
           :use ((:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-nmk (x (cadr x))) (:instance no-calls-set (cs nil))))))

(defthm stn-lam
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (vars))) (sn-hyps) (no-calls :term x sigs nil)
                (stan-ok (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st)
                (stn-ok (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs))
           (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (current-theory :here) '(stn-ok-nmk stan-ok-nmk))
                                                                     (list* 'snv-ok-holds 'snv-ok-nmk (stn-dis)))
           :use ((:instance snv-ok-holds (vars (vars)) (xs (cdr x))) (:instance snv-ok-nmk (vars (vars)) (xs (cdr x)))
                 (:instance asgv-nmk (ss (gl1 1)) (f fnames) (e (em-names em)) (l0 locs) (l1 (gl1 4)))
                 (:instance nmk-e (a (asgv :list (lc 1))) (f fnames) (e (em-names em)) (e2 (em-names (append (gl1 2) em)))
                            (l0 (la 3)) (l1 (lc 3)))
                 (:instance no-calls-lambda-parts (cs nil))))))

(defthm stan-nil
  (implies (or (atom vars) (atom xs)) (stan-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (union-theories '(stan-ok-nmk g-sacts-nil nmk-nil subsetp-refl asgv-nil mv-nth-0-car mv-nth-cons-k
                                               car-cons cdr-cons (equal) (posp) (binary-+) (unary--))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))

(defthm stan-skip
  (implies (and (consp vars) (consp xs)
                (not (and (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs)))))
                (stan-ok (cdr vars) (cdr xs) em cnt locs sigs fnames st))
           (stan-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) '(stan-ok-nmk)) (stn-dis)))))

(defthm stan-act
  (implies (and (consp vars) (consp xs) (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs)))
                (stn-ok (car xs) em cnt locs sigs fnames st (list (car vars)))
                (stan-ok (cdr vars) (cdr xs) em (gc1 2) (gc1 3) sigs fnames st))
           (stan-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) '(stn-ok-nmk stan-ok-nmk)) (stn-dis)))))

; ---- the induction: st-plain's recursion, carrying every part's arguments
; as the case lemmas name them

(set-irrelevant-formals-ok t)
(set-ignore-ok t)

(defun-nx gst-ind (flag x vars em cnt locs sigs fnames st outs env s defs n fr heap o)
  (declare (xargs :measure (acl2-count x) :verify-guards nil
                  :hints (("Goal" :in-theory (disable g-sexpr g-stmt g-svals g-sacts a-sx a-st a-sx-list a-sacts sx-list
                                                      g-role g-mvnth g-tmp nfix okey put)))))
  (if (eq flag :acts)
      (let ((xs x))
        (cond ((or (atom vars) (atom xs)) nil)
              ((and (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs))))
               (list (gst-ind :term (car xs) nil em cnt locs sigs fnames st (list (car vars)) env s defs (1- n) fr heap o)
                     (gst-ind :acts (cdr xs) (cdr vars) em (gc1 2) (gc1 3) sigs fnames st outs env (sc1) defs (1- n) (frc1)
                              (put (okey o fr) (sc1) heap) o)))
              (t (gst-ind :acts (cdr xs) (cdr vars) em cnt locs sigs fnames st outs env s defs (1- n) fr heap o))))
    (cond ((symbolp x) nil)
          ((or (atom x) (not (true-listp x)) (eq (car x) 'cons) (eq (car x) 'quote)) nil)
          ((eq (g-role (car x) st) :set)
           (list (gst-ind :term (caddr x) nil em (k1 4) (k1 5) sigs fnames st outs env s defs (1- n)
                          (mv-nth 1 (sx-list (k1 1) fr heap)) heap o)
                 (gst-ind :term (caddr x) nil em (1+ (nfix (k1 4))) (locv) sigs fnames st outs env s defs (1- n) (frv) heap o)))
          ((eq (g-role (car x) st) :seti)
           (gst-ind :term (cadddr x) nil em (c3) (locw) sigs fnames st outs env s defs (1- n) (sfd) heap o))
          ((eq (car x) 'if)
           (list (gst-ind :term (caddr x) nil em (e1 4) (e1 5) sigs fnames st outs env s defs (1- n) (sfa) heap o)
                 (gst-ind :term (cadddr x) nil em (ia 2) (ia 3) sigs fnames st outs env s defs (1- n) (sfa) heap o)))
          ((consp (car x))
           (list (gst-ind :acts (cdr x) (vars) em (gl1 3) (gl1 4) sigs fnames st outs env s defs (1- n) (lfb) heap o)
                 (gst-ind :term (caddr (car x)) nil (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs (lenv) (ls1) defs (1- n)
                          (lfc) (lh1) o)))
          (t nil))))

(defthm no-calls-lambda-car
  (implies (and (consp x) (consp (car x)) (no-calls :term x sigs cs)) (no-calls :list (cdr x) sigs cs))
  :hints (("Goal" :use no-calls-lambda-parts)))

(defthm stn-set-any
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :set) (sn-hyps) (no-calls :term x sigs nil)
                (stn-ok (caddr x) em (k1 4) (k1 5) sigs fnames st outs)
                (stn-ok (caddr x) em (1+ (nfix (k1 4))) (locv) sigs fnames st outs))
           (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :do-not-induct t :cases ((symbolp (caddr x)) (and (not (symbolp (caddr x))) (g-stable (k1 2))))
           :in-theory (union-theories '(stn-set-sym stn-set-stable stn-set-tmp) (theory 'minimal-theory)))))

(defthm stn-ok-thm
  (implies (sn-hyps)
           (if (eq flag :acts)
               (implies (and (st-plain :acts x vars st) (no-calls :list x sigs nil)) (stan-ok vars x em cnt locs sigs fnames st))
             (implies (and (st-plain :term x nil st) (no-calls :term x sigs nil)) (stn-ok x em cnt locs sigs fnames st outs))))
  :rule-classes nil
  :hints (("Goal" :induct (gst-ind flag x vars em cnt locs sigs fnames st outs env s defs n fr heap o) :do-not-induct t
           :in-theory (union-theories '((:induction gst-ind) st-plain g-role-quote no-calls-set no-calls-list-parts no-calls-lambda-car
                                        no-calls-lambda-parts
                                        stn-sym stn-set-any stn-seti stn-if stn-lam stan-nil stan-skip stan-act)
                                      (theory 'minimal-theory)))))

(defthm stn-ok-holds
  (implies (and (sn-hyps) (st-plain :term x nil st) (no-calls :term x sigs nil)) (stn-ok x em cnt locs sigs fnames st outs))
  :hints (("Goal" :use (:instance stn-ok-thm (flag :term)))))

(defthm stan-ok-holds
  (implies (and (sn-hyps) (st-plain :acts xs vars st) (no-calls :list xs sigs nil)) (stan-ok vars xs em cnt locs sigs fnames st))
  :hints (("Goal" :use (:instance stn-ok-thm (flag :acts) (x xs)))))

; ---- gst-sem: each case from its parts' gst-sem (the induction) and
; stn-ok (stn-ok-holds)

(defmacro gst-min (&rest rs) `(union-theories '(g-role-quote ,@rs) (theory 'minimal-theory)))

(defthm gst-set-any
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :set) (sn-hyps) (st-plain :term (caddr x) nil st) (no-calls :term x sigs nil)
                (gst-sem (caddr x) em (k1 4) (k1 5) sigs fnames st outs env s defs (1- n)
                         (mv-nth 1 (sx-list (k1 1) fr heap)) heap o)
                (gst-sem (caddr x) em (1+ (nfix (k1 4))) (locv) sigs fnames st outs env s defs (1- n) (frv) heap o))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :cases ((symbolp (caddr x)) (and (not (symbolp (caddr x))) (g-stable (k1 2))))
           :in-theory (gst-min gst-set-sym gst-set-stable gst-set-tmp no-calls-set)
           :use ((:instance stn-ok-holds (x (caddr x)) (cnt (k1 4)) (locs (k1 5)))
                 (:instance stn-ok-holds (x (caddr x)) (cnt (1+ (nfix (k1 4)))) (locs (locv)))))))

(defthm gst-seti-any
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :seti) (sn-hyps) (st-plain :term (cadddr x) nil st) (no-calls :term x sigs nil)
                (gst-sem (cadddr x) em (c3) (locw) sigs fnames st outs env s defs (1- n) (sfd) heap o))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (gst-min gst-seti no-calls-set)
           :use ((:instance stn-ok-holds (x (cadddr x)) (cnt (c3)) (locs (locw)))))))

(defthm gst-if-any
  (implies (and (consp x) (true-listp x) (eq (car x) 'if) (sn-hyps) (no-calls :term x sigs nil)
                (st-plain :term (caddr x) nil st) (st-plain :term (cadddr x) nil st)
                (gst-sem (caddr x) em (e1 4) (e1 5) sigs fnames st outs env s defs (1- n) (sfa) heap o)
                (gst-sem (cadddr x) em (ia 2) (ia 3) sigs fnames st outs env s defs (1- n) (sfa) heap o))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (gst-min gst-if no-calls-set)
           :use ((:instance stn-ok-holds (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance stn-ok-holds (x (cadddr x)) (cnt (ia 2)) (locs (ia 3)))))))

(defthm gst-lam-any
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (vars))) (sn-hyps) (em-nostobj em st)
                (no-calls :term x sigs nil) (st-plain :acts (cdr x) (vars) st) (st-plain :term (caddr (car x)) nil st)
                (gsc-sem (vars) (cdr x) em (gl1 3) (gl1 4) sigs fnames st env s defs (1- n) (lfb) heap o)
                (gst-sem (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs (lenv) (ls1) defs (1- n) (lfc) (lh1) o))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (gst-min gst-lam no-calls-lambda-parts)
           :use ((:instance stan-ok-holds (vars (vars)) (xs (cdr x)) (cnt (gl1 3)) (locs (gl1 4)))
                 (:instance stn-ok-holds (x (caddr (car x))) (em (append (gl1 2) em)) (cnt (la 2)) (locs (la 3)))))))

(defthm gsc-act-any
  (implies (and (consp vars) (consp xs) (eq (g-role (car vars) st) :stobj) (not (eq (car vars) (car xs))) (not (g-mvnth (car xs)))
                (sn-hyps) (no-calls :list xs sigs nil) (st-plain :term (car xs) nil st) (st-plain :acts (cdr xs) (cdr vars) st)
                (gst-sem (car xs) em cnt locs sigs fnames st (list (car vars)) env s defs (1- n) fr heap o)
                (gsc-sem (cdr vars) (cdr xs) em (gc1 2) (gc1 3) sigs fnames st env (sc1) defs (1- n) (frc1)
                         (put (okey o fr) (sc1) heap) o))
           (gsc-sem vars xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (gst-min gsc-act no-calls-list-parts)
           :use ((:instance stn-ok-holds (x (car xs)) (outs (list (car vars))))
                 (:instance stan-ok-holds (vars (cdr vars)) (xs (cdr xs)) (cnt (gc1 2)) (locs (gc1 3)))))))

(defthm gst-sym
  (implies (symbolp x) (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o) (sx-list nil fr heap))
           :in-theory (disable g-stmt a-st sx-list no-calls em-ok decl-ok st-ok st-wf obj-at g-role))))

(defthm gst-sem-thm
  (implies (and (sn-hyps) (em-nostobj em st))
           (if (eq flag :acts)
               (implies (and (st-plain :acts x vars st) (no-calls :list x sigs nil))
                        (gsc-sem vars x em cnt locs sigs fnames st env s defs n fr heap o))
             (implies (and (st-plain :term x nil st) (no-calls :term x sigs nil))
                      (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))))
  :rule-classes nil
  :hints (("Goal" :induct (gst-ind flag x vars em cnt locs sigs fnames st outs env s defs n fr heap o) :do-not-induct t
           :in-theory (gst-min (:induction gst-ind) st-plain no-calls-set no-calls-list-parts no-calls-lambda-car
                               no-calls-lambda-parts em-nostobj-append em-nostobj-g-svals
                               gst-sym gst-set-any gst-seti-any gst-if-any gst-lam-any gsc-nil gsc-skip gsc-act-any))))

(defthm gst-sem-holds
  (implies (and (sn-hyps) (em-nostobj em st) (st-plain :term x nil st) (no-calls :term x sigs nil))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :use (:instance gst-sem-thm (flag :term)))))
