; gen-proof: g-expr's output, run by fx (fsem without fuel, gen-cf.lisp),
; answers what a-ev answers on the source, for call-free code: the
; statements answer :normal and the code's value is a-ev's, of the type
; g-expr inferred (ge-sem). The induction is g-ind (gen-names.lisp); each
; of g-expr's cases is its own lemma, taking its parts' results as
; hypotheses, so the induction only dispatches.

(in-package "ACL2")

(include-book "gen-names")

; ---- the invariants
;
; em-ok: each variable bound in both em and a-ev's env names, in the frame,
; a variable holding the env's value, of em's type. decl-ok: each temporary
; is declared in the frame with its type.

(defun var-ok (x em env fr)
  (let ((b (lkp x em)) (a (lkp x env)))
    (implies (and (consp b) (consp (cdr b)) (consp a))
             (and (equal (cdr (lkp (cadr b) fr)) (cons (cddr b) (cdr a)))
                  (scalar-ok (cddr b) (cdr a))))))

(defun-sk em-ok (em env fr) (forall x (var-ok x em env fr)))

(defun decl-ok (locs fr)
  (if (atom locs) t
    (and (equal (dty (car (car locs)) fr) (list (cdr (car locs)))) (decl-ok (cdr locs) fr))))

(defconst *g-prims* '(binary-+ binary-* unary-- < equal eql = not nfix zp natp integerp implies the-check hide))

; ACL2 defines none of the primitives: a-ev calls them, not a definition
(defun no-prim-defs (defs) (not (intersectp-equal (strip-cars defs) *g-prims*)))

(defun cf-exprs (cs) (if (atom cs) t (and (cf-expr (car cs)) (cf-exprs (cdr cs)))))

(defun fvs-ok (cs ts vs fr)
  (if (atom cs) (atom vs)
    (mv-let (err v) (fv (car cs) fr)
      (and (consp vs) (not err) (equal v (car vs)) (scalar-ok (car ts) (car vs))
           (fvs-ok (cdr cs) (cdr ts) (cdr vs) fr)))))

; ---- invariant lemmas

(defthm decl-ok-member
  (implies (and (decl-ok locs fr) (member-equal p locs)) (equal (dty (car p) fr) (list (cdr p)))))

(defthm decl-ok-subset
  (implies (and (subsetp-equal a b) (decl-ok b fr)) (decl-ok a fr))
  :hints (("Goal" :induct (len a))))

(defthm decl-ok-after
  (equal (decl-ok locs (mv-nth 1 (fx-list s fr))) (decl-ok locs fr)))

(defthm decl-ok-put
  (implies (and (decl-ok locs fr) (equal (dty k fr) (list (car v))) (consp v))
           (decl-ok locs (put k v fr))))

(defthm not-member-intersect
  (implies (and (member-equal y a) (not (intersectp-equal b a))) (not (member-equal y b))))

(defthm var-ok-after
  (implies (and (var-ok x em env fr) (not (intersectp-equal (asg :list s) (em-names em))))
           (var-ok x em env (mv-nth 1 (fx-list s fr))))
  :hints (("Goal" :in-theory (disable fx-list fx-list-keeps not-member-intersect) :do-not-induct t
           :use ((:instance fx-list-keeps (n (cadr (lkp x em))))
                 (:instance not-member-intersect (y (cadr (lkp x em))) (a (em-names em)) (b (asg :list s)))))))

(defthm var-ok-put
  (implies (and (var-ok x em env fr) (not (member-equal k (em-names em))))
           (var-ok x em env (put k v fr)))
  :hints (("Goal" :do-not-induct t)))

(defthm em-ok-after
  (implies (and (em-ok em env fr) (not (intersectp-equal (asg :list s) (em-names em))))
           (em-ok em env (mv-nth 1 (fx-list s fr))))
  :hints (("Goal" :do-not-induct t :expand ((em-ok em env (mv-nth 1 (fx-list s fr))))
           :in-theory (disable var-ok em-ok-necc fx-list)
           :use ((:instance em-ok-necc (x (em-ok-witness em env (mv-nth 1 (fx-list s fr)))))))))

(defthm em-ok-put
  (implies (and (em-ok em env fr) (not (member-equal k (em-names em))))
           (em-ok em env (put k v fr)))
  :hints (("Goal" :do-not-induct t :expand ((em-ok em env (put k v fr)))
           :in-theory (disable var-ok em-ok-necc put)
           :use ((:instance em-ok-necc (x (em-ok-witness em env (put k v fr))))))))

(defthm lkp-strip-cars (implies (consp (lkp f al)) (member-equal f (strip-cars al))))

(defthm no-prim-defs-lkp
  (implies (and (no-prim-defs defs) (member-equal f *g-prims*)) (not (consp (lkp f defs))))
  :hints (("Goal" :in-theory (disable lkp-strip-cars) :use lkp-strip-cars)))

(in-theory (disable no-prim-defs))

; ---- the source calls no translated function

; cs: the translated functions the source may call (layer 3, calls (c));
; nil for call-free source
(defun no-calls (flag x sigs cs)
  (declare (xargs :measure (acl2-count x)))
  (cond ((eq flag :list) (if (atom x) t (and (no-calls :term (car x) sigs cs) (no-calls :list (cdr x) sigs cs))))
        ((or (atom x) (eq (car x) 'quote)) t)
        ((consp (car x)) (and (no-calls :term (kaddr (car x)) sigs cs) (no-calls :list (cdr x) sigs cs)))
        (t (and (or (not (consp (lkp (car x) sigs))) (member-equal (car x) cs)) (no-calls :list (cdr x) sigs cs)))))

(defun int64-listp (ks) (if (atom ks) (null ks) (and (int64p (car ks)) (int64-listp (cdr ks)))))

; a-ev's answer on a call of f, the arguments' values vals
(defun a-call (f vals defs n)
  (let ((d (lkp f defs)))
    (if (consp d) (a-ev (kaddr d) (pairlis$ (true-list-fix (kadr d)) vals) defs n) (a-prim f vals))))

; the oracle is a-ev's: on int64 arguments, wherever a-ev of a call of an f
; in cs answers without an error, f-call-val answers that value, of f's type
(defun-sk a-orc (defs sigs cs)
  (forall (f vals n)
    (implies (and (member-equal f cs) (int64-listp vals) (not (mv-nth 0 (a-call f vals defs n))))
             (and (equal (f-call-val (g-sym f nil) vals) (mv nil (mv-nth 1 (a-call f vals defs n))))
                  (scalar-ok (kadr (cdr (lkp f sigs))) (mv-nth 1 (a-call f vals defs n)))))))

(defthm member-equal-nil (not (member-equal a nil)))

(defthm a-orc-nil (a-orc defs sigs nil) :hints (("Goal" :in-theory (enable a-orc))))

(in-theory (disable a-orc))

; ---- what is proved, per flag: run (here); that the output is call-free
; (cf-stmts, cf-expr) is its own induction, the next lemma set

(defun ge-sem (x em cnt locs sigs fnames env defs n fr cs)
  (mv-let (e s c ty cnt2 locs2) (g-expr x em cnt locs sigs fnames)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-ev x env defs n)
      (implies (and (not e) (not ae) (no-calls :term x sigs cs) (a-orc defs sigs cs) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs))
               (mv-let (st fr2) (fx-list s fr)
                 (mv-let (fe fvv) (fv c fr2)
                   (and (equal st :normal) (not fe) (equal fvv v) (scalar-ok ty v))))))))

(defun ga-sem (xs em cnt locs sigs fnames env defs n fr cs)
  (mv-let (e s codes ts cnt2 locs2) (g-args xs em cnt locs sigs fnames)
    (declare (ignore cnt2))
    (mv-let (ae vs) (a-ev-list xs env defs n)
      (implies (and (not e) (not ae) (no-calls :list xs sigs cs) (a-orc defs sigs cs) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs))
               (mv-let (st fr2) (fx-list s fr)
                 (and (equal st :normal) (fvs-ok codes ts vs fr2)))))))

(defun gb-sem (vars xs em cnt locs sigs fnames env defs n fr cs)
  (mv-let (e s binds cnt2 locs2) (g-binds vars xs em cnt locs sigs fnames)
    (declare (ignore cnt2))
    (mv-let (ae vs) (a-ev-list xs env defs n)
      (implies (and (not e) (not ae) (no-calls :list xs sigs cs) (a-orc defs sigs cs) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (symbol-listp vars) (no-duplicatesp-equal vars) (equal (len vars) (len xs)))
               (mv-let (st fr2) (fx-list s fr)
                 (and (equal st :normal) (subsetp-equal (strip-cars binds) vars)
                      (em-ok em env fr2) (em-ok (append binds em) (pairlis$ vars vs) fr2)))))))

; ---- a-ev and fx-list, opened one step

(defthm a-ev-list-open
  (implies (consp xs)
           (equal (a-ev-list xs env defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e v) (a-ev (car xs) env defs (1- n))
                      (if e (mv e nil)
                        (mv-let (e vs) (a-ev-list (cdr xs) env defs (1- n))
                          (if e (mv e nil) (mv nil (cons v vs)))))))))
  :hints (("Goal" :expand ((a-ev-list xs env defs n)))))

(defthm a-ev-list-end
  (implies (atom xs) (equal (a-ev-list xs env defs n) (if (zp n) (mv :fuel nil) (mv nil nil))))
  :hints (("Goal" :expand ((a-ev-list xs env defs n)))))

(defthm a-ev-list-zp (implies (zp n) (equal (a-ev-list xs env defs n) (mv :fuel nil)))
  :hints (("Goal" :expand ((a-ev-list xs env defs n)))))

(defthm a-ev-zp (implies (zp n) (equal (a-ev x env defs n) (mv :fuel nil)))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm fx-list-nil (implies (atom s) (equal (fx-list s fr) (mv :normal fr)))
  :hints (("Goal" :expand ((fx-list s fr)))))

(defthm fx-list-one (equal (fx-list (list a) fr) (mv-let (st fr2) (fx a fr) (mv st fr2)))
  :hints (("Goal" :expand ((fx-list (list a) fr) (fx-list nil (mv-nth 1 (fx a fr)))))))

(defthm cf-stmts-one (equal (cf-stmts (list a)) (cf-stmt a)) :hints (("Goal" :expand ((cf-stmts (list a))))))

(in-theory (disable a-ev-list))

; ---- the primitives: fsem's operator on the code is a-prim on the values

(defthm g-unop-prim (implies (not (car (g-unop op c ty))) (member-equal op *g-prims*)))
(defthm g-binop-prim (implies (not (car (g-binop op a ta b tb))) (member-equal op *g-prims*)))

(defthm g-binop-types
  (implies (not (and (equal ta :int64) (equal tb :int64))) (car (g-binop op a ta b tb))))

(defthm g-unop-cf
  (implies (and (not (car (g-unop op c ty))) (cf-expr c)) (cf-expr (mv-nth 1 (g-unop op c ty)))))

(defthm g-binop-cf
  (implies (and (not (car (g-binop op a ta b tb))) (cf-expr a) (cf-expr b)) (cf-expr (mv-nth 1 (g-binop op a ta b tb)))))

(defthm g-unop-sem
  (implies (and (not (car (g-unop op c ty))) (not (car (a-prim op vs)))
                (not (car (fv c fr))) (equal (mv-nth 1 (fv c fr)) (car vs)) (scalar-ok ty (car vs)))
           (and (implies (cf-expr c) (cf-expr (mv-nth 1 (g-unop op c ty))))
                (not (car (fv (mv-nth 1 (g-unop op c ty)) fr)))
                (equal (mv-nth 1 (fv (mv-nth 1 (g-unop op c ty)) fr)) (mv-nth 1 (a-prim op vs)))
                (scalar-ok (mv-nth 2 (g-unop op c ty)) (mv-nth 1 (a-prim op vs)))))
  :hints (("Goal" :expand ((fv (list :neg c) fr) (fv (list :not c) fr) (fv (list :max '(:int 0) c) fr)
                           (fv (list :le c '(:int 0)) fr) (fv (list :ge c '(:int 0)) fr)))))

(defthm g-binop-sem
  (implies (and (not (car (g-binop op a ta b tb))) (not (car (a-prim op vs)))
                (not (car (fv a fr))) (equal (mv-nth 1 (fv a fr)) (car vs)) (scalar-ok ta (car vs))
                (not (car (fv b fr))) (equal (mv-nth 1 (fv b fr)) (cadr vs)) (scalar-ok tb (cadr vs)))
           (and (implies (and (cf-expr a) (cf-expr b)) (cf-expr (mv-nth 1 (g-binop op a ta b tb))))
                (not (car (fv (mv-nth 1 (g-binop op a ta b tb)) fr)))
                (equal (mv-nth 1 (fv (mv-nth 1 (g-binop op a ta b tb)) fr)) (mv-nth 1 (a-prim op vs)))
                (scalar-ok (mv-nth 2 (g-binop op a ta b tb)) (mv-nth 1 (a-prim op vs)))))
  :hints (("Goal" :expand ((fv (list :add a b) fr) (fv (list :mul a b) fr) (fv (list :eq a b) fr)
                           (fv (list :lt a b) fr)))))

(defthm disjoint-via-subset
  (implies (and (subsetp-equal a (append b c)) (not (intersectp-equal d b)) (not (intersectp-equal d c)))
           (not (intersectp-equal a d))))

(defthm no-calls-cons
  (implies (consp xs)
           (equal (no-calls :list xs sigs cs) (and (no-calls :term (car xs) sigs cs) (no-calls :list (cdr xs) sigs cs)))))

(in-theory (disable em-ok var-ok))

(defthm len-pos (implies (< 0 (len x)) (consp x)))

(defthm cf-exprs-cons
  (implies (consp cs) (equal (cf-exprs cs) (and (cf-expr (car cs)) (cf-exprs (cdr cs))))))

(defthm fvs-ok-cons
  (implies (consp cs)
           (equal (fvs-ok cs ts vs fr)
                  (and (consp vs) (not (car (fv (car cs) fr))) (equal (mv-nth 1 (fv (car cs) fr)) (car vs))
                       (scalar-ok (car ts) (car vs)) (fvs-ok (cdr cs) (cdr ts) (cdr vs) fr)))))

; ---- g-expr's cases

(defthm ge-sym
  (implies (symbolp x) (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :expand ((g-expr x em cnt locs sigs fnames) (a-ev x env defs n))
           :in-theory (e/d (var-ok) (em-ok-necc)) :use ((:instance em-ok-necc (x x))))))

(defthm ge-atom
  (implies (and (atom x) (not (symbolp x))) (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :expand ((g-expr x em cnt locs sigs fnames)))))

(defthm ge-quote
  (implies (and (consp x) (eq (car x) 'quote)) (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :expand ((g-expr x em cnt locs sigs fnames) (a-ev x env defs n)))))

(defthm ge-the-check
  (implies (and (consp x) (eq (car x) 'the-check)
                (ge-sem (kadddr x) em cnt locs sigs fnames env defs (- n 4) fr cs))
           (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t :expand ((g-expr x em cnt locs sigs fnames) (a-ev x env defs n)
                                            (no-calls :term x sigs cs))
           :in-theory (disable g-expr no-calls))))

(defthm gkind-call-facts
  (implies (equal (gkind x) :call)
           (and (consp x) (not (equal (car x) 'quote)) (not (equal (car x) 'if)) (not (equal (car x) 'implies))
                (not (consp (car x))) (not (equal (car x) 'the-check))))
  :rule-classes :forward-chaining)

(defthm g-expr-call
  (implies (equal (gkind x) :call)
           (equal (g-expr x em cnt locs sigs fnames)
                  (mv-let (e s cs ts cnt locs) (g-args (cdr x) em cnt locs sigs fnames)
                    (cond (e (mv e nil nil nil cnt locs))
                          ((not (true-listp x)) (mv :syntax nil nil nil cnt locs))
                          ((consp (lkp (car x) sigs))
                           (let ((sig (cdr (lkp (car x) sigs))))
                             (if (and (equal (len (kar sig)) (len cs)) (all-int64-types ts))
                                 (mv nil s (list :fcall (g-sym (car x) nil) cs) (kadr sig) cnt locs)
                               (mv :type nil nil nil cnt locs))))
                          ((= (len cs) 1) (mv-let (e c ty) (g-unop (car x) (car cs) (car ts)) (mv e s c ty cnt locs)))
                          ((= (len cs) 2) (mv-let (e c ty) (g-binop (car x) (car cs) (car ts) (cadr cs) (cadr ts))
                                            (mv e s c ty cnt locs)))
                          (t (mv :unknown nil nil nil cnt locs))))))
  :hints (("Goal" :expand ((g-expr x em cnt locs sigs fnames)) :in-theory (disable g-args))))

(defthm a-ev-prim
  (implies (and (consp x) (not (equal (car x) 'quote)) (not (equal (car x) 'if)) (not (consp (car x)))
                (not (consp (lkp (car x) defs))))
           (equal (a-ev x env defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e vs) (a-ev-list (cdr x) env defs (1- n))
                      (if e (mv e nil) (a-prim (car x) vs))))))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm no-calls-call
  (implies (and (consp x) (not (equal (car x) 'quote)) (not (consp (car x))))
           (equal (no-calls :term x sigs cs) (and (or (not (consp (lkp (car x) sigs))) (member-equal (car x) cs)) (no-calls :list (cdr x) sigs cs))))
  :hints (("Goal" :expand ((no-calls :term x sigs cs)))))

(defthm ge-prim-call
  (implies (and (equal (gkind x) :call) (not (consp (lkp (car x) sigs)))
                (ga-sem (cdr x) em cnt locs sigs fnames env defs (1- n) fr cs))
           (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable gkind g-expr g-args no-calls g-unop g-binop a-prim fv a-ev g-expr-names g-args-names scalar-ok))))

; ---- a call of a translated function: the oracle (layer 3, calls (c))

(defthm a-ev-call
  (implies (and (consp x) (not (equal (car x) 'quote)) (not (equal (car x) 'if)) (not (consp (car x))))
           (equal (a-ev x env defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e vs) (a-ev-list (cdr x) env defs (1- n))
                      (if e (mv e nil) (a-call (car x) vs defs (1- n)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm fvs-ok-fv-list
  (implies (and (fvs-ok cs ts vs fr) (true-listp vs))
           (equal (fv-list cs fr) (list nil vs)))
  :hints (("Goal" :induct (fvs-ok cs ts vs fr) :expand ((fv-list cs fr)))))

(defthm fvs-ok-int64
  (implies (and (fvs-ok cs ts vs fr) (all-int64-types ts) (true-listp vs)) (int64-listp vs))
  :hints (("Goal" :induct (fvs-ok cs ts vs fr))))

(defun ael-ind (xs n) (if (or (zp n) (atom xs)) nil (ael-ind (cdr xs) (1- n))))

(defthm true-listp-a-ev-list (true-listp (mv-nth 1 (a-ev-list xs env defs n)))
  :hints (("Goal" :induct (ael-ind xs n) :expand ((a-ev-list xs env defs n)))))

(defthm fv-fcall-list
  (equal (fv (list :fcall name cs) fr)
         (mv-let (err vs) (fv-list cs fr)
           (if err (mv err nil) (mv-let (err v) (f-call-val name vs) (if err (mv err nil) (mv nil v))))))
  :hints (("Goal" :expand ((fv (list :fcall name cs) fr)))))

(defthm ge-fcall
  (implies (and (equal (gkind x) :call) (consp (lkp (car x) sigs))
                (ga-sem (cdr x) em cnt locs sigs fnames env defs (1- n) fr cs))
           (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable gkind g-expr g-args g-unop g-binop a-prim fv a-ev g-expr-names g-args-names a-call
                               a-orc-necc)
           :expand ((no-calls :term x sigs cs))
           :use (a-ev-call
                 (:instance a-orc-necc (f (car x)) (vals (mv-nth 1 (a-ev-list (cdr x) env defs (1- n)))) (n (1- n)))))))

(defthm ge-call
  (implies (and (equal (gkind x) :call) (ga-sem (cdr x) em cnt locs sigs fnames env defs (1- n) fr cs))
           (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :cases ((consp (lkp (car x) sigs))) :in-theory (disable ge-sem ga-sem gkind))))

(defthm ge-args-nil
  (implies (atom xs) (ga-sem xs em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :expand ((g-args xs em cnt locs sigs fnames)))))

(defmacro ga1 (k) `(mv-nth ,k (g-expr (car xs) em cnt locs sigs fnames)))
(defmacro ga2 (k) `(mv-nth ,k (g-args (cdr xs) em (ga1 4) (ga1 5) sigs fnames)))

(defthm ge-args-cons
  (implies (and (consp xs)
                (ge-sem (car xs) em cnt locs sigs fnames env defs (1- n) fr cs)
                (ga-sem (cdr xs) em (ga1 4) (ga1 5) sigs fnames env defs (1- n) (mv-nth 1 (fx-list (ga1 1) fr)) cs))
           (ga-sem xs em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t :expand ((g-args xs em cnt locs sigs fnames) (fvs-ok (cons a b) ts vs fr))
           :in-theory (disable g-expr g-args no-calls fv-agree fx-list-agree fx-list decl-ok-subset disjoint-via-subset fv)
           :use ((:instance fv-agree (e (ga1 2)) (fr (mv-nth 1 (fx-list (ga1 1) fr)))
                            (fr2 (mv-nth 1 (fx-list (ga2 1) (mv-nth 1 (fx-list (ga1 1) fr))))))
                 (:instance fx-list-agree (ns (ev-names (ga1 2))) (s (ga2 1)) (fr (mv-nth 1 (fx-list (ga1 1) fr))))
                 (:instance decl-ok-subset (a (ga1 5)) (b (ga2 5)))
                 (:instance disjoint-via-subset (a (ev-names (ga1 2))) (b (em-names em)) (c (strip-cars (ga1 5)))
                            (d (asg :list (ga2 1))))))))

(defthm ge-big
  (implies (and (equal (gkind x) :big)
                (ge-sem (if (g-big (kadr x)) (kaddr x) (kadr x)) em cnt locs sigs fnames env defs
                        (if (g-big (kadr x)) (- n 3) (- n 2)) fr cs))
           (ge-sem x em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :do-not-induct t :expand ((g-expr x em cnt locs sigs fnames) (no-calls :term x sigs cs))
           :in-theory (disable g-expr no-calls))))

(defthm em-ok-nil-env
  (em-ok em nil fr)
  :hints (("Goal" :in-theory (enable em-ok var-ok))))

(defthm ge-binds-nil
  (implies (or (atom vars) (atom xs)) (gb-sem vars xs em cnt locs sigs fnames env defs n fr cs))
  :hints (("Goal" :expand ((g-binds vars xs em cnt locs sigs fnames)))))
