; gen-loopthm: g-fn-sem-loop, the function-level theorem for tail-only
; bodies (GEN.md, layer 3): f-invoke of g-fn's output on int64 literals
; answers a-ev's value of the body, whenever a-ev answers without an error
; within fuel n, at any fsem fuel past 6 + (len args) + n * (size + 2).

(in-package "ACL2")

(include-book "gen-loopfn")

(set-irrelevant-formals-ok t)

; ---- every iteration of the function's body is lp-ok

(defthm iter-one-lr
  (implies (do-hyps) (iter-one (lr 1) fs fn sigs defs rt (lr 3) body fr vs n v))
  :hints (("Goal" :in-theory (e/d (inv) (iter-ok g-ret a-ev fx-list tail-only em-ok decl-ok dty lp-hyps lp-ok
                                             g-em g-formals))
           :use iter-ok)))

(defthm iter-all-lr
  (implies (do-hyps) (iter-all (lr 1) fs fn sigs defs rt (lr 3) body))
  :hints (("Goal" :in-theory (e/d (iter-all) (iter-one g-ret iter-one-lr))
           :use ((:instance iter-one-lr
                            (fr (mv-nth 0 (iter-all-witness (lr 1) fs fn sigs defs rt (lr 3) body)))
                            (vs (mv-nth 1 (iter-all-witness (lr 1) fs fn sigs defs rt (lr 3) body)))
                            (n (mv-nth 2 (iter-all-witness (lr 1) fs fn sigs defs rt (lr 3) body)))
                            (v (mv-nth 3 (iter-all-witness (lr 1) fs fn sigs defs rt (lr 3) body))))))))

(defthm do-run
  (implies (and (do-hyps) (inv fs fn sigs defs rt (lr 3) body fr vs n v)
                (integerp m) (natp c) (<= (+ 2 (acl2-count (lr 1))) c) (< (* (nfix n) c) m))
           (do-ok (lr 1) fr heap procs m rt v))
  :hints (("Goal" :in-theory (disable g-ret do-run-abs iter-all-lr g-ret-tail-cf inv do-ok iter-all)
           :use ((:instance do-run-abs (s (lr 1)) (locs2 (lr 3)))
                 (:instance iter-all-lr)
                 (:instance g-ret-tail-cf (x body) (em (g-em fs)) (cnt 0) (locs nil) (self fn) (fnames (g-formals fs)))))))

; ---- the procedure's body: the DO, or (no CYCLE in it) the statements

(defthm f-ex-list-single
  (implies (and (integerp k) (< 1 k) (not (equal (car (f-ex x fr heap procs (1- k))) :normal)))
           (equal (f-ex-list (list x) fr heap procs k)
                  (list (car (f-ex x fr heap procs (1- k))) (mv-nth 1 (f-ex x fr heap procs (1- k)))
                        (mv-nth 2 (f-ex x fr heap procs (1- k))))))
  :hints (("Goal" :expand ((f-ex-list (list x) fr heap procs k)) :in-theory (disable f-ex f-ex-list-open))))

(defthm times-mono
  (implies (and (natp n) (<= a b)) (<= (* n a) (* n b)))
  :hints (("Goal" :nonlinearp t)))

(defmacro lfr () '(undef-locals (cons (list "r" rt) (g-locals (lr 3))) (fb fs args nil)))

(defmacro fr-hyps ()
  '(and (do-hyps) (no-duplicatesp-equal (cons "r" (g-formals fs))) (true-listp fs)
        (consp (lkp fn defs)) (equal (kadr (lkp fn defs)) fs)
        (int64-listp args) (equal (len args) (len fs))
        (not (car (a-ev body (pairlis$ fs args) defs n)))))

(defthm inv-frame
  (implies (fr-hyps) (inv fs fn sigs defs rt (lr 3) body (lfr) args n (mv-nth 1 (a-ev body (pairlis$ fs args) defs n))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (inv lp-hyps) (g-ret a-ev fn-frame-em-ok fn-frame-decl em-ok-int-dums g-ret-tail-cf
                                          undef-locals g-locals fb em-ok decl-ok dty g-formals g-em tail-only))
           :use ((:instance g-ret-tail-cf (x body) (em (g-em fs)) (cnt 0) (locs nil) (self fn) (fnames (g-formals fs)))
                 (:instance fn-frame-em-ok (vs fs) (ks args) (locs (lr 3)))
                 (:instance fn-frame-decl (vs fs) (ks args) (locs (lr 3)) (fnames (g-formals fs)))
                 (:instance em-ok-int-dums (fs0 fs) (ks args) (fr (lfr)))))))

(defmacro av () '(mv-nth 1 (a-ev body (pairlis$ fs args) defs n)))

(defthm body-lp
  (implies (fr-hyps) (lp-ok (car (fx-list (lr 1) (lfr))) (mv-nth 1 (fx-list (lr 1) (lfr))) rt (av) fn sigs defs n))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-ret a-ev inv-frame iter-lp iter-all-lr lp-ok inv fx-list
                                                       undef-locals g-locals fb)
           :use ((:instance inv-frame) (:instance iter-all-lr)
                 (:instance iter-lp (s (lr 1)) (locs2 (lr 3)) (fr (lfr)) (vs args) (v (av)))))))

(defthm body-plain
  (implies (and (fr-hyps) (not (g-has '(:cycle) (lr 1))) (integerp k) (< (+ 1 (* (nfix n) (+ 2 (acl2-count (lr 1))))) k))
           (and (equal (car (f-ex-list (lr 1) (lfr) heap procs k)) :return)
                (equal (caddr (f-ex-list (lr 1) (lfr) heap procs k)) heap)
                (ret-ok (mv-nth 1 (f-ex-list (lr 1) (lfr) heap procs k)) rt (av))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-ret a-ev body-lp g-ret-tail-cf no-cycle undef-locals g-locals fb lp-ok ret-ok
                               f-ex-list fx-list fx-list-is-f-ex-list times-ge g-has)
           :use ((:instance body-lp)
                 (:instance lp-ok-cases (st (car (fx-list (lr 1) (lfr)))) (fr2 (mv-nth 1 (fx-list (lr 1) (lfr))))
                            (self fn) (v (av)))
                 (:instance no-cycle (s (lr 1)) (fr (lfr)))
                 (:instance fx-list-is-f-ex-list (ss (lr 1)) (fr (lfr)))
                 (:instance times-ge (c (+ 2 (acl2-count (lr 1)))))
                 (:instance g-ret-tail-cf (x body) (em (g-em fs)) (cnt 0) (locs nil) (self fn) (fnames (g-formals fs)))))))

(defthm body-do
  (implies (and (fr-hyps) (integerp k) (< (+ 1 (* (nfix n) (+ 2 (acl2-count (lr 1))))) k))
           (and (equal (car (f-ex-list (list (list :do (lr 1))) (lfr) heap procs k)) :return)
                (equal (caddr (f-ex-list (list (list :do (lr 1))) (lfr) heap procs k)) heap)
                (ret-ok (mv-nth 1 (f-ex-list (list (list :do (lr 1))) (lfr) heap procs k)) rt (av))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (do-ok) (g-ret a-ev inv-frame do-run undef-locals g-locals fb ret-ok f-ex f-ex-list
                                   f-ex-list-open inv))
           :use ((:instance inv-frame)
                 (:instance do-run (fr (lfr)) (vs args) (v (av)) (m (1- k)) (c (+ 2 (acl2-count (lr 1)))))))))

;; ---- the function: f-invoke, once its body's run is known

(defthm f-invoke-fn
  (implies (and (int64-listp args) (equal (len args) (len fs)) (integerp fuel) (< (+ 6 (len fs)) fuel)
                (equal (car (f-ex-list b (undef-locals (cons (list "r" rt) locs) (fb fs args nil)) heap procs (1- fuel)))
                       :return)
                (ret-ok (mv-nth 1 (f-ex-list b (undef-locals (cons (list "r" rt) locs) (fb fs args nil)) heap procs (1- fuel)))
                        rt v))
           (equal (f-invoke (list :function nm pure rec (g-dummies fs) rt locs b) (g-lits args) caller heap procs fuel)
                  (mv nil v heap)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (ret-ok) (f-ex-list undef-locals f-bind fb g-dummies g-lits))
           :expand ((f-invoke (list :function nm pure rec (g-dummies fs) rt locs b) (g-lits args) caller heap procs fuel)))))

(defmacro gfs () '(kadr (lkp fn defs)))
(defmacro gr0 (k) `(mv-nth ,k (g-ret (kaddr (lkp fn defs)) (g-em (gfs)) 0 nil fn sigs (g-formals (gfs)))))
(defmacro gbody () '(if (g-has '(:cycle) (gr0 1)) (list (list :do (gr0 1))) (gr0 1)))

(defthm g-fn-open
  (implies (not (car (g-fn fn defs sigs)))
           (and (consp (lkp fn defs)) (symbol-listp (gfs)) (true-listp (gfs)) (no-duplicatesp-equal (cons "r" (g-formals (gfs))))
                (no-duplicatesp-equal (g-formals (gfs))) (not (member-equal "r" (g-formals (gfs))))
                (equal (kar (cdr (lkp fn sigs))) (gfs))
                (not (car (g-ret (kaddr (lkp fn defs)) (g-em (gfs)) 0 nil fn sigs (g-formals (gfs)))))
                (equal (mv-nth 1 (g-fn fn defs sigs))
                       (list :function (g-sym fn nil) t
                             (if (g-reaches (g-called (strip-cars sigs) (g-fcalls (gr0 1))) fn defs (1+ (len defs))) t nil)
                             (g-dummies (gfs)) (kadr (cdr (lkp fn sigs))) (g-locals (gr0 3)) (gbody)))))
  :hints (("Goal" :in-theory (disable g-ret g-reaches g-called g-fcalls g-has g-sym g-dummies g-locals g-em g-formals))))

(defthm ac-cons (equal (acl2-count (cons a b)) (+ 1 (acl2-count a) (acl2-count b)))
  :hints (("Goal" :expand ((acl2-count (cons a b))))))

(defthm count-body-sub
  (< (acl2-count s) (acl2-count (list :function nm pure rec dums rt locs (if c (list (list :do s)) s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable acl2-count) :cases (c))))

(defmacro sem-hyps ()
  '(and (not (mv-nth 0 (g-fn fn defs sigs)))
        (consp (lkp fn sigs)) (symbolp fn) (not (equal fn 'quote)) (not (equal fn 'if))
        (tail-only (kaddr (fd)) fn sigs) (no-prim-defs defs)
        (int64-listp args) (equal (len args) (len (kadr (fd))))
        (not (mv-nth 0 (a-ev (kaddr (fd)) (pairlis$ (kadr (fd)) args) defs n)))
        (integerp fuel)
        (< (+ 6 (len args) (* (nfix n) (+ 2 (acl2-count (mv-nth 1 (g-fn fn defs sigs)))))) fuel)))

(defthm g-fn-sem-loop-plain
  (implies (and (sem-hyps) (not (g-has '(:cycle) (gr0 1))))
           (equal (f-invoke (mv-nth 1 (g-fn fn defs sigs)) (g-lits args) caller heap procs fuel)
                  (mv nil (mv-nth 1 (a-ev (kaddr (fd)) (pairlis$ (kadr (fd)) args) defs n)) heap)))
  :hints (("Goal" :do-not-induct t
     :in-theory (disable g-fn g-ret g-reaches g-called g-fcalls g-has g-sym g-dummies g-lits g-locals g-em g-formals
                         fx-list a-ev tail-only undef-locals f-bind f-ex-list fb times-mono f-invoke ret-ok
                         acl2-count f-invoke-fn body-plain body-do kar kdr kadr kaddr)
     :use ((:instance body-plain (fs (gfs)) (body (kaddr (lkp fn defs))) (rt (kadr (cdr (lkp fn sigs)))) (k (1- fuel)))
           (:instance f-invoke-fn (fs (gfs)) (rt (kadr (cdr (lkp fn sigs))))
                      (v (mv-nth 1 (a-ev (kaddr (fd)) (pairlis$ (kadr (fd)) args) defs n)))
                      (nm (g-sym fn nil)) (pure t)
                      (rec (if (g-reaches (g-called (strip-cars sigs) (g-fcalls (gr0 1))) fn defs (1+ (len defs))) t nil))
                      (locs (g-locals (gr0 3))) (b (gbody)))
           (:instance count-body-sub (s (gr0 1)) (c (g-has '(:cycle) (gr0 1))) (nm (g-sym fn nil)) (pure t)
                      (rec (if (g-reaches (g-called (strip-cars sigs) (g-fcalls (gr0 1))) fn defs (1+ (len defs))) t nil))
                      (dums (g-dummies (gfs))) (rt (kadr (cdr (lkp fn sigs)))) (locs (g-locals (gr0 3))))
           (:instance times-mono (n (nfix n)) (a (+ 2 (acl2-count (gr0 1))))
                      (b (+ 2 (acl2-count (mv-nth 1 (g-fn fn defs sigs))))))))))

(defthm g-fn-sem-loop-do
  (implies (and (sem-hyps) (g-has '(:cycle) (gr0 1)))
           (equal (f-invoke (mv-nth 1 (g-fn fn defs sigs)) (g-lits args) caller heap procs fuel)
                  (mv nil (mv-nth 1 (a-ev (kaddr (fd)) (pairlis$ (kadr (fd)) args) defs n)) heap)))
  :hints (("Goal" :do-not-induct t
     :in-theory (disable g-fn g-ret g-reaches g-called g-fcalls g-has g-sym g-dummies g-lits g-locals g-em g-formals
                         fx-list a-ev tail-only undef-locals f-bind f-ex-list fb times-mono f-invoke ret-ok
                         acl2-count f-invoke-fn body-plain body-do kar kdr kadr kaddr)
     :use ((:instance body-do (fs (gfs)) (body (kaddr (lkp fn defs))) (rt (kadr (cdr (lkp fn sigs)))) (k (1- fuel)))
           (:instance f-invoke-fn (fs (gfs)) (rt (kadr (cdr (lkp fn sigs))))
                      (v (mv-nth 1 (a-ev (kaddr (fd)) (pairlis$ (kadr (fd)) args) defs n)))
                      (nm (g-sym fn nil)) (pure t)
                      (rec (if (g-reaches (g-called (strip-cars sigs) (g-fcalls (gr0 1))) fn defs (1+ (len defs))) t nil))
                      (locs (g-locals (gr0 3))) (b (gbody)))
           (:instance count-body-sub (s (gr0 1)) (c (g-has '(:cycle) (gr0 1))) (nm (g-sym fn nil)) (pure t)
                      (rec (if (g-reaches (g-called (strip-cars sigs) (g-fcalls (gr0 1))) fn defs (1+ (len defs))) t nil))
                      (dums (g-dummies (gfs))) (rt (kadr (cdr (lkp fn sigs)))) (locs (g-locals (gr0 3))))
           (:instance times-mono (n (nfix n)) (a (+ 2 (acl2-count (gr0 1))))
                      (b (+ 2 (acl2-count (mv-nth 1 (g-fn fn defs sigs))))))))))

(defthm g-fn-sem-loop
  (implies (sem-hyps)
           (equal (f-invoke (mv-nth 1 (g-fn fn defs sigs)) (g-lits args) caller heap procs fuel)
                  (mv nil (mv-nth 1 (a-ev (kaddr (fd)) (pairlis$ (kadr (fd)) args) defs n)) heap)))
  :hints (("Goal" :cases ((g-has '(:cycle) (gr0 1)))
           :in-theory (disable g-fn g-ret f-invoke a-ev g-has g-fn-sem-loop-plain g-fn-sem-loop-do)
           :use (g-fn-sem-loop-plain g-fn-sem-loop-do))))
