; gen-stret: g-sret (a function reading a stobj, answering a value) against
; a-sx on sx-list (GEN.md "What remains" 4b, value functions): on call-free
; bodies its statements answer :return, the heap unchanged, "r" holding
; a-sx's value, of the function's type. gen-ret's gr-sem for g-ret, on
; g-sexpr (gs-sem-holds) in place of g-expr.

(in-package "ACL2")

(include-book "gen-stcase")

(defmacro srty () '(kadr (cdr (lkp self sigs))))
(defun sret-ok (fr2 rt v) (and (equal (cdr (lkp "r" fr2)) (cons rt v)) (scalar-ok rt v)))

(defmacro gsr-ifp ()
  '(and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4) (< (g-chain x nil nil) 3)))

; ---- openers

(defthm g-sret-if
  (implies (gsr-ifp)
           (equal (g-sret x em cnt locs self sigs fnames st)
                  (mv-let (e sc cc tc cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                    (if (or e (not (eq tc :logical))) (mv (or e :type) nil cnt locs)
                      (mv-let (e sa cnt locs) (g-sret (caddr x) em cnt locs self sigs fnames st)
                        (if e (mv e nil cnt locs)
                          (mv-let (e sb cnt locs) (g-sret (cadddr x) em cnt locs self sigs fnames st)
                            (if e (mv e nil cnt locs)
                              (mv nil (append sc (list (list :if cc sa sb))) cnt locs)))))))))
  :hints (("Goal" :in-theory (disable g-sexpr g-chain) :expand ((g-sret x em cnt locs self sigs fnames st)))))

(defthm g-sret-other
  (implies (not (gsr-ifp))
           (equal (g-sret x em cnt locs self sigs fnames st)
                  (if (and (consp x) (or (eq (car x) self) (eq (car x) 'if))) (mv :stobj nil cnt locs)
                    (mv-let (e s c ty cnt locs) (g-sexpr x em cnt locs sigs fnames st)
                      (if (or e (not (equal ty (srty)))) (mv (or e :type) nil cnt locs)
                        (mv nil (append s (list (list :assign '(:var "r") c) '(:return))) cnt locs))))))
  :hints (("Goal" :in-theory (disable g-sexpr g-chain) :expand ((g-sret x em cnt locs self sigs fnames st)))))

(in-theory (disable g-sret))

(defthm a-sx-free-open
  (implies (and (g-st-free x st) (not (zp n))) (equal (a-sx x env s st defs n) (a-ev x env defs n)))
  :hints (("Goal" :expand ((a-sx x env s st defs n)) :in-theory (disable a-ev g-st-free))))

;; a-sx of an if, whether or not it reads the stobj
(defthm a-sx-if-all
  (implies (and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4) (not (g-role 'if st)))
           (equal (a-sx x env s st defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e c) (a-sx (cadr x) env s st defs (1- n))
                      (cond (e (mv e nil))
                            (c (a-sx (caddr x) env s st defs (1- n)))
                            (t (a-sx (cadddr x) env s st defs (1- n))))))))
  :hints (("Goal" :cases ((g-st-free x st)))
          ("Subgoal 2" :in-theory (e/d (gs-ifp) (g-st-free a-ev a-sx-list)))
          ("Subgoal 1" :in-theory (e/d (kadr kaddr kadddr) (a-ev a-sx-list g-role))
           :expand ((a-sx x env s st defs n) (g-st-free x st) (g-st-free-list (cdr x) st)
                    (g-st-free-list (cddr x) st) (g-st-free-list (cdddr x) st)
                    (a-sx (cadr x) env s st defs (1- n)) (a-sx (caddr x) env s st defs (1- n))
                    (a-sx (cadddr x) env s st defs (1- n))))))

; ---- names: g-sret only adds locals

(defmacro r1 (k) `(mv-nth ,k (g-sexpr (cadr x) em cnt locs sigs fnames st)))
(defmacro ra (k) `(mv-nth ,k (g-sret (caddr x) em (r1 4) (r1 5) self sigs fnames st)))
(defmacro rb (k) `(mv-nth ,k (g-sret (cadddr x) em (ra 2) (ra 3) self sigs fnames st)))
(defmacro grx (k) `(mv-nth ,k (g-sret x em cnt locs self sigs fnames st)))

(defun-nx gsr-ind (x em cnt locs self sigs fnames st env s defs n fr heap)
  (declare (xargs :measure (acl2-count x) :verify-guards nil))
  (if (gsr-ifp)
      (list (gsr-ind (caddr x) em (r1 4) (r1 5) self sigs fnames st env s defs (1- n)
                     (mv-nth 1 (sx-list (r1 1) fr heap)) heap)
            (gsr-ind (cadddr x) em (ra 2) (ra 3) self sigs fnames st env s defs (1- n)
                     (mv-nth 1 (sx-list (r1 1) fr heap)) heap))
    t))

(defthm no-calls-if-any
  (implies (and (consp x) (eq (car x) 'if) (no-calls :term x sigs cs))
           (and (no-calls :term (cadr x) sigs cs) (no-calls :term (caddr x) sigs cs) (no-calls :term (cadddr x) sigs cs)))
  :hints (("Goal" :use (:instance no-calls-set) :in-theory (theory 'minimal-theory))))

(defun srn (x em cnt locs self sigs fnames st)
  (mv-let (e ss cnt2 locs2) (g-sret x em cnt locs self sigs fnames st)
    (declare (ignore ss cnt2))
    (implies (and (sn-hyps) (no-calls :term x sigs nil) (not e)) (subsetp-equal locs locs2))))

(defmacro gx (k) `(mv-nth ,k (g-sexpr x em cnt locs sigs fnames st)))

(defthm g-sret-leaf-out
  (implies (and (not (gsr-ifp)) (not (grx 0)))
           (and (not (gx 0)) (equal (gx 3) (srty))
                (equal (grx 1) (append (gx 1) (list (list :assign '(:var "r") (gx 2)) '(:return))))
                (equal (grx 3) (gx 5))))
  :hints (("Goal" :in-theory (disable g-sexpr g-chain g-sret-if))))

(defthm g-sret-if-out
  (implies (and (gsr-ifp) (not (grx 0)))
           (and (not (r1 0)) (equal (r1 3) :logical) (not (ra 0)) (not (rb 0))
                (equal (grx 1) (append (r1 1) (list (list :if (r1 2) (ra 1) (rb 1)))))
                (equal (grx 3) (rb 3))))
  :hints (("Goal" :in-theory (disable g-sexpr g-chain g-sret-other))))

(in-theory (disable g-sret-leaf-out g-sret-if-out))

(defthm srn-leaf
  (implies (not (gsr-ifp)) (srn x em cnt locs self sigs fnames st))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(srn) (theory 'minimal-theory))
           :use ((:instance sn-ok-holds) (:instance sn-ok-use) g-sret-leaf-out))))

(defthm srn-if
  (implies (and (gsr-ifp)
                (srn (caddr x) em (r1 4) (r1 5) self sigs fnames st)
                (srn (cadddr x) em (ra 2) (ra 3) self sigs fnames st))
           (srn x em cnt locs self sigs fnames st))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(srn) (theory 'minimal-theory))
           :use ((:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-use (x (cadr x)))
                 (:instance no-calls-if-any (cs nil)) g-sret-if-out
                 (:instance subsetp-trans (a locs) (b (r1 5)) (c (ra 3)))
                 (:instance subsetp-trans (a locs) (b (ra 3)) (c (rb 3)))))))

(defthm srn-thm
  (srn x em cnt locs self sigs fnames st)
  :hints (("Goal" :induct (gsr-ind x em cnt locs self sigs fnames st env s defs n fr heap)
           :in-theory (union-theories '(srn-leaf srn-if gsr-ind) (theory 'minimal-theory)))))

(defthm srn-ok
  (implies (and (sn-hyps) (no-calls :term x sigs nil) (not (grx 0)))
           (subsetp-equal locs (grx 3)))
  :hints (("Goal" :use srn-thm :in-theory (union-theories '(srn) (theory 'minimal-theory)))))

(in-theory (disable srn))

; ---- the leaf: s, then r = c, RETURN

(defthm sret-glue
  (let ((fra (mv-nth 1 (sx-list s fr heap))))
    (implies (and (equal (dty "r" fr) (list rt)) (equal (car (sx-list s fr heap)) :normal)
                  (equal (mv-nth 2 (sx-list s fr heap)) heap)
                  (not (car (sv c fra heap))) (scalar-ok rt (mv-nth 1 (sv c fra heap))))
             (equal (sx-list (append s (list (list :assign '(:var "r") c) '(:return))) fr heap)
                    (mv :return (put "r" (cons rt (mv-nth 1 (sv c fra heap))) fra) heap))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (sx-list-append dty) (sv sx-list-is-f-ex-list))
           :use ((:instance dty-after-sx (k "r") (ss s)))
           :expand ((sx-list (list (list :assign '(:var "r") c) '(:return)) (mv-nth 1 (sx-list s fr heap)) heap)
                    (sx (list :assign '(:var "r") c) (mv-nth 1 (sx-list s fr heap)) heap)
                    (:free (f h) (sx-list '((:return)) f h)) (:free (f h) (sx '(:return) f h))))))

; ---- what is proved

(defmacro gsr-hyps (locs2)
  `(and (no-calls :term x sigs nil) (em-ok em env fr) (decl-ok ,locs2 fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (obj-is o s fr heap) (sn-hyps) (em-nostobj em st) (equal (dty "r" fr) (list (srty)))))

(defun gsr-sem (x em cnt locs self sigs fnames st env s defs n fr heap o)
  (mv-let (e ss cnt2 locs2) (g-sret x em cnt locs self sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-sx x env s st defs n)
      (implies (and (not e) (not ae) (gsr-hyps locs2))
               (mv-let (stt fr2 h2) (sx-list ss fr heap)
                 (and (equal stt :return) (equal h2 heap) (sret-ok fr2 (srty) v)))))))

(defthm gsr-sem-use
  (implies (and (gsr-sem x em cnt locs self sigs fnames st env s defs n fr heap o)
                (not (grx 0)) (not (car (a-sx x env s st defs n))) (gsr-hyps (grx 3)))
           (and (equal (car (sx-list (grx 1) fr heap)) :return)
                (equal (mv-nth 2 (sx-list (grx 1) fr heap)) heap)
                (sret-ok (mv-nth 1 (sx-list (grx 1) fr heap)) (srty) (mv-nth 1 (a-sx x env s st defs n)))))
  :hints (("Goal" :in-theory (e/d (gsr-sem) (g-sret a-sx sx-list sret-ok no-calls em-ok decl-ok st-ok obj-is dty)))))

(in-theory (disable gsr-sem sret-ok))

(defthm sret-ok-put
  (equal (sret-ok (put "r" val fr) rt v) (and (equal val (cons rt v)) (scalar-ok rt v)))
  :hints (("Goal" :in-theory (enable sret-ok))))

(defthm gsr-leaf
  (implies (not (gsr-ifp))
           (gsr-sem x em cnt locs self sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(gsr-sem sret-ok-put mv-nth-0-car mv-nth-cons-k car-cons cdr-cons (equal) (cons))
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (g-sret-leaf-out (:instance gs-sem-holds) (:instance gs-sem-use)
                 (:instance sret-glue (rt (srty)) (s (gx 1)) (c (gx 2)))))))

(defmacro rfa () '(mv-nth 1 (sx-list (r1 1) fr heap)))

(defmacro rifc () '(mv-nth 1 (a-sx (cadr x) env s st defs (1- n))))

;; the hypotheses as a function, so the branches' instances stay small
(defun gsr-h (x em env fr locs2 self sigs fnames defs st o s heap)
  (gsr-hyps locs2))

(defthm gsr-h-use
  (implies (and (gsr-sem x em cnt locs self sigs fnames st env s defs n fr heap o)
                (not (grx 0)) (not (car (a-sx x env s st defs n))) (gsr-h x em env fr (grx 3) self sigs fnames defs st o s heap))
           (and (equal (car (sx-list (grx 1) fr heap)) :return)
                (equal (mv-nth 2 (sx-list (grx 1) fr heap)) heap)
                (sret-ok (mv-nth 1 (sx-list (grx 1) fr heap)) (srty) (mv-nth 1 (a-sx x env s st defs n)))))
  :hints (("Goal" :in-theory (union-theories '(gsr-h) (theory 'minimal-theory)) :use gsr-sem-use)))

(defmacro gsr-ctx ()
  '(and (gsr-ifp) (not (grx 0)) (not (car (a-sx x env s st defs n)))
        (gsr-h x em env fr (grx 3) self sigs fnames defs st o s heap)))

(defthm gsr-if-test
  (implies (gsr-ctx)
           (and (not (zp n)) (not (car (a-sx (cadr x) env s st defs (1- n))))
                (equal (car (sx-list (r1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (r1 1) fr heap)) heap)
                (not (car (sv (r1 2) (rfa) heap))) (equal (mv-nth 1 (sv (r1 2) (rfa) heap)) (rifc)) (booleanp (rifc))
                (implies (rifc) (not (car (a-sx (caddr x) env s st defs (1- n)))))
                (implies (not (rifc)) (not (car (a-sx (cadddr x) env s st defs (1- n)))))
                (equal (car (a-sx x env s st defs n))
                       (if (rifc) (car (a-sx (caddr x) env s st defs (1- n))) (car (a-sx (cadddr x) env s st defs (1- n)))))
                (equal (mv-nth 1 (a-sx x env s st defs n))
                       (if (rifc) (mv-nth 1 (a-sx (caddr x) env s st defs (1- n)))
                         (mv-nth 1 (a-sx (cadddr x) env s st defs (1- n)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(gsr-h a-sx-if-all mv-nth-0-car mv-nth-cons-k car-cons cdr-cons (equal) (cons)
                                        scalar-ok (zp) (unary--) (binary-+))
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (g-sret-if-out
                 (:instance no-calls-if-any (cs nil))
                 (:instance gs-sem-holds (x (cadr x)) (n (1- n)))
                 (:instance gs-sem-use (x (cadr x)) (n (1- n)))
                 (:instance srn-ok (x (caddr x)) (cnt (r1 4)) (locs (r1 5)))
                 (:instance srn-ok (x (cadddr x)) (cnt (ra 2)) (locs (ra 3)))
                 (:instance subsetp-trans (a (r1 5)) (b (ra 3)) (c (rb 3)))
                 (:instance decl-ok-subset (a (r1 5)) (b (rb 3)))))))

(defthm gsr-if-hyps
  (implies (gsr-ctx)
           (and (not (ra 0)) (not (rb 0)) (equal (grx 1) (append (r1 1) (list (list :if (r1 2) (ra 1) (rb 1)))))
                (gsr-h (caddr x) em env (rfa) (ra 3) self sigs fnames defs st o s heap)
                (gsr-h (cadddr x) em env (rfa) (rb 3) self sigs fnames defs st o s heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(gsr-h decl-ok-after-sx obj-is-after-sx dty-after-sx)
                                      (theory 'minimal-theory))
           :use (g-sret-if-out
                 (:instance no-calls-if-any (cs nil))
                 (:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-use (x (cadr x)))
                 (:instance srn-ok (x (cadddr x)) (cnt (ra 2)) (locs (ra 3)))
                 (:instance decl-ok-subset (a (ra 3)) (b (rb 3)))
                 (:instance em-ok-after-sx (s (r1 1)))))))

(defthm gsr-if
  (implies (and (gsr-ifp)
                (gsr-sem (caddr x) em (r1 4) (r1 5) self sigs fnames st env s defs (1- n) (rfa) heap o)
                (gsr-sem (cadddr x) em (ra 2) (ra 3) self sigs fnames st env s defs (1- n) (rfa) heap o))
           (gsr-sem x em cnt locs self sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gsr-sem x em cnt locs self sigs fnames st env s defs n fr heap o))
           :in-theory (union-theories '(mv-nth-0-car) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance gsr-h (locs2 (grx 3)))
                 gsr-if-test gsr-if-hyps
                 (:instance gsr-h-use (x (caddr x)) (cnt (r1 4)) (locs (r1 5)) (n (1- n)) (fr (rfa)))
                 (:instance gsr-h-use (x (cadddr x)) (cnt (ra 2)) (locs (ra 3)) (n (1- n)) (fr (rfa)))
                 (:instance sif-st-glue (sc (r1 1)) (cc (r1 2)) (sa (ra 1)) (sb (rb 1)))))))

(defthm gsr-sem-thm
  (gsr-sem x em cnt locs self sigs fnames st env s defs n fr heap o)
  :hints (("Goal" :induct (gsr-ind x em cnt locs self sigs fnames st env s defs n fr heap)
           :in-theory (union-theories '(gsr-leaf gsr-if gsr-ind) (theory 'minimal-theory)))))
