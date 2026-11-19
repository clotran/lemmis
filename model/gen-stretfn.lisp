; gen-stretfn: the FUNCTION g-st-fn emits for a function reading a stobj and
; answering a value (GEN.md "What remains" 4b): f-invoke of it, the stobj's
; object passed first, answers a-sx's value of the body, the heap unchanged.
; gen-stfn's g-st-fn-sem for the subroutine, with gen-stret's gsr-sem-thm.

(in-package "ACL2")

(include-book "gen-stret")
(include-book "gen-stfn")

; ---- g-sret keeps lf-ok (gen-stlf's sl-sexpr through the if)

(defun srl (x em cnt locs self sigs fnames st)
  (mv-let (e ss cnt2 locs2) (g-sret x em cnt locs self sigs fnames st)
    (declare (ignore ss cnt2))
    (implies (and (no-calls :term x sigs nil) (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames))))

(defthm srl-leaf
  (implies (not (gsr-ifp)) (srl x em cnt locs self sigs fnames st))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(srl) (theory 'minimal-theory))
           :use (g-sret-leaf-out (:instance sl-sexpr)))))

(defthm srl-if
  (implies (and (gsr-ifp)
                (srl (caddr x) em (r1 4) (r1 5) self sigs fnames st)
                (srl (cadddr x) em (ra 2) (ra 3) self sigs fnames st))
           (srl x em cnt locs self sigs fnames st))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(srl) (theory 'minimal-theory))
           :use (g-sret-if-out (:instance sl-sexpr (x (cadr x))) (:instance no-calls-if-any (cs nil))))))

(defthm srl-thm
  (srl x em cnt locs self sigs fnames st)
  :hints (("Goal" :induct (gsr-ind x em cnt locs self sigs fnames st env s defs n fr heap)
           :in-theory (union-theories '(srl-leaf srl-if gsr-ind) (theory 'minimal-theory)))))

(defthm srl-holds
  (implies (and (no-calls :term x sigs nil) (not (grx 0)) (lf-ok locs fnames)) (lf-ok (grx 3) fnames))
  :hints (("Goal" :use srl-thm :in-theory (union-theories '(srl) (theory 'minimal-theory)))))

(in-theory (disable srl))

; ---- "r" is no formal's name (each ends in "_")

(defthm app-underscore-not-r
  (implies (character-listp a) (not (equal (coerce (append a '(#\_)) 'string) "r")))
  :hints (("Goal" :use (:instance coerce-inverse-1 (x (append a '(#\_)))) :cases ((consp a))
           :do-not-induct t :expand ((append a '(#\_)) (append (cdr a) '(#\_))))))

(defthm g-formal-not-r (not (equal (g-formal v) "r"))
  :hints (("Goal" :in-theory (e/d (string-append g-formal) (g-sym)))))

(defthm r-not-g-formals (not (member-equal "r" (g-formals vs)))
  :hints (("Goal" :in-theory (disable g-formal))))

; ---- the FUNCTION's shape

(defmacro rfn () '(g-st-fn (list fn formals (list nil) t x) gdefs sigs st))
(defmacro rsn () '(append (g-formals (g-st-vals formals st)) (st-objs st)))
(defmacro grf (k) `(mv-nth ,k (g-sret x (g-em (g-st-vals formals st)) 0 nil fn sigs (rsn) st)))

(defthm g-st-fn-fshape
  (implies (not (mv-nth 0 (rfn)))
           (and (not (grf 0)) (consp (lkp fn sigs)) (no-duplicatesp-equal (g-formals (g-st-vals formals st)))
                (equal (mv-nth 1 (rfn))
                       (list :function (g-sym fn nil) t
                             (if (g-reaches (g-called (strip-cars sigs) (g-fcalls (grf 1))) fn gdefs (1+ (len gdefs))) t nil)
                             (append (g-st-dummies formals (list nil) st) (g-dummies (g-st-vals formals st)))
                             (kadr (cdr (lkp fn sigs))) (g-locals (grf 3)) (grf 1)))))
  :hints (("Goal" :in-theory (e/d (kar kadr kaddr kadddr) (g-stmt g-sret g-reaches g-called g-fcalls g-ccalls g-has
                                                           g-st-dummies g-dummies g-locals g-em g-formals g-st-vals
                                                           g-role g-st-outs-ok)))))

; ---- the callee frame: the object dummy (intent(in)), the values, "r", the temporaries

(defthm f-bind-obj-in
  (implies (and (posp fuel) (equal (cdr (lkp ob caller)) (list* :obj intent key)))
           (equal (f-bind (cons (list o :in c) ds) (cons (list :var ob) as) caller callee outs heap procs fuel)
                  (f-bind ds as caller (put o (list* :obj :in key) callee) outs heap procs (1- fuel))))
  :hints (("Goal" :expand ((f-bind (cons (list o :in c) ds) (cons (list :var ob) as) caller callee outs heap procs fuel)))))

(defmacro rfr (rt) `(undef-locals (cons (list "r" ,rt) (g-locals locs)) (fb vs ks (put o (list* :obj :in key) nil))))

(defthm rfr-open
  (equal (rfr rt) (undef-locals (g-locals locs) (put "r" (cons rt :undef) (fb vs ks (put o (list* :obj :in key) nil)))))
  :hints (("Goal" :expand ((undef-locals (cons (list "r" rt) (g-locals locs)) (fb vs ks (put o (list* :obj :in key) nil))))
           :in-theory (enable kar kadr))))

(defthm rfr-ok
  (implies (and (no-duplicatesp-equal (g-formals vs)) (lf-ok locs (append (g-formals vs) objs))
                (member-equal o objs) (not (member-equal o (g-formals vs))) (not (equal o "r"))
                (int64-listp ks) (equal (len ks) (len vs)) (equal (cdr (lkp key heap)) s))
           (and (em-ok (g-em vs) (pairlis$ vs ks) (rfr rt))
                (decl-ok locs (rfr rt))
                (equal (dty "r" (rfr rt)) (list rt))
                (obj-is o s (rfr rt) heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (obj-is dty lf-ok) (em-ok-undef-locals undef-locals em-ok fb intersectp-subset-l decl-ok
                                         lkp-undef-locals-other member-lkeys-g-locals not-member-intersect-cars
                                         decl-ok-g-locals))
           :use ((:instance em-ok-undef-locals (em (g-em vs)) (env (pairlis$ vs ks))
                            (fr (fb vs ks (put o (list* :obj :in key) nil))) (l (cons (list "r" rt) (g-locals locs))))
                 (:instance intersectp-subset-l (a (lkeys (g-locals locs))) (b (strip-cars locs)) (c (g-formals vs)))
                 (:instance lf-ok-append-parts (a (g-formals vs)) (b objs))
                 (:instance decl-ok-g-locals (fr (put "r" (cons rt :undef) (fb vs ks (put o (list* :obj :in key) nil)))))
                 (:instance lkp-undef-locals-other (n "r") (l (g-locals locs))
                            (fr (put "r" (cons rt :undef) (fb vs ks (put o (list* :obj :in key) nil)))))
                 (:instance lkp-undef-locals-other (n o) (l (g-locals locs))
                            (fr (put "r" (cons rt :undef) (fb vs ks (put o (list* :obj :in key) nil)))))
                 (:instance member-lkeys-g-locals (n "r"))
                 (:instance member-lkeys-g-locals (n o))
                 (:instance not-member-intersect-cars (b objs) (l (strip-cars locs)))
                 (:instance lkp-fb-put-obj (v (list* :obj :in key)))))))

(in-theory (disable rfr-open))

; ---- the body's run at that frame (gsr-sem-thm)

(defmacro rfn-hyps ()
  '(and (no-calls :term x sigs nil)
        (not (g-role 'if st)) (not (g-role 'implies st)) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
        (not (member-equal o (g-formals vs))) (not (equal o "r")) (member-equal o (st-objs st))
        (int64-listp ks) (equal (len ks) (len vs)) (equal (cdr (lkp key heap)) s)
        (st-ok st o s) (em-nostobj (g-em vs) st) (not (car (a-sx x (pairlis$ vs ks) s st defs n)))))

(defmacro rgv (k) `(mv-nth ,k (g-sret x (g-em vs) 0 nil fn sigs (append (g-formals vs) (st-objs st)) st)))

(defthm rfn-run
  (implies (and (rfn-hyps) (not (rgv 0)) (no-duplicatesp-equal (g-formals vs)))
           (let ((fr (undef-locals (cons (list "r" (kadr (cdr (lkp fn sigs)))) (g-locals (rgv 3)))
                                   (fb vs ks (put o (list* :obj :in key) nil)))))
             (and (equal (car (sx-list (rgv 1) fr heap)) :return)
                  (equal (mv-nth 2 (sx-list (rgv 1) fr heap)) heap)
                  (sret-ok (mv-nth 1 (sx-list (rgv 1) fr heap)) (kadr (cdr (lkp fn sigs)))
                           (mv-nth 1 (a-sx x (pairlis$ vs ks) s st defs n))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(subsetp-append-r lf-ok-nil-stfn) (theory 'minimal-theory))
           :use ((:instance srl-holds (em (g-em vs)) (cnt 0) (locs nil) (self fn) (fnames (append (g-formals vs) (st-objs st))))
                 (:instance rfr-ok (locs (rgv 3)) (objs (st-objs st)) (rt (kadr (cdr (lkp fn sigs)))))
                 (:instance gsr-sem-thm (em (g-em vs)) (cnt 0) (locs nil) (self fn) (fnames (append (g-formals vs) (st-objs st)))
                            (env (pairlis$ vs ks))
                            (fr (undef-locals (cons (list "r" (kadr (cdr (lkp fn sigs)))) (g-locals (rgv 3)))
                                              (fb vs ks (put o (list* :obj :in key) nil)))))
                 (:instance gsr-sem-use (em (g-em vs)) (cnt 0) (locs nil) (self fn) (fnames (append (g-formals vs) (st-objs st)))
                            (env (pairlis$ vs ks))
                            (fr (undef-locals (cons (list "r" (kadr (cdr (lkp fn sigs)))) (g-locals (rgv 3)))
                                              (fb vs ks (put o (list* :obj :in key) nil)))))))))

; ---- the FUNCTION

(defthm g-st-dummies-objs
  (implies (member-equal d (g-st-dummies formals outs st)) (member-equal (car d) (st-objs st)))
  :hints (("Goal" :in-theory (disable g-role g-obj g-comp))))

(defthm sret-ok-r
  (implies (sret-ok fr rt v) (and (consp (cdr (lkp "r" fr))) (equal (car (cdr (lkp "r" fr))) rt)
                                  (equal (cdr (cdr (lkp "r" fr))) v) (scalar-ok rt v)))
  :hints (("Goal" :in-theory (enable sret-ok))))

;; f-invoke of such a FUNCTION, on its body's run
(defthm f-invoke-sret
  (implies (and (equal (car (sx-list body (rfr rt) heap)) :return)
                (equal (mv-nth 2 (sx-list body (rfr rt) heap)) heap)
                (sret-ok (mv-nth 1 (sx-list body (rfr rt) heap)) rt v)
                (equal (cdr (lkp ob caller)) (list* :obj intent key))
                (int64-listp ks) (equal (len ks) (len vs))
                (integerp fuel) (< (+ 7 (len ks) (acl2-count body)) fuel))
           (equal (f-invoke (list :function nm t rec (cons (list o :in c) (g-dummies vs)) rt (g-locals locs) body)
                            (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                  (mv nil v heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (sret-ok) (sx-list f-ex-list undef-locals fb g-dummies g-lits g-locals f-bind
                               sx-ok-is-f-ex-list sx-list-is-f-ex-list f-ex-list-open))
           :expand ((:free (p) (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel)))
           :use ((:instance sx-ok-is-f-ex-list (ss body) (fr (rfr rt)) (k (1- fuel)))))))

(defthm g-sret-fn-sem
  (let ((vs (g-st-vals formals st)))
    (implies (and (not (mv-nth 0 (rfn)))
                  (equal (g-st-dummies formals (list nil) st) (list (list o :in c)))
                  (no-calls :term x sigs nil)
                  (not (g-role 'if st)) (not (g-role 'implies st)) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                  (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                  (not (member-equal o (g-formals vs))) (not (equal o "r"))
                  (int64-listp ks) (equal (len ks) (len vs)) (equal (cdr (lkp key heap)) s)
                  (st-ok st o s) (not (car (a-sx x (pairlis$ vs ks) s st defs n)))
                  (equal (cdr (lkp ob caller)) (list* :obj intent key))
                  (integerp fuel) (< (+ 7 (len ks) (acl2-count (grf 1))) fuel))
             (equal (f-invoke (mv-nth 1 (rfn)) (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                    (mv nil (mv-nth 1 (a-sx x (pairlis$ vs ks) s st defs n)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(binary-append member-equal car-cons cdr-cons) (theory 'minimal-theory))
           :use (g-st-fn-fshape
                 (:instance g-st-dummies-objs (d (list o :in c)) (outs (list nil)))
                 (:instance em-nostobj-g-em-vals (f formals))
                 (:instance rfn-run (vs (g-st-vals formals st)))
                 (:instance f-invoke-sret (vs (g-st-vals formals st)) (body (grf 1)) (locs (grf 3))
                            (rt (kadr (cdr (lkp fn sigs)))) (nm (g-sym fn nil))
                            (rec (if (g-reaches (g-called (strip-cars sigs) (g-fcalls (grf 1))) fn gdefs (1+ (len gdefs))) t nil))
                            (v (mv-nth 1 (a-sx x (pairlis$ (g-st-vals formals st) ks) s st defs n))))))))
