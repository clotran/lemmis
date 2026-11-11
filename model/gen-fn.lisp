; gen-fn: a whole function. When g-fn translates fn, its body calls no
; translated function, and the arguments are int64s, fsem's f-invoke of the
; output on the arguments' literals answers what a-ev answers on the body
; (g-fn-sem). The pieces: f-bind of the :value dummies gives the formals'
; frame (em-ok); undef-locals declares "r" and every temporary (decl-ok,
; dty "r"), none overwriting a formal or another (lf-ok); the body is
; call-free (g-ret-cf), so f-ex-list is fx-list; then gr-sem-thm.

(in-package "ACL2")

(include-book "gen-retout")

; int64-listp: gen-proof

; ---- the arguments: literals, bound to the dummies

(defthm f-ev-g-lit
  (implies (and (int64p k) (integerp f) (< 3 f))
           (equal (f-ev (g-lit k) fr heap procs f) (mv nil k)))
  :hints (("Goal" :expand ((f-ev (g-lit k) fr heap procs f) (f-ev '(:neg (:huge)) fr heap procs (+ -1 f))
                           (f-ev '(:huge) fr heap procs (+ -2 f)) (f-ev '(:int 1) fr heap procs (+ -1 f))))))

(defun fb (vs ks fr)
  (if (atom vs) fr (fb (cdr vs) (cdr ks) (put (g-formal (car vs)) (cons :int64 (car ks)) fr))))

(defun fbi (vs ks fr fuel)
  (if (atom vs) (list ks fr fuel)
    (fbi (cdr vs) (cdr ks) (put (g-formal (car vs)) (cons :int64 (car ks)) fr) (1- fuel))))

(defthm f-bind-g-dummies
  (implies (and (int64-listp ks) (equal (len ks) (len vs)) (integerp fuel) (< (+ 4 (len vs)) fuel))
           (equal (f-bind (g-dummies vs) (g-lits ks) caller callee outs heap procs fuel)
                  (mv nil (fb vs ks callee) outs)))
  :hints (("Goal" :induct (fbi vs ks callee fuel) :in-theory (disable g-lit f-ev put)
           :expand ((f-bind (g-dummies vs) (g-lits ks) caller callee outs heap procs fuel)))))

(defthm lkp-fb-other
  (implies (not (member-equal n (g-formals vs))) (equal (lkp n (fb vs ks fr)) (lkp n fr))))

(defthm em-names-g-em (equal (em-names (g-em vs)) (g-formals vs)))

(defthm var-ok-fb
  (implies (and (no-duplicatesp-equal (g-formals vs)) (int64-listp ks) (equal (len ks) (len vs)))
           (var-ok x (g-em vs) (pairlis$ vs ks) (fb vs ks fr)))
  :hints (("Goal" :induct (fb vs ks fr) :in-theory (enable var-ok))))

(defthm em-ok-fb
  (implies (and (no-duplicatesp-equal (g-formals vs)) (int64-listp ks) (equal (len ks) (len vs)))
           (em-ok (g-em vs) (pairlis$ vs ks) (fb vs ks fr)))
  :hints (("Goal" :expand ((em-ok (g-em vs) (pairlis$ vs ks) (fb vs ks fr))) :in-theory (disable var-ok fb))))

; ---- the declarations: "r", then the temporaries in the order made

(defun lkeys (l) (if (atom l) nil (cons (kar (car l)) (lkeys (cdr l)))))

(defthm undef-locals-append
  (equal (undef-locals (append a b) fr) (undef-locals b (undef-locals a fr))))

(defthm lkeys-append (equal (lkeys (append a b)) (append (lkeys a) (lkeys b))))

(defthm member-lkeys-g-locals
  (iff (member-equal n (lkeys (g-locals locs))) (member-equal n (strip-cars locs))))

(defthm em-ok-undef-locals
  (implies (and (em-ok em env fr) (not (intersectp-equal (lkeys l) (em-names em))))
           (em-ok em env (undef-locals l fr)))
  :hints (("Goal" :in-theory (disable em-ok put))))

(defthm lkp-undef-locals-other
  (implies (not (member-equal n (lkeys l))) (equal (lkp n (undef-locals l fr)) (lkp n fr)))
  :hints (("Goal" :in-theory (disable put))))

(defthm decl-ok-put-other
  (implies (not (member-equal k (strip-cars locs)))
           (equal (decl-ok locs (put k v fr)) (decl-ok locs fr))))

(defthm decl-ok-g-locals
  (implies (and (alistp locs) (no-duplicatesp-equal (strip-cars locs)))
           (decl-ok locs (undef-locals (g-locals locs) fr)))
  :hints (("Goal" :in-theory (disable put))))

(defthm intersectp-subset-l
  (implies (and (subsetp-equal a b) (not (intersectp-equal b c))) (not (intersectp-equal a c))))

(defthm subsetp-lkeys-g-locals (subsetp-equal (lkeys (g-locals locs)) (strip-cars locs))
  :hints (("Goal" :in-theory (disable member-lkeys-g-locals))))

(defmacro fn-fr (rt) `(undef-locals (cons (list "r" ,rt) (g-locals locs)) (fb vs ks nil)))

(defthm lf-ok-nil (lf-ok nil fnames) :hints (("Goal" :in-theory (enable lf-ok))))

(defthm fn-frame-em-ok
  (implies (and (no-duplicatesp-equal (cons "r" (g-formals vs))) (lf-ok locs (g-formals vs))
                (int64-listp ks) (equal (len ks) (len vs)))
           (em-ok (g-em vs) (pairlis$ vs ks) (fn-fr rt)))
  :hints (("Goal" :in-theory (e/d (lf-ok) (em-ok-undef-locals undef-locals em-ok fb))
           :use ((:instance em-ok-undef-locals (em (g-em vs)) (env (pairlis$ vs ks)) (fr (fb vs ks nil))
                            (l (cons (list "r" rt) (g-locals locs))))
                 (:instance intersectp-subset-l (a (lkeys (g-locals locs))) (b (strip-cars locs)) (c (g-formals vs)))))))

(defthm fn-frame-decl
  (implies (lf-ok locs fnames)
           (and (decl-ok locs (fn-fr rt)) (equal (dty "r" (fn-fr rt)) (list rt))))
  :hints (("Goal" :in-theory (e/d (lf-ok) (decl-ok put fb)))))

(in-theory (disable fb))

; ---- the body's run

(defmacro gfr (k) `(mv-nth ,k (g-ret body (g-em vs) 0 nil fn sigs (g-formals vs))))

(defthm fn-run
  (implies (and (not (gfr 0)) (no-duplicatesp-equal (cons "r" (g-formals vs)))
                (consp (lkp fn sigs)) (symbolp fn) (not (equal fn 'quote))
                (no-calls :term body sigs nil) (no-prim-defs defs)
                (int64-listp ks) (equal (len ks) (len vs))
                (not (mv-nth 0 (a-ev body (pairlis$ vs ks) defs n))))
           (let ((fr (undef-locals (cons (list "r" (kadr (cdr (lkp fn sigs)))) (g-locals (gfr 3))) (fb vs ks nil))))
             (and (cf-stmts (gfr 1))
                  (equal (car (fx-list (gfr 1) fr)) :return)
                  (ret-ok (mv-nth 1 (fx-list (gfr 1) fr)) (kadr (cdr (lkp fn sigs)))
                          (mv-nth 1 (a-ev body (pairlis$ vs ks) defs n))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-ret gr-sem-use g-ret-cf fn-frame-em-ok fn-frame-decl undef-locals g-locals
                               fx-list a-ev no-calls em-ok decl-ok dty ret-ok lf-ok)
           :use (a-orc-nil (:instance member-equal-nil (a fn)) (:instance g-ret-cf (x body) (em (g-em vs)) (cnt 0) (locs nil) (self fn) (fnames (g-formals vs)))
                 (:instance fn-frame-em-ok (locs (gfr 3)) (rt (kadr (cdr (lkp fn sigs)))))
                 (:instance fn-frame-decl (locs (gfr 3)) (rt (kadr (cdr (lkp fn sigs)))) (fnames (g-formals vs)))
                 (:instance gr-sem-thm (flag :ret) (x body) (em (g-em vs)) (cnt 0) (locs nil) (self fn) (cs nil)
                            (fnames (g-formals vs)) (env (pairlis$ vs ks))
                            (fr (undef-locals (cons (list "r" (kadr (cdr (lkp fn sigs)))) (g-locals (gfr 3))) (fb vs ks nil))))
                 (:instance gr-sem-use (x body) (em (g-em vs)) (cnt 0) (locs nil) (self fn) (cs nil)
                            (fnames (g-formals vs)) (env (pairlis$ vs ks)) (rt (kadr (cdr (lkp fn sigs))))
                            (fr (undef-locals (cons (list "r" (kadr (cdr (lkp fn sigs)))) (g-locals (gfr 3))) (fb vs ks nil))))))))

; ---- the function: f-bind, the declarations, the body (a DO around it if
; g-has found a CYCLE, which call-free code has none of)

(defthm f-ex-list-do
  (implies (and (cf-stmts s) (integerp k) (< (+ 3 (acl2-count s)) k) (equal (car (fx-list s fr)) :return))
           (equal (f-ex-list (list (list :do s)) fr heap procs k) (list :return (mv-nth 1 (fx-list s fr)) heap)))
  :hints (("Goal" :in-theory (disable fx-list f-ex-list-open)
           :expand ((f-ex-list (list (list :do s)) fr heap procs k) (f-ex (list :do s) fr heap procs (+ -1 k))))))

(defthm f-ex-list-cf-return
  (implies (and (cf-stmts s) (integerp k) (< (acl2-count s) k) (equal (car (fx-list s fr)) :return))
           (equal (f-ex-list s fr heap procs k) (list :return (mv-nth 1 (fx-list s fr)) heap)))
  :hints (("Goal" :in-theory (disable fx-list))))

(defmacro fd () '(lkp fn defs))

(defthm g-fn-sem
  (implies (and (not (mv-nth 0 (g-fn fn defs sigs)))
                (consp (lkp fn sigs)) (symbolp fn) (not (equal fn 'quote))
                (no-calls :term (kaddr (fd)) sigs nil) (no-prim-defs defs)
                (int64-listp args) (equal (len args) (len (kadr (fd))))
                (not (mv-nth 0 (a-ev (kaddr (fd)) (pairlis$ (kadr (fd)) args) defs n)))
                (integerp fuel) (< (+ 6 (len args) (acl2-count (mv-nth 1 (g-fn fn defs sigs)))) fuel))
           (equal (f-invoke (mv-nth 1 (g-fn fn defs sigs)) (g-lits args) caller heap procs fuel)
                  (mv nil (mv-nth 1 (a-ev (kaddr (fd)) (pairlis$ (kadr (fd)) args) defs n)) heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (ret-ok) (g-ret g-reaches g-called g-fcalls g-has g-sym g-dummies g-lits g-locals g-em g-formals
                                     fn-run fx-list a-ev no-calls undef-locals f-bind f-ex-list fb))
           :expand ((f-invoke (mv-nth 1 (g-fn fn defs sigs)) (g-lits args) caller heap procs fuel))
           :use ((:instance fn-run (vs (kadr (fd))) (ks args) (body (kaddr (fd))))))))
