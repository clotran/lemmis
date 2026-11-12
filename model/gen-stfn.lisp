; gen-stfn: a whole subroutine (GEN.md "What remains" 4 (a), step (4)).
; When g-st-fn translates a function of one stobj answering that stobj,
; its body st-plain and call-free, f-invoke of the subroutine on the
; stobj's object and int64 literals leaves the object as a-st leaves S,
; the caller's frame unchanged (g-st-fn-sem).
;
; The pieces: g-st-fn's tail position (tself = the function, dests the
; results' r) does not matter on st-plain statements (tsx-plain); f-bind
; of the object dummy, then the value dummies (gen-fn's fb); the
; temporaries declared over them (lf-ok); gst-sem-holds at that frame; the
; sx-list run is f-ex-list's (sx-list-is-f-ex-list).

(in-package "ACL2")

(include-book "gen-stopen")
(include-book "gen-fresh")

; ---- from gen-fn (whose gen-ret macros clash with gen-stlst's)
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

(in-theory (disable fb))

(defthm tsx-use
  (implies (and (tsx x sigs fnames st) (tself-ok tself st) (syntaxp (not (and (equal dests ''nil) (equal tself ''nil)))))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests tself)
                  (g-stmt x em cnt locs sigs fnames st outs nil nil)))
  :hints (("Goal" :in-theory (disable g-stmt) :use tsx-necc)))

(defthm tself-ok-nil (tself-ok nil st) :hints (("Goal" :in-theory (enable tself-ok))))

(defmacro tsx-min (&rest rs) `(union-theories '(tsx-use tself-ok-nil ,@rs) (theory 'minimal-theory)))

(defthm tsx-sym
  (implies (symbolp x) (tsx x sigs fnames st))
  :hints (("Goal" :in-theory (tsx-min g-stmt-sym-t) :expand ((tsx x sigs fnames st)))))

(defthm tsx-set
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :set) (tsx (caddr x) sigs fnames st))
           (tsx x sigs fnames st))
  :hints (("Goal" :in-theory (tsx-min g-stmt-set-t g-stmt-set) :expand ((tsx x sigs fnames st)))))

(defthm tsx-seti
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :seti) (tsx (cadddr x) sigs fnames st))
           (tsx x sigs fnames st))
  :hints (("Goal" :in-theory (tsx-min g-stmt-seti-t g-stmt-seti) :expand ((tsx x sigs fnames st)))))

(defthm tsx-if
  (implies (and (consp x) (true-listp x) (eq (car x) 'if) (not (g-role 'if st))
                (tsx (caddr x) sigs fnames st) (tsx (cadddr x) sigs fnames st))
           (tsx x sigs fnames st))
  :hints (("Goal" :in-theory (tsx-min g-stmt-if-t g-stmt-if) :expand ((tsx x sigs fnames st)))))

(defthm tsx-lam
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (cadr (car x))))
                (tsx (caddr (car x)) sigs fnames st))
           (tsx x sigs fnames st))
  :hints (("Goal" :in-theory (tsx-min g-stmt-lam-t g-stmt-lam) :expand ((tsx x sigs fnames st)))))

(defun tsi (x)
  (if (atom x) nil (list (tsi (caddr x)) (tsi (cadddr x)) (tsi (caddr (car x))))))

(defthm tsx-plain
  (implies (and (st-plain :term x nil st) (not (g-role 'if st))) (tsx x sigs fnames st))
  :hints (("Goal" :induct (tsi x) :expand ((st-plain :term x nil st))
           :in-theory (union-theories '((:induction tsi) st-plain g-role-quote tsx-sym tsx-set tsx-seti tsx-if tsx-lam)
                                      (theory 'minimal-theory)))))

(defthm g-stmt-tself
  (implies (and (st-plain :term x nil st) (not (g-role 'if st)) (tself-ok tself st)
                (syntaxp (not (and (equal dests ''nil) (equal tself ''nil)))))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests tself)
                  (g-stmt x em cnt locs sigs fnames st outs nil nil)))
  :hints (("Goal" :in-theory (disable g-stmt st-plain tsx-use tsx-plain) :use (tsx-plain tsx-use))))

; ---- the frame: the object dummy, then the value dummies (fb), then the
; temporaries undefined

(defthm f-bind-obj
  (implies (and (posp fuel) (equal (cdr (lkp ob caller)) (list* :obj :inout key)))
           (equal (f-bind (cons (list o :inout c) ds) (cons (list :var ob) as) caller callee outs heap procs fuel)
                  (f-bind ds as caller (put o (list* :obj :inout key) callee) outs heap procs (1- fuel))))
  :hints (("Goal" :expand ((f-bind (cons (list o :inout c) ds) (cons (list :var ob) as) caller callee outs heap procs fuel)))))

(defthm em-nostobj-g-em-vals (em-nostobj (g-em (g-st-vals f st)) st)
  :hints (("Goal" :in-theory (disable g-role))))

(defthm subsetp-append-r (subsetp-equal a (append b a)))

(defthm lf-ok-append-parts
  (implies (lf-ok locs (append a b))
           (and (lf-ok locs a) (not (intersectp-equal (strip-cars locs) a)) (not (intersectp-equal (strip-cars locs) b))
                (alistp locs) (no-duplicatesp-equal (strip-cars locs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable lf-ok))))

(defthm not-member-intersect-cars
  (implies (and (member-equal o b) (not (intersectp-equal l b))) (not (member-equal o l))))

(defthm lkp-fb-put-obj
  (implies (not (member-equal o (g-formals vs)))
           (equal (lkp o (fb vs ks (put o v nil))) (cons o v)))
  :hints (("Goal" :in-theory (disable lkp-fb-other) :use ((:instance lkp-fb-other (n o) (fr (put o v nil)))))))

; the callee's frame
(defmacro sfr () '(undef-locals (g-locals locs) (fb vs ks (put o (list* :obj :inout key) nil))))

(defthm sfr-em-ok
  (implies (and (no-duplicatesp-equal (g-formals vs)) (lf-ok locs (append (g-formals vs) objs))
                (int64-listp ks) (equal (len ks) (len vs)))
           (em-ok (g-em vs) (pairlis$ vs ks) (sfr)))
  :hints (("Goal" :in-theory (disable em-ok-undef-locals undef-locals em-ok fb lf-ok intersectp-subset-l)
           :use ((:instance em-ok-undef-locals (em (g-em vs)) (env (pairlis$ vs ks))
                            (fr (fb vs ks (put o (list* :obj :inout key) nil))) (l (g-locals locs)))
                 (:instance intersectp-subset-l (a (lkeys (g-locals locs))) (b (strip-cars locs)) (c (g-formals vs)))
                 (:instance lf-ok-append-parts (a (g-formals vs)) (b objs))))))

(defthm sfr-decl
  (implies (lf-ok locs fnames) (decl-ok locs (sfr)))
  :hints (("Goal" :in-theory (e/d (lf-ok) (decl-ok put fb undef-locals)))))

(defthm sfr-obj-at
  (implies (and (lf-ok locs (append (g-formals vs) objs)) (member-equal o objs)
                (not (member-equal o (g-formals vs))) (equal (lkp key heap) (cons key s)))
           (and (obj-at o s (sfr) heap) (equal (okey o (sfr)) key)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (obj-at okey) (not-member-intersect-cars lf-ok undef-locals fb lkp-undef-locals-other member-lkeys-g-locals))
           :use ((:instance lkp-undef-locals-other (n o) (l (g-locals locs)) (fr (fb vs ks (put o (list* :obj :inout key) nil))))
                 (:instance member-lkeys-g-locals (n o))
                 (:instance not-member-intersect-cars (b objs) (l (strip-cars locs)))
                 (:instance lf-ok-append-parts (a (g-formals vs)) (b objs))))))

; ---- the body's run at that frame (gst-sem-holds)

(defmacro sfn () '(append (g-formals vs) (st-objs st)))
(defmacro gsf (k) `(mv-nth ,k (g-stmt x (g-em vs) 0 nil sigs (sfn) st outs nil nil)))

(defmacro stfn-hyps ()
  '(and (st-plain :term x nil st) (no-calls :term x sigs nil)
        (not (g-role 'if st)) (not (g-role 'implies st)) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
        (lf-ok (gsf 3) (sfn)) (not (member-equal o (g-formals vs)))
        (int64-listp ks) (equal (len ks) (len vs)) (equal (lkp key heap) (cons key s))
        (st-ok st o s) (st-wf st s) (not (car (a-st x (pairlis$ vs ks) s st defs n)))))

(defthm stfn-run
  (implies (and (stfn-hyps) (not (gsf 0)) (no-duplicatesp-equal (g-formals vs)) (em-nostobj (g-em vs) st)
                (member-equal o (st-objs st)))
           (let ((fr (undef-locals (g-locals (gsf 3)) (fb vs ks (put o (list* :obj :inout key) nil)))))
             (and (equal (car (sx-list (gsf 1) fr heap)) :normal)
                  (equal (mv-nth 2 (sx-list (gsf 1) fr heap)) (put key (mv-nth 1 (a-st x (pairlis$ vs ks) s st defs n)) heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance gst-sem-holds (em (g-em vs)) (cnt 0) (locs nil) (fnames (sfn)) (env (pairlis$ vs ks))
                            (fr (undef-locals (g-locals (gsf 3)) (fb vs ks (put o (list* :obj :inout key) nil)))))
                 (:instance gst-sem-use (em (g-em vs)) (cnt 0) (locs nil) (fnames (sfn)) (env (pairlis$ vs ks))
                            (fr (undef-locals (g-locals (gsf 3)) (fb vs ks (put o (list* :obj :inout key) nil)))))
                 (:instance sfr-em-ok (locs (gsf 3)) (objs (st-objs st)))
                 (:instance sfr-decl (locs (gsf 3)) (fnames (sfn)))
                 (:instance sfr-obj-at (locs (gsf 3)) (objs (st-objs st)))
                 (:instance subsetp-append-r (a (st-objs st)) (b (g-formals vs)))))))

; ---- the subroutine

(defthm g-st-vals-not-stobj
  (implies (eq (g-role v st) :stobj) (not (member-equal v (g-st-vals f st))))
  :hints (("Goal" :in-theory (disable g-role))))

; r = (fn formals (sv) t x): one stobj, its object o, the one result
(defthm g-st-fn-shape
  (implies (and sv (eq (g-role sv st) :stobj) (not (mv-nth 0 (g-st-fn (list fn formals (list sv) t x) gdefs sigs st))))
           (equal (mv-nth 1 (g-st-fn (list fn formals (list sv) t x) gdefs sigs st))
                  (let ((vs (g-st-vals formals st)))
                    (mv-let (e stmts cnt locs) (g-stmt x (g-em vs) 0 nil sigs (sfn) st (list sv) nil fn)
                      (declare (ignore e cnt))
                      (list :subroutine (g-sym fn nil)
                            (if (g-reaches (g-called (strip-cars gdefs) (append (g-fcalls stmts) (g-ccalls stmts)))
                                           fn gdefs (1+ (len gdefs)))
                                t nil)
                            (append (g-st-dummies formals (list sv) st) (g-dummies vs))
                            (g-locals locs)
                            (if (g-has '(:cycle) stmts) (list (list :do (append stmts '((:exit))))) stmts))))))
  :hints (("Goal" :in-theory (e/d (kar kadr kaddr kadddr) (g-stmt g-sret g-reaches g-called g-fcalls g-ccalls g-has g-st-dummies
                                                           g-dummies g-locals g-em g-formals g-st-vals g-role g-st-outs-ok)))))

(defthm g-st-fn-err
  (implies (and sv (eq (g-role sv st) :stobj) (not (mv-nth 0 (g-st-fn (list fn formals (list sv) t x) gdefs sigs st))))
           (and (not (mv-nth 0 (g-stmt x (g-em (g-st-vals formals st)) 0 nil sigs
                                       (append (g-formals (g-st-vals formals st)) (st-objs st)) st (list sv) nil fn)))
                (no-duplicatesp-equal (g-formals (g-st-vals formals st)))))
  :hints (("Goal" :in-theory (e/d (kar kadr kaddr kadddr) (g-stmt g-sret g-reaches g-called g-fcalls g-ccalls g-has g-st-dummies
                                                           g-dummies g-locals g-em g-formals g-st-vals g-role g-st-outs-ok)))))

(defmacro gfn () '(g-st-fn (list fn formals (list sv) t x) gdefs sigs st))

(defthm g-st-fn-sem
  (let ((vs (g-st-vals formals st)) (outs (list sv)))
    (implies (and (not (mv-nth 0 (gfn))) sv (eq (g-role sv st) :stobj) (tself-ok fn st)
                  (equal (g-st-dummies formals outs st) (list (list o :inout c)))
                  (stfn-hyps) (cs-stmts (gsf 1)) (not (g-has '(:cycle) (gsf 1)))
                  (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                  (integerp fuel) (< (+ 6 (len ks) (acl2-count (gsf 1))) fuel))
             (equal (f-invoke (mv-nth 1 (gfn)) (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                    (mv nil caller (put key (mv-nth 1 (a-st x (pairlis$ vs ks) s st defs n)) heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-st-fn g-stmt g-reaches g-called g-fcalls g-ccalls g-has g-st-dummies g-dummies g-locals g-em
                               g-formals g-st-vals g-role g-lits f-bind f-ex-list sx-list a-st undef-locals fb stfn-run
                               st-plain no-calls lf-ok st-ok st-wf g-st-fn-err)
           :expand ((:free (p) (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel)))
           :use (g-st-fn-err (:instance stfn-run (vs (g-st-vals formals st)) (outs (list sv)))
                 (:instance st-ok-necc (x sv))
                 (:instance g-obj-st-objs (x sv))))))
