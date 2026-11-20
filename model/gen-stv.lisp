; gen-stv: g-stmt with outs and dests against a source meaning answering
; values (GEN.md 4 (4a) (2b), the restatement). `a-stv x outs ...` =>
; (mv err S' vs): a tuple by a-tuple, a :sub call by a-stcall / a-stcall-u
; (vs its value results, g-rvals, int64s), if and a lambda (no mv) by
; recursion, every other case a-st's with vs nil. `gstv-sem` is gst-sem on
; sxc-list with dests: the statements answer :normal, the heap the object put
; to S', S' keeps st-ok/st-wf, and each dest holds its value (svs-is).
; This book: the definitions and the leaf, cons and :sub cases.

(in-package "ACL2")

(include-book "gen-stcons")
(include-book "gen-stcallud")

(set-verify-guards-eagerness 0)

; g-callst-dests rewrites its own instance at dests nil (loops): :use it only
(in-theory (disable g-callst-dests))

(defun nvals (outs) (if (atom outs) 0 (+ (if (car outs) 0 1) (nvals (cdr outs)))))

(defthm len-g-rvals (equal (len (g-rvals outs rs)) (nvals outs))
  :hints (("Goal" :induct (g-rvals outs rs) :in-theory (enable g-rvals))))

; ---- the source

(defun a-stv (x outs env s st defs n)
  (declare (xargs :measure (nfix n)))
  (cond ((and (consp x) (eq (car x) 'cons))
         (if (zp n) (mv :fuel s nil) (a-tuple outs (g-conses x) env s st defs (1- n))))
        ((or (atom x) (eq (g-role (car x) st) :set) (eq (g-role (car x) st) :seti))
         (mv-let (e s2) (a-st x env s st defs n) (mv e s2 nil)))
        ((zp n) (mv :fuel s nil))
        ((eq (car x) 'if)
         (mv-let (e c) (a-sx (kadr x) env s st defs (1- n))
           (cond (e (mv e s nil))
                 (c (a-stv (kaddr x) outs env s st defs (1- n)))
                 (t (a-stv (kadddr x) outs env s st defs (1- n))))))
        ((consp (car x))
         (if (member-equal 'mv (kadr (car x))) (mv :mv s nil)
           (mv-let (e vs s1) (a-st-args (kadr (car x)) (cdr x) env s s st defs (1- n))
             (if e (mv e s nil)
               (a-stv (kaddr (car x)) outs (pairlis$ (true-list-fix (kadr (car x))) vs) s1 st defs (1- n))))))
        ((eq (g-role (car x) st) :sub)
         (mv-let (e s2 rs) (if (g-upd (g-obj (car x) st) (cdr x) st) (a-stcall-u x env s st defs (1- n))
                             (a-stcall x env s st defs (1- n)))
           (cond (e (mv e s nil))
                 ((not (int64s (g-rvals outs rs))) (mv :type s nil))
                 (t (mv nil s2 (g-rvals outs rs))))))
        (t (mv :stobj s nil))))

(in-theory (disable a-stv))

(defthm a-stv-leaf
  (implies (and (not (and (consp x) (eq (car x) 'cons)))
                (or (atom x) (eq (g-role (car x) st) :set) (eq (g-role (car x) st) :seti)))
           (equal (a-stv x outs env s st defs n)
                  (list (car (a-st x env s st defs n)) (mv-nth 1 (a-st x env s st defs n)) nil)))
  :hints (("Goal" :expand ((a-stv x outs env s st defs n)) :in-theory (disable a-st a-tuple g-role))))

(defthm a-stv-cons
  (implies (and (consp x) (eq (car x) 'cons))
           (equal (a-stv x outs env s st defs n)
                  (if (zp n) (list :fuel s nil) (a-tuple outs (g-conses x) env s st defs (1- n)))))
  :hints (("Goal" :expand ((a-stv x outs env s st defs n)) :in-theory (disable a-st a-tuple g-role))))

(defthm a-stv-if
  (implies (and (consp x) (eq (car x) 'if) (not (g-role 'if st)))
           (equal (a-stv x outs env s st defs n)
                  (if (zp n) (list :fuel s nil)
                    (mv-let (e c) (a-sx (cadr x) env s st defs (1- n))
                      (cond (e (list e s nil))
                            (c (a-stv (caddr x) outs env s st defs (1- n)))
                            (t (a-stv (cadddr x) outs env s st defs (1- n))))))))
  :hints (("Goal" :expand ((a-stv x outs env s st defs n)) :in-theory (e/d (kadr kaddr kadddr kar) (a-st a-tuple g-role a-sx)))))

(defthm a-stv-lam
  (implies (and (consp x) (consp (car x)) (not (member-equal 'mv (cadr (car x)))))
           (equal (a-stv x outs env s st defs n)
                  (if (zp n) (list :fuel s nil)
                    (mv-let (e vs s1) (a-st-args (cadr (car x)) (cdr x) env s s st defs (1- n))
                      (if e (list e s nil)
                        (a-stv (caddr (car x)) outs (pairlis$ (true-list-fix (cadr (car x))) vs) s1 st defs (1- n)))))))
  :hints (("Goal" :expand ((a-stv x outs env s st defs n)) :in-theory (e/d (kadr kaddr kar) (a-st a-tuple g-role a-st-args)))))

(defthm a-stv-sub
  (implies (and (consp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :sub) (not (g-role 'if st)))
           (equal (a-stv x outs env s st defs n)
                  (if (zp n) (list :fuel s nil)
                    (mv-let (e s2 rs) (if (g-upd (g-obj (car x) st) (cdr x) st) (a-stcall-u x env s st defs (1- n))
                                        (a-stcall x env s st defs (1- n)))
                      (cond (e (list e s nil))
                            ((not (int64s (g-rvals outs rs))) (list :type s nil))
                            (t (list nil s2 (g-rvals outs rs))))))))
  :hints (("Goal" :expand ((a-stv x outs env s st defs n))
           :in-theory (disable a-st a-tuple a-stcall a-stcall-u g-upd g-obj int64s g-rvals))
          ("Goal'" :in-theory (e/d (g-role) (a-st a-tuple a-stcall a-stcall-u g-upd g-obj int64s g-rvals)))))

; ---- g-stmt's openers with dests

(defthm g-stmt-if-d
  (implies (and (consp x) (true-listp x) (eq (car x) 'if) (not (g-role 'if st)))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests nil)
                  (if (or (not (= (len x) 4)) (<= 3 (g-chain x nil nil))) (mv :stobj nil cnt locs)
                    (mv-let (e sc cc tc cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                      (if (or e (not (eq tc :logical))) (mv (or e :type) nil cnt locs)
                        (mv-let (e sa cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs dests nil)
                          (if e (mv e nil cnt locs)
                            (mv-let (e sb cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs dests nil)
                              (if e (mv e nil cnt locs)
                                (mv nil (append sc (list (list :if cc sa sb))) cnt locs))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs dests nil)))))

(defthm g-stmt-lam-d
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (cadr (car x)))))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests nil)
                  (let ((vars (cadr (car x))) (body (caddr (car x))))
                    (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                                  (no-duplicatesp-eq vars) (= (len vars) (len (cdr x)))))
                        (mv :stobj nil cnt locs)
                      (mv-let (e s binds cnt locs) (g-svals vars (cdr x) em cnt locs sigs fnames st)
                        (if e (mv e nil cnt locs)
                          (if (not (g-acts-place vars (cdr x) em st)) (mv :mv nil cnt locs)
                            (mv-let (e sa cnt locs) (g-sacts vars (cdr x) em cnt locs sigs fnames st)
                              (if e (mv e nil cnt locs)
                                (mv-let (e sb cnt locs) (g-stmt body (append binds em) cnt locs sigs fnames st outs dests nil)
                                  (if e (mv e nil cnt locs)
                                    (mv nil (append s sa sb) cnt locs))))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) '(kadr kaddr kar)) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs dests nil)))))

(defthm g-stmt-sub-d
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :sub) (not (g-role 'if st)))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests nil)
                  (if (not (equal (g-comp (car x) st) outs)) (mv :stobj nil cnt locs)
                    (g-callst x em cnt locs sigs fnames st dests))))
  :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (cons 'g-callst (gst-dis)))
           :expand ((g-stmt x em cnt locs sigs fnames st outs dests nil)))
          ("Goal'" :in-theory (union-theories '(g-role) (set-difference-theories (current-theory :here) (cons 'g-callst (gst-dis)))))))

; ---- the dests after put-dests

(defthm lkp-put-dests-other
  (implies (not (member-equal k (dnames ds))) (equal (lkp k (put-dests ds vs fr)) (lkp k fr)))
  :hints (("Goal" :induct (put-dests ds vs fr) :in-theory (disable put))))

(defthm dests-ok-put-int
  (implies (dests-ok ds fr) (dests-ok ds (put k (cons :int64 v) fr)))
  :hints (("Goal" :in-theory (disable put))))

(defthm svs-is-put-dests
  (implies (and (dests-ok ds fr) (no-duplicatesp-equal (dnames ds)) (equal (len vs) (len ds)) (int64s vs))
           (svs-is ds vs (put-dests ds vs fr) h))
  :hints (("Goal" :induct (put-dests ds vs fr) :in-theory (disable put))
          ("Subgoal *1/2" :expand ((sv (car ds) (put-dests (cdr ds) (cdr vs) (put (cadr (car ds)) (cons :int64 (car vs)) fr)) h)))))

; ---- the fact: gstv-sem

(defmacro gstv-hyps ()
  '(and (em-ok em env fr) (decl-ok locs2 fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
        (c-sorc o st) (c-sorc-d o st) (a-call-ok st o)
        (true-listp dests) (dests-ok dests fr) (equal (len dests) (nvals outs)) (no-duplicatesp-equal (dnames dests))
        (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars locs2))))))

(defun gstv-sem (x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
  (mv-let (e ss cnt2 locs2) (g-stmt x em cnt locs sigs fnames st outs dests nil)
    (declare (ignore cnt2))
    (mv-let (ae s2 vs) (a-stv x outs env s st defs n)
      (implies (and (not e) (not ae) (gstv-hyps))
               (mv-let (stt fr2 h2) (sxc-list ss fr heap)
                 (and (equal stt :normal) (equal h2 (put (okey o fr) s2 heap)) (st-ok st o s2) (st-wf st s2)
                      (svs-is dests vs fr2 h2)))))))

; the locals grow (static)
(defun stv-grow (x em cnt locs sigs fnames st outs dests)
  (mv-let (e ss cnt2 locs2) (g-stmt x em cnt locs sigs fnames st outs dests nil)
    (declare (ignore ss cnt2))
    (implies (and (not e) (true-listp dests) (equal (len dests) (nvals outs))) (subsetp-equal locs locs2))))

(defmacro gvx (k) `(mv-nth ,k (g-stmt x em cnt locs sigs fnames st outs dests nil)))
(defmacro avx (k) `(mv-nth ,k (a-stv x outs env s st defs n)))

(defthm gstv-sem-use
  (implies (and (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
                (not (gvx 0)) (not (avx 0))
                (em-ok em env fr) (decl-ok (gvx 3) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
                (c-sorc o st) (c-sorc-d o st) (a-call-ok st o)
                (true-listp dests) (dests-ok dests fr) (equal (len dests) (nvals outs)) (no-duplicatesp-equal (dnames dests))
                (not (intersectp-equal (dnames dests) (append fnames (em-names em) (strip-cars (gvx 3))))))
           (and (equal (car (sxc-list (gvx 1) fr heap)) :normal)
                (equal (mv-nth 2 (sxc-list (gvx 1) fr heap)) (put (okey o fr) (avx 1) heap))
                (st-ok st o (avx 1)) (st-wf st (avx 1))
                (svs-is dests (avx 2) (mv-nth 1 (sxc-list (gvx 1) fr heap)) (mv-nth 2 (sxc-list (gvx 1) fr heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (gstv-sem) (g-stmt a-stv sxc-list em-ok decl-ok st-ok st-wf obj-at c-sorc c-sorc-d a-call-ok
                                       dests-ok svs-is)))))

(defthm stv-grow-use
  (implies (and (stv-grow x em cnt locs sigs fnames st outs dests) (not (gvx 0))
                (true-listp dests) (equal (len dests) (nvals outs))) (subsetp-equal locs (gvx 3)))
  :hints (("Goal" :in-theory (disable g-stmt))))

(in-theory (disable gstv-sem stv-grow))

