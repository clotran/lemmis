; gen-stcase: g-stmt's element update, if and lambda against a-st on sx-list
; (GEN.md "What remains" 4 (a), step (2')), each as gen-stst's gst-set-*:
; the case's gst-sem from its parts' gst-sem/gs-sem and names facts.

(in-package "ACL2")

(include-book "gen-stst")

(defthm mv-nth-0-car (equal (mv-nth 0 x) (car x)))
(defthm mv-nth-cons-k
  (implies (and (syntaxp (quotep k)) (posp k)) (equal (mv-nth k (cons a b)) (mv-nth (1- k) b))))
(in-theory (disable mv-nth-0-car mv-nth-cons-k))

; ---- the element update (update-fi i v s): i, v into temporaries i_N, v_N+1,
; then s's statements, then hs%a(i_N) = v_N+1

(defthm g-stmt-seti
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :seti))
           (equal (g-stmt x em cnt locs sigs fnames st outs nil nil)
                  (if (not (and (= (len x) 4) (equal outs (list (cadddr x))) (equal (g-obj (car x) st) (g-obj (cadddr x) st))))
                      (mv :stobj nil cnt locs)
                    (mv-let (e si ci ti cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                      (if (or e (not (eq ti :int64))) (mv (or e :type) nil cnt locs)
                        (mv-let (e sv cv tv cnt locs) (g-sexpr (caddr x) em cnt locs sigs fnames st)
                          (if (or e (not (eq tv :int64))) (mv (or e :type) nil cnt locs)
                            (mv-let (e tmi cnt locs) (g-fresh 'i :int64 cnt locs (append fnames (em-names em)))
                              (if e (mv e nil cnt locs)
                                (mv-let (e tmv cnt locs) (g-fresh 'v :int64 cnt locs (append fnames (em-names em)))
                                  (if e (mv e nil cnt locs)
                                    (mv-let (e ss cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs nil nil)
                                      (if e (mv e nil cnt locs)
                                        (mv nil (append si (list (list :assign (list :var tmi) ci)) sv
                                                        (list (list :assign (list :var tmv) cv)) ss
                                                        (list (list :assign (list :elem (g-obj (car x) st) (g-comp (car x) st)
                                                                                    (list :var tmi))
                                                                    (list :var tmv))))
                                            cnt locs))))))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs nil nil)))))

(defthm a-st-seti
  (implies (and (consp x) (eq (g-role (car x) st) :seti))
           (equal (a-st x env s st defs n)
                  (if (zp n) (mv :fuel s)
                    (mv-let (e i) (a-sx (cadr x) env s st defs (1- n))
                      (if e (mv e s)
                        (mv-let (e v) (a-sx (caddr x) env s st defs (1- n))
                          (if e (mv e s)
                            (mv-let (e s1) (a-st (cadddr x) env s st defs (1- n))
                              (let ((p (cdr (lkp (g-comp (car x) st) s1))))
                                (cond (e (mv e s))
                                      ((not (and (farrayp p) (integerp i))) (mv :type s))
                                      ((not (and (<= 0 i) (< i (len (cdr p))))) (mv :bounds s))
                                      (t (mv nil (put (g-comp (car x) st) (cons :array (update-nth i v (cdr p))) s1)))))))))))))
  :hints (("Goal" :in-theory (e/d (kadr kaddr kadddr kar) (g-role g-comp a-sx farrayp)) :expand ((a-st x env s st defs n)))))

(defthm sx-assign-elem
  (implies (and (not (car (sv cv fr heap))) (int64p (mv-nth 1 (sv cv fr heap))) (obj-at o (hs-of) fr heap)
                (farrayp (cdr (lkp comp (hs-of)))) (not (car (sv ci fr heap))) (integerp (mv-nth 1 (sv ci fr heap))))
           (equal (sx (list :assign (list :elem o comp ci) cv) fr heap)
                  (let ((i (mv-nth 1 (sv ci fr heap))) (a (cddr (lkp comp (hs-of)))))
                    (if (and (<= 0 i) (< i (len a)))
                        (mv :normal fr (put (okey o fr) (put comp (cons :array (update-nth i (mv-nth 1 (sv cv fr heap)) a)) (hs-of))
                                            heap))
                      (mv (errst :bounds) fr heap)))))
  :hints (("Goal" :in-theory (e/d (obj-at okey) (sv)) :expand ((sx (list :assign (list :elem o comp ci) cv) fr heap)))))

(defmacro e1 (k) `(mv-nth ,k (g-sexpr (cadr x) em cnt locs sigs fnames st)))
(defmacro e2 (k) `(mv-nth ,k (g-sexpr (caddr x) em (e1 4) (e1 5) sigs fnames st)))
(defmacro tmi () '(g-tmp 'i (1+ (nfix (e2 4)))))
(defmacro c3 () '(1+ (nfix (1+ (nfix (e2 4))))))
(defmacro tmv () '(g-tmp 'v (c3)))
(defmacro loci () '(cons (cons (tmi) :int64) (true-list-fix (e2 5))))
(defmacro locw () '(cons (cons (tmv) :int64) (true-list-fix (loci))))
(defmacro e3 (k) `(mv-nth ,k (g-stmt (cadddr x) em (c3) (locw) sigs fnames st outs nil nil)))
(defmacro sfa () '(mv-nth 1 (sx-list (e1 1) fr heap)))
(defmacro sfb () '(put (tmi) (cons :int64 (mv-nth 1 (a-sx (cadr x) env s st defs (1- n)))) (sfa)))
(defmacro sfc () '(mv-nth 1 (sx-list (e2 1) (sfb) heap)))
(defmacro sfd () '(put (tmv) (cons :int64 (mv-nth 1 (a-sx (caddr x) env s st defs (1- n)))) (sfc)))

(defthm nfix-1+-nfix (equal (nfix (+ 1 (nfix c))) (+ 1 (nfix c))))


;; a temporary the statements do not assign reads the same after them
(defthm sv-var-after
  (implies (not (member-equal k (asgv :list ss)))
           (equal (sv (list :var k) (mv-nth 1 (sx-list ss fr heap)) h2) (sv (list :var k) fr heap)))
  :hints (("Goal" :in-theory (disable stable-sv-after) :use (:instance stable-sv-after (c (list :var k))))))

(defthm sv-var-put-other
  (implies (not (equal k j)) (equal (sv (list :var k) (put j v fr) heap) (sv (list :var k) fr heap)))
  :hints (("Goal" :expand ((sv (list :var k) (put j v fr) heap) (sv (list :var k) fr heap)))))

;; the glue's steps, each used by instance
(defthm seti-sv-v
  (implies (and (int64p vv) (not (member-equal kv (asgv :list ss))))
           (equal (sv (list :var kv) (mv-nth 1 (sx-list ss (put kv (cons :int64 vv) fc) heap)) h2) (mv nil vv)))
  :rule-classes nil :hints (("Goal" :in-theory (disable sv sx-list dty))))

(defthm seti-okey
  (implies (and (obj-at o s fd heap) (equal (okey o fd) (okey o fr)))
           (equal (okey o (mv-nth 1 (sx-list ss fd heap))) (okey o fr)))
  :rule-classes nil :hints (("Goal" :in-theory (disable sv sx-list dty okey obj-at))))

(defthm seti-sv-i
  (implies (and (int64p iv) (not (equal ki kv)) (not (member-equal ki (asgv :list sv)))
                (not (member-equal ki (asgv :list ss))))
           (equal (sv (list :var ki) (mv-nth 1 (sx-list ss (put kv (cons :int64 vv) (mv-nth 1 (sx-list sv (put ki (cons :int64 iv) fa) heap))) heap)) h2)
                  (mv nil iv)))
  :rule-classes nil :hints (("Goal" :in-theory (disable sv sx-list dty))))

(defthm seti-last
  (implies (and (obj-at o s1 fe (put k s1 heap)) (equal (okey o fe) k) (farrayp (cdr (lkp c s1)))
                (equal (sv (list :var ki) fe (put k s1 heap)) (mv nil iv))
                (equal (sv (list :var kv) fe (put k s1 heap)) (mv nil vv)) (int64p iv) (int64p vv))
           (equal (sx (list :assign (list :elem o c (list :var ki)) (list :var kv)) fe (put k s1 heap))
                  (if (and (<= 0 iv) (< iv (len (cddr (lkp c s1)))))
                      (mv :normal fe (put k (put c (cons :array (update-nth iv vv (cddr (lkp c s1)))) s1) heap))
                    (mv (errst :bounds) fe (put k s1 heap)))))
  :rule-classes nil :hints (("Goal" :in-theory (disable sv sx-list dty okey obj-at sx farrayp errst))))

(defmacro fa () '(mv-nth 1 (sx-list si fr heap)))
(defmacro fc () '(mv-nth 1 (sx-list sv (put ki (cons :int64 iv) (fa)) heap)))
(defmacro fd () '(put kv (cons :int64 vv) (fc)))

;; the element update's statements on abstract parts
(defthm seti-glue
  (let* ((fa (mv-nth 1 (sx-list si fr heap)))
         (fb (put ki (cons :int64 iv) fa))
         (fc (mv-nth 1 (sx-list sv fb heap)))
         (fd (put kv (cons :int64 vv) fc))
         (fe (mv-nth 1 (sx-list ss fd heap)))
         (a (cddr (lkp c s1))))
    (implies (and (equal (car (sx-list si fr heap)) :normal) (equal (mv-nth 2 (sx-list si fr heap)) heap)
                  (not (car (sv ci fa heap))) (equal (mv-nth 1 (sv ci fa heap)) iv) (int64p iv)
                  (equal (dty ki fa) '(:int64))
                  (equal (car (sx-list sv fb heap)) :normal) (equal (mv-nth 2 (sx-list sv fb heap)) heap)
                  (not (car (sv cv fc heap))) (equal (mv-nth 1 (sv cv fc heap)) vv) (int64p vv)
                  (equal (dty kv fc) '(:int64))
                  (equal (car (sx-list ss fd heap)) :normal) (equal (mv-nth 2 (sx-list ss fd heap)) (put (okey o fr) s1 heap))
                  (not (member-equal ki (asgv :list sv))) (not (member-equal ki (asgv :list ss)))
                  (not (member-equal kv (asgv :list ss))) (not (equal ki kv))
                  (obj-at o s fd heap) (equal (okey o fd) (okey o fr))
                  (farrayp (cdr (lkp c s1))))
             (equal (sx-list (append si (list (list :assign (list :var ki) ci)) sv (list (list :assign (list :var kv) cv)) ss
                                     (list (list :assign (list :elem o c (list :var ki)) (list :var kv))))
                             fr heap)
                    (if (and (<= 0 iv) (< iv (len a)))
                        (mv :normal fe (put (okey o fr) (put c (cons :array (update-nth iv vv a)) s1) heap))
                      (mv (errst :bounds) fe (put (okey o fr) s1 heap))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(sx-list-append sx-list-one sx-assign-run scalar-ok (consp) (car) (equal) car-cons cdr-cons mv-nth-0-car
                                        mv-nth-cons-k (posp) (binary-+))
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance obj-at-after (s2 s1) (fr (fd)) (heap heap))
                 (:instance seti-okey (fd (fd)))
                 (:instance seti-sv-v (fc (fc)) (h2 (put (okey o fr) s1 heap)))
                 (:instance seti-sv-i (fa (fa)) (h2 (put (okey o fr) s1 heap)))
                 (:instance seti-last (fe (mv-nth 1 (sx-list ss (fd) heap))) (k (okey o fr)))))))

;; the element update's context: no error anywhere, gst-sem's hypotheses
(defmacro seti-ctx ()
  '(and (consp x) (true-listp x) (not (eq (car x) 'quote)) (eq (g-role (car x) st) :seti)
        (not (e1 0)) (equal (e1 3) :int64) (not (e2 0)) (equal (e2 3) :int64)
        (not (car (g-fresh 'i :int64 (e2 4) (e2 5) (append fnames (em-names em)))))
        (not (car (g-fresh 'v :int64 (1+ (nfix (e2 4))) (loci) (append fnames (em-names em)))))
        (not (e3 0))
        (not (car (a-sx (cadr x) env s st defs (1- n)))) (not (car (a-sx (caddr x) env s st defs (1- n))))
        (not (car (a-st (cadddr x) env s st defs (1- n))))
        (no-calls :term x sigs nil) (em-ok em env fr) (decl-ok (e3 3) fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
        (gst-sem (cadddr x) em (c3) (locw) sigs fnames st outs env s defs (1- n) (sfd) heap o)
        (stn-ok (cadddr x) em (c3) (locw) sigs fnames st outs)))

(defmacro seti-dis () '(set-difference-theories (current-theory :here) (list* 'g-fresh-out 'gs-sem-int64 'stn-ok-use 'gst-sem-use 'sn-ok-use (gst-hint-dis))))

;; the names: the temporaries are new, declared, and survive what follows them
(defthm seti-names-abs
  (implies (and (subsetp-equal l1 l2)
                (subsetp-equal (cons (cons kv ty) (true-list-fix (cons (cons ki ty) (true-list-fix l2)))) l3)
                (decl-ok l3 fr)
                (not (member-equal ki (append f e))) (not (member-equal ki (strip-cars l2)))
                (not (member-equal kv (append f e))) (not (member-equal kv (strip-cars (cons (cons ki ty) (true-list-fix l2)))))
                (subsetp-equal (asg :list s2) (strip-cars l2))
                (not (intersectp-equal (asgv :list s3) (append f e (strip-cars (cons (cons kv ty) (true-list-fix (cons (cons ki ty) (true-list-fix l2)))))))))
           (and (decl-ok l1 fr) (decl-ok l2 fr) (equal (dty ki fr) (list ty)) (equal (dty kv fr) (list ty))
                (not (equal ki kv)) (not (member-equal ki e)) (not (member-equal kv e))
                (not (member-equal ki (strip-cars l2))) (not (member-equal kv (strip-cars l2)))
                (not (member-equal ki (asgv :list s2)))
                (not (member-equal ki (asgv :list s3))) (not (member-equal kv (asgv :list s3)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance decl-ok-subset (a (cons (cons kv ty) (true-list-fix (cons (cons ki ty) (true-list-fix l2))))) (b l3))
                 (:instance decl-ok-subset (a l1) (b l2))
                 (:instance member-subset-not (k ki) (a (asg :list s2)) (b (strip-cars l2)))
                 (:instance member-subset-not (k ki) (a (asgv :list s2)) (b (asg :list s2)))
                 (:instance asgv-subset-asg (flag :list) (x s2))))))

(defthm seti-names
  (implies (seti-ctx)
           (and (decl-ok (e1 5) fr) (decl-ok (e2 5) fr)
                (equal (dty (tmi) fr) '(:int64)) (equal (dty (tmv) fr) '(:int64))
                (not (equal (tmi) (tmv))) (not (member-equal (tmi) (em-names em))) (not (member-equal (tmv) (em-names em)))
                (not (member-equal (tmi) (strip-cars (e2 5)))) (not (member-equal (tmv) (strip-cars (e2 5))))
                (not (member-equal (tmi) (asgv :list (e2 1))))
                (not (member-equal (tmi) (asgv :list (e3 1)))) (not (member-equal (tmv) (asgv :list (e3 1))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)
           :use ((:instance g-fresh-out (b 'i) (ty :int64) (cnt (e2 4)) (locs (e2 5)) (used (append fnames (em-names em))))
                 (:instance g-fresh-out (b 'v) (ty :int64) (cnt (1+ (nfix (e2 4)))) (locs (loci))
                            (used (append fnames (em-names em))))
                 (:instance sn-ok-holds (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance sn-ok-use (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance no-calls-set (cs nil)) (:instance g-role-quote (x (car x)))
                 (:instance stn-ok-use (x (cadddr x)) (cnt (c3)) (locs (locw)))
                 (:instance seti-names-abs (l1 (e1 5)) (l2 (e2 5)) (l3 (e3 3)) (kv (tmv)) (ki (tmi)) (ty :int64)
                            (f fnames) (e (em-names em)) (s2 (e2 1)) (s3 (e3 1)))))))

(defthm decl-ok-put-int
  (implies (and (decl-ok locs fr) (equal (dty k fr) '(:int64))) (decl-ok locs (put k (cons :int64 v) fr))))

(defthm obj-at-put-int
  (implies (and (obj-at o s fr heap) (equal (dty k fr) '(:int64)) (int64p v)) (obj-at o s (put k (cons :int64 v) fr) heap))
  :hints (("Goal" :in-theory (disable obj-at-put-scalar) :use (:instance obj-at-put-scalar (ty :int64)))))

(defthm dty-after-sx (equal (dty k (mv-nth 1 (sx-list ss fr heap))) (dty k fr)))

;; i's and v's statements and values, each at its frame
(defthm seti-vals
  (implies (seti-ctx)
           (and (equal (car (sx-list (e1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (e1 1) fr heap)) heap)
                (not (car (sv (e1 2) (sfa) heap)))
                (equal (mv-nth 1 (sv (e1 2) (sfa) heap)) (mv-nth 1 (a-sx (cadr x) env s st defs (1- n))))
                (int64p (mv-nth 1 (a-sx (cadr x) env s st defs (1- n))))
                (equal (car (sx-list (e2 1) (sfb) heap)) :normal) (equal (mv-nth 2 (sx-list (e2 1) (sfb) heap)) heap)
                (not (car (sv (e2 2) (sfc) heap)))
                (equal (mv-nth 1 (sv (e2 2) (sfc) heap)) (mv-nth 1 (a-sx (caddr x) env s st defs (1- n))))
                (int64p (mv-nth 1 (a-sx (caddr x) env s st defs (1- n))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(em-ok-put em-ok-after-sx decl-ok-put-int dty-after-sx decl-ok-after-sx obj-is-put-scalar
                                        obj-at-is obj-is-after-sx sx-list-keeps scalar-ok (cons) (equal))
                                      (theory 'minimal-theory))
           :use (seti-names (:instance no-calls-set (cs nil)) (:instance g-role-quote (x (car x)))
                 (:instance sn-ok-holds (x (cadr x)))
                 (:instance sn-ok-use (x (cadr x)))
                 (:instance gs-sem-holds (x (cadr x)) (n (1- n)))
                 (:instance gs-sem-use (x (cadr x)) (n (1- n)))
                 (:instance gs-sem-int64 (x (cadr x)) (n (1- n)))
                 (:instance gs-sem-holds (x (caddr x)) (cnt (e1 4)) (locs (e1 5)) (n (1- n)) (fr (sfb)))
                 (:instance gs-sem-use (x (caddr x)) (cnt (e1 4)) (locs (e1 5)) (n (1- n)) (fr (sfb)))
                 (:instance gs-sem-int64 (x (caddr x)) (cnt (e1 4)) (locs (e1 5)) (n (1- n)) (fr (sfb)))))))

;; the object through the two temporaries' frames
(defthm obj-at-seti-frames
  (implies (and (obj-at o s fr heap) (equal (dty ki fr) '(:int64)) (equal (dty kv fr) '(:int64)) (int64p iv) (int64p vv))
           (let ((fd (put kv (cons :int64 vv) (mv-nth 1 (sx-list s2 (put ki (cons :int64 iv) (mv-nth 1 (sx-list s1 fr heap))) heap)))))
             (and (obj-at o s fd heap) (equal (okey o fd) (okey o fr)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable obj-at okey sx-list int64p)
           :use ((:instance obj-at-cadr) 
                 (:instance obj-at-cadr (fr (mv-nth 1 (sx-list s1 fr heap))))
                 (:instance obj-at-cadr (fr (put ki (cons :int64 iv) (mv-nth 1 (sx-list s1 fr heap)))))
                 (:instance obj-at-cadr (fr (mv-nth 1 (sx-list s2 (put ki (cons :int64 iv) (mv-nth 1 (sx-list s1 fr heap))) heap))))))))

;; the inner update's statements, at the frame after v's temporary
(defthm seti-inner
  (implies (seti-ctx)
           (and (obj-at o s (sfd) heap) (equal (okey o (sfd)) (okey o fr))
                (equal (car (sx-list (e3 1) (sfd) heap)) :normal)
                (equal (mv-nth 2 (sx-list (e3 1) (sfd) heap)) (put (okey o fr) (mv-nth 1 (a-st (cadddr x) env s st defs (1- n))) heap))
                (st-ok st o (mv-nth 1 (a-st (cadddr x) env s st defs (1- n))))
                (st-wf st (mv-nth 1 (a-st (cadddr x) env s st defs (1- n))))
                (farrayp (cdr (lkp (g-comp (car x) st) (mv-nth 1 (a-st (cadddr x) env s st defs (1- n))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(em-ok-put em-ok-after-sx decl-ok-put-int dty-after-sx dty-put decl-ok-after-sx
                                        obj-at-seti-frames scalar-ok st-wf-seti (cons) (equal) (consp) (car))
                                      (theory 'minimal-theory))
           :use (seti-names seti-vals (:instance no-calls-set (cs nil)) (:instance g-role-quote (x (car x)))
                 (:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-use (x (cadr x)))
                 (:instance sn-ok-holds (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance sn-ok-use (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance gst-sem-use (x (cadddr x)) (cnt (c3)) (locs (locw)) (n (1- n)) (fr (sfd)))
                 (:instance st-wf-seti (x (car x)) (s (mv-nth 1 (a-st (cadddr x) env s st defs (1- n)))))))))

;; S' keeps st-ok and st-wf
(defthm seti-s2
  (implies (and (st-ok st o s1) (st-wf st s1) (farrayp (cdr (lkp c s1))) (natp i) (< i (len (cddr (lkp c s1)))))
           (and (st-ok st o (put c (cons :array (update-nth i v (cddr (lkp c s1)))) s1))
                (st-wf st (put c (cons :array (update-nth i v (cddr (lkp c s1)))) s1))))
  :hints (("Goal" :in-theory (disable st-ok st-wf))))


(defun-nx seti-ctxp (x em cnt locs sigs fnames st outs env s defs n fr heap o) (seti-ctx))
(in-theory (disable seti-ctxp))

(defmacro sfe () '(mv-nth 1 (sx-list (e3 1) (sfd) heap)))
(defmacro sts () '(mv-nth 1 (a-st (cadddr x) env s st defs (1- n))))
(defmacro seti-stmts ()
  '(append (e1 1) (list (list :assign (list :var (tmi)) (e1 2))) (e2 1) (list (list :assign (list :var (tmv)) (e2 2))) (e3 1)
           (list (list :assign (list :elem o (g-comp (car x) st) (list :var (tmi))) (list :var (tmv))))))

;; the statements run: S' put, or the write's :bounds
(defthm seti-run
  (let ((iv (mv-nth 1 (a-sx (cadr x) env s st defs (1- n)))) (a (cddr (lkp (g-comp (car x) st) (sts)))))
    (implies (seti-ctxp x em cnt locs sigs fnames st outs env s defs n fr heap o)
             (and (equal (sx-list (seti-stmts) fr heap)
                         (if (and (<= 0 iv) (< iv (len a)))
                             (mv :normal (sfe) (put (okey o fr) (put (g-comp (car x) st)
                                                                     (cons :array (update-nth iv (mv-nth 1 (a-sx (caddr x) env s st defs (1- n))) a))
                                                                     (sts)) heap))
                           (mv (errst :bounds) (sfe) (put (okey o fr) (sts) heap))))
                  (st-ok st o (sts)) (st-wf st (sts)) (farrayp (cdr (lkp (g-comp (car x) st) (sts)))))))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(seti-ctxp dty-after-sx dty-put) (theory 'minimal-theory))
           :use (seti-names seti-vals seti-inner
                 (:instance seti-glue (si (e1 1)) (ci (e1 2)) (sv (e2 1)) (cv (e2 2)) (ss (e3 1)) (ki (tmi)) (kv (tmv))
                            (c (g-comp (car x) st))
                            (iv (mv-nth 1 (a-sx (cadr x) env s st defs (1- n))))
                            (vv (mv-nth 1 (a-sx (caddr x) env s st defs (1- n))))
                            (s1 (sts)))))))

(defthm gst-seti
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :seti)
                (gst-sem (cadddr x) em (c3) (locw) sigs fnames st outs env s defs (1- n) (sfd) heap o)
                (stn-ok (cadddr x) em (c3) (locw) sigs fnames st outs))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
           :in-theory (union-theories '(g-stmt-seti a-st-seti g-fresh-out g-fresh-cnt mv-nth-0-car mv-nth-cons-k seti-s2 put-put-same
                                        seti-ctxp st-ok-obj (member-equal) (equal) (cons) (natp) (posp) (binary-+) (unary--)
                                        natp-compound-recognizer car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (seti-run))))

;; the write's :bounds, both sides: i, v and s answering, a-st's :bounds is the code's
(defthm gst-seti-bounds
  (implies (and (consp x) (true-listp x) (not (eq (car x) 'cons)) (not (eq (car x) 'quote))
                (eq (g-role (car x) st) :seti)
                (gst-sem (cadddr x) em (c3) (locw) sigs fnames st outs env s defs (1- n) (sfd) heap o)
                (stn-ok (cadddr x) em (c3) (locw) sigs fnames st outs)
                (not (gtx 0)) (equal (car (a-st x env s st defs n)) :bounds)
                (not (car (a-sx (cadr x) env s st defs (1- n)))) (not (car (a-sx (caddr x) env s st defs (1- n))))
                (not (car (a-st (cadddr x) env s st defs (1- n))))
                (no-calls :term x sigs nil) (em-ok em env fr) (decl-ok (gtx 3) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st))
           (equal (car (sx-list (gtx 1) fr heap)) (errst :bounds)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(g-stmt-seti a-st-seti g-fresh-out g-fresh-cnt mv-nth-0-car mv-nth-cons-k
                                        seti-ctxp st-ok-obj (member-equal) (equal) (cons) (posp) (binary-+) (unary--)
                                        natp-compound-recognizer car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (seti-run))))

; ---- if: the test's statements, then IF (c) THEN a ELSE b, both branches
; at the frame after the test

(defthm g-stmt-if
  (implies (and (consp x) (true-listp x) (eq (car x) 'if) (not (g-role 'if st)))
           (equal (g-stmt x em cnt locs sigs fnames st outs nil nil)
                  (if (or (not (= (len x) 4)) (<= 3 (g-chain x nil nil))) (mv :stobj nil cnt locs)
                    (mv-let (e sc cc tc cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                      (if (or e (not (eq tc :logical))) (mv (or e :type) nil cnt locs)
                        (mv-let (e sa cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs nil nil)
                          (if e (mv e nil cnt locs)
                            (mv-let (e sb cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs nil nil)
                              (if e (mv e nil cnt locs)
                                (mv nil (append sc (list (list :if cc sa sb))) cnt locs))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs nil nil)))))

(defthm a-st-if
  (implies (and (consp x) (eq (car x) 'if) (not (g-role 'if st)))
           (equal (a-st x env s st defs n)
                  (if (zp n) (mv :fuel s)
                    (mv-let (e c) (a-sx (cadr x) env s st defs (1- n))
                      (cond (e (mv e s))
                            (c (a-st (caddr x) env s st defs (1- n)))
                            (t (a-st (cadddr x) env s st defs (1- n))))))))
  :hints (("Goal" :in-theory (e/d (kadr kaddr kadddr kar) (g-role a-sx)) :expand ((a-st x env s st defs n)))))

(defmacro ia (k) `(mv-nth ,k (g-stmt (caddr x) em (e1 4) (e1 5) sigs fnames st outs nil nil)))
(defmacro ib (k) `(mv-nth ,k (g-stmt (cadddr x) em (ia 2) (ia 3) sigs fnames st outs nil nil)))

;; the if's statements on abstract parts
(defthm sif-st-glue
  (let ((fr1 (mv-nth 1 (sx-list sc fr heap))))
    (implies (and (equal (car (sx-list sc fr heap)) :normal) (equal (mv-nth 2 (sx-list sc fr heap)) heap)
                  (not (car (sv cc fr1 heap))) (booleanp (mv-nth 1 (sv cc fr1 heap))))
             (let ((l (sx-list (append sc (list (list :if cc sa sb))) fr heap))
                   (b (if (mv-nth 1 (sv cc fr1 heap)) (sx-list sa fr1 heap) (sx-list sb fr1 heap))))
               (and (equal (car l) (car b)) (equal (mv-nth 1 l) (mv-nth 1 b)) (equal (mv-nth 2 l) (mv-nth 2 b))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (e/d (sx-list-append) (sx sv sx-list)))))

(defmacro if-ctx ()
  '(and (consp x) (true-listp x) (eq (car x) 'if) (not (e1 0)) (equal (e1 3) :logical) (not (ia 0)) (not (ib 0))
        (not (car (a-sx (cadr x) env s st defs (1- n))))
        (implies (mv-nth 1 (a-sx (cadr x) env s st defs (1- n))) (not (car (a-st (caddr x) env s st defs (1- n)))))
        (implies (not (mv-nth 1 (a-sx (cadr x) env s st defs (1- n)))) (not (car (a-st (cadddr x) env s st defs (1- n)))))
        (no-calls :term x sigs nil) (em-ok em env fr) (decl-ok (ib 3) fr)
        (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
        (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st)
        (gst-sem (caddr x) em (e1 4) (e1 5) sigs fnames st outs env s defs (1- n) (sfa) heap o)
        (gst-sem (cadddr x) em (ia 2) (ia 3) sigs fnames st outs env s defs (1- n) (sfa) heap o)
        (stn-ok (caddr x) em (e1 4) (e1 5) sigs fnames st outs)
        (stn-ok (cadddr x) em (ia 2) (ia 3) sigs fnames st outs)))

(defun-nx if-ctxp (x em cnt locs sigs fnames st outs env s defs n fr heap o) (if-ctx))
(in-theory (disable if-ctxp))

(defmacro ifc () '(mv-nth 1 (a-sx (cadr x) env s st defs (1- n))))

(defthm if-run
  (implies (if-ctxp x em cnt locs sigs fnames st outs env s defs n fr heap o)
           (and (equal (car (sx-list (e1 1) fr heap)) :normal) (equal (mv-nth 2 (sx-list (e1 1) fr heap)) heap)
                (not (car (sv (e1 2) (sfa) heap))) (equal (mv-nth 1 (sv (e1 2) (sfa) heap)) (ifc)) (booleanp (ifc))
                (implies (ifc)
                         (and (equal (car (sx-list (ia 1) (sfa) heap)) :normal)
                              (equal (mv-nth 2 (sx-list (ia 1) (sfa) heap))
                                     (put (okey o fr) (mv-nth 1 (a-st (caddr x) env s st defs (1- n))) heap))
                              (st-ok st o (mv-nth 1 (a-st (caddr x) env s st defs (1- n))))
                              (st-wf st (mv-nth 1 (a-st (caddr x) env s st defs (1- n))))))
                (implies (not (ifc))
                         (and (equal (car (sx-list (ib 1) (sfa) heap)) :normal)
                              (equal (mv-nth 2 (sx-list (ib 1) (sfa) heap))
                                     (put (okey o fr) (mv-nth 1 (a-st (cadddr x) env s st defs (1- n))) heap))
                              (st-ok st o (mv-nth 1 (a-st (cadddr x) env s st defs (1- n))))
                              (st-wf st (mv-nth 1 (a-st (cadddr x) env s st defs (1- n))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(if-ctxp em-ok-after-sx decl-ok-after-sx obj-at-frame obj-at-cadr okey-after obj-at-is
                                        obj-is-after-sx scalar-ok (equal) (consp))
                                      (theory 'minimal-theory))
           :use ((:instance no-calls-set (cs nil))
                 (:instance sn-ok-holds (x (cadr x))) (:instance sn-ok-use (x (cadr x)))
                 (:instance gs-sem-holds (x (cadr x)) (n (1- n)))
                 (:instance gs-sem-use (x (cadr x)) (n (1- n)))
                 (:instance stn-ok-use (x (caddr x)) (cnt (e1 4)) (locs (e1 5)))
                 (:instance stn-ok-use (x (cadddr x)) (cnt (ia 2)) (locs (ia 3)))
                 (:instance decl-ok-subset (a (ia 3)) (b (ib 3)))
                 (:instance decl-ok-subset (a (e1 5)) (b (ia 3)))
                 (:instance gst-sem-use (x (caddr x)) (cnt (e1 4)) (locs (e1 5)) (n (1- n)) (fr (sfa)))
                 (:instance gst-sem-use (x (cadddr x)) (cnt (ia 2)) (locs (ia 3)) (n (1- n)) (fr (sfa)))))))

(defthm gst-if
  (implies (and (consp x) (true-listp x) (eq (car x) 'if) (sn-hyps)
                (gst-sem (caddr x) em (e1 4) (e1 5) sigs fnames st outs env s defs (1- n) (sfa) heap o)
                (gst-sem (cadddr x) em (ia 2) (ia 3) sigs fnames st outs env s defs (1- n) (sfa) heap o)
                (stn-ok (caddr x) em (e1 4) (e1 5) sigs fnames st outs)
                (stn-ok (cadddr x) em (ia 2) (ia 3) sigs fnames st outs))
           (gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gst-sem x em cnt locs sigs fnames st outs env s defs n fr heap o))
           :in-theory (union-theories '(g-stmt-if a-st-if if-ctxp mv-nth-0-car mv-nth-cons-k (equal) (cons) (posp) (binary-+)
                                        (unary--) car-cons cdr-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (if-run (:instance sif-st-glue (sc (e1 1)) (cc (e1 2)) (sa (ia 1)) (sb (ib 1)))))))
