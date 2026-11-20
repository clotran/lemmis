; gen-st-xvec: p-sorc-d, part 3 (GEN.md "Left of 4c step 3" (ii)). hpg_scan_vec (no loop:
; hp_n_vec, voff/vlen read through max(0,..), a CALL of hpg_scan_run) run on hs's entry; then
; p-sorc-d-holds (drain's CALLs of hpg_scan_obj and hpg_scan_vec answer s-call-val-d) and
; hpg-drain-fortran-correct-x, with nothing past the ground xp-finds and the state facts
; xd-lens and nt-lens.

(in-package "ACL2")

(include-book "gen-st-xdrain")

; ---- hpg_scan_vec: one lemma per statement

(defconst *sv-ls* (nth 4 *sv-proc*))
(defconst *sv-body* (nth 5 *sv-proc*))

(defthm sv-proc-shape
  (equal *sv-proc* (list :subroutine "hpg_scan_vec" (nth 2 *sv-proc*)
                         (cons (list "hs" :inout "heap_state") (g-dummies '(i))) *sv-ls* *sv-body*))
  :rule-classes nil)

(defconst *sv-v1* (nth 0 *sv-body*))
(defconst *sv-g* (nth 2 (nth 1 *sv-body*)))
(assert-event (and (equal (len *sv-body*) 2) (equal (nth 3 (nth 1 *sv-body*)) nil) (equal (len *sv-g*) 4)
                   (equal (nth 3 (nth 3 *sv-g*)) nil)))

(defun-nx sv-env (procs heap key cm hpg i)
  (and (xp-finds) (natp i) (int64p i) (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (dr-heap-at heap key cm hpg)))
(defthm sv-env-heap (implies (sv-env procs heap key cm hpg i)
                             (and (dr-heap-at heap key cm hpg) (natp i) (equal (find-proc "hpg_scan_run" procs) *sr-proc*)))
  :rule-classes :forward-chaining)
(defmacro sv-fr (fr) `(and (dr-frp ,fr *sv-ls*) (dr-hs-at ,fr key) (rf-v-at ,fr "i_" i)))
(defmacro sv-hyps () '(and (sv-env procs heap key cm hpg i) (sv-fr fr)))

(defmacro sv-off () '(nfix (nth i (nth *h-voffi* hpg))))
(defmacro sv-n () '(nfix (nth i (nth *h-vleni* hpg))))
(defmacro sv-c () '(and (<= off *hb40*) (<= n *hb40*) (<= (+ off n) *hb40*)))

(defmacro sv-iter-thy (&rest en)
  `(e/d (sv-env obj-of int64p ext-op ext-read-p ext-write-p ext-dums ,@en)
        (f-ev f-bind f-ex hs-rep hpgp hpg-ok xd-lens nt-lens dr-heap-at hpg-push hpg-scan-run hpg-scan-vec)))

(make-event
 `(defthm sv-v1
    (implies (and (sv-hyps) (integerp fu) (< 40 fu))
             (let ((r (f-ex *sv-v1* fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (sv-fr (mv-nth 1 r))
                    (equal (lkp "t_1" (mv-nth 1 r)) (list* "t_1" :logical (< i (len (nth *h-vmarki* hpg))))))))
    :hints (("Goal" :do-not-induct t :in-theory (sv-iter-thy)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *sv-proc*)))))))

(make-event
 `(defthm sv-g1
    (implies (and (sv-hyps) (< i (len (nth *h-vmarki* hpg))) (integerp fu) (< 40 fu))
             (let ((r (f-ex (nth 0 *sv-g*) fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (sv-fr (mv-nth 1 r))
                    (rf-v-at (mv-nth 1 r) "off_2" (sv-off)))))
    :hints (("Goal" :do-not-induct t :in-theory (sv-iter-thy xd-lens-arena)
             :use ((:instance xd-voff-elem (j i)))
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *sv-proc*)))))))

(make-event
 `(defthm sv-g2
    (implies (and (sv-hyps) (< i (len (nth *h-vmarki* hpg))) (rf-v-at fr "off_2" off) (integerp fu) (< 40 fu))
             (let ((r (f-ex (nth 1 *sv-g*) fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (sv-fr (mv-nth 1 r))
                    (rf-v-at (mv-nth 1 r) "off_2" off) (rf-v-at (mv-nth 1 r) "n_3" (sv-n)))))
    :hints (("Goal" :do-not-induct t :in-theory (sv-iter-thy xd-lens-arena)
             :use ((:instance xd-vlen-elem (j i)))
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *sv-proc*)))))))

(make-event
 `(defthm sv-g3
    (implies (and (sv-hyps) (rf-v-at fr "off_2" off) (rf-v-at fr "n_3" n) (int64p off) (natp off) (int64p n) (natp n)
                  (integerp fu) (< 40 fu))
             (let ((r (f-ex (nth 2 *sv-g*) fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (sv-fr (mv-nth 1 r))
                    (rf-v-at (mv-nth 1 r) "off_2" off) (rf-v-at (mv-nth 1 r) "n_3" n)
                    (equal (lkp "t_5" (mv-nth 1 r)) (list* "t_5" :logical (sv-c))))))
    :hints (("Goal" :do-not-induct t :in-theory (sv-iter-thy)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *sv-proc*)))))))

(defmacro sv-kb () '(+ 100 (sr-kx) (acl2-count *sv-body*)))

(defthm sv-sr-env
  (implies (and (sv-env procs heap key cm hpg i) (natp off) (natp n) (sv-c))
           (sr-env procs heap key cm hpg off (+ off n)))
  :hints (("Goal" :in-theory (e/d (sv-env sr-env) (hpgp hpg-ok xd-lens nt-lens dr-heap-at)))))

(make-event
 `(defthm sv-g4
  (implies (and (sv-hyps) (rf-v-at fr "off_2" off) (rf-v-at fr "n_3" n) (int64p off) (natp off) (int64p n) (natp n)
                (equal (lkp "t_5" fr) (list* "t_5" :logical (sv-c)))
                (integerp fu) (< (sv-kb) fu))
           (let ((r (f-ex-list (cdddr *sv-g*) fr heap procs fu)))
             (and (equal (car r) :normal)
                  (equal (mv-nth 2 r) (if (sv-c) (put key (hs-rep cm (hpg-scan-run off (+ off n) hpg)) heap) heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (set-difference-theories (rf-c-thy) '(sv-env sr-env hpg-scan-run xd-lens nt-lens hpg-ok))
                                      '(sv-sr-env int64p))
           :use (sv-sr-env
                 (:instance xd-ex-sr (ob "hs") (c1 '(:var "off_2")) (c2 '(:add (:var "off_2") (:var "n_3"))) (j off) (e (+ off n))
                            (fuel (- fu 3))))
           :expand ((f-ex-list ',(cdddr *sv-g*) fr heap procs fu)
                    (f-ex ',(nth 3 *sv-g*) fr heap procs (- fu 1))
                    (:free (fr h k) (f-ex-list nil fr h procs k))
                    (:free (fr h k) (f-ex-list '((:call "hpg_scan_run" ((:var "hs") (:var "off_2") (:add (:var "off_2") (:var "n_3")))))
                                               fr h procs k))
                    (:free (fr h k) (f-ev '(:var "t_5") fr h procs k))
                    (sv '(:var "off_2") fr heap) (sv '(:add (:var "off_2") (:var "n_3")) fr heap)
                    (:free (e) (sv (list :var e) fr heap)))))))

(defmacro sv-c-thy (&rest en)
  `(union-theories (set-difference-theories (rf-c-thy)
                                            '(sv-v1 sv-g1 sv-g2 sv-g3 sv-g4 sv-env sr-env hpg-scan-run hpg-scan-vec xd-lens nt-lens hpg-ok
                                              xd-ex-ps-run xd-ex-ps-obj ps-run ps-ok sp-run sp-ok))
                   ',en))

(make-event
 `(defthm sv-t3
    (implies (and (sv-hyps) (rf-v-at fr "off_2" off) (rf-v-at fr "n_3" n) (int64p off) (natp off) (int64p n) (natp n)
                  (integerp fu) (< (+ 2 (sv-kb)) fu))
             (let ((r (f-ex-list (cddr *sv-g*) fr heap procs fu)))
               (and (equal (car r) :normal)
                    (equal (mv-nth 2 r) (if (sv-c) (put key (hs-rep cm (hpg-scan-run off (+ off n) hpg)) heap) heap)))))
    :hints (("Goal" :do-not-induct t :in-theory (sv-c-thy)
             :expand ((f-ex-list ',(cddr *sv-g*) fr heap procs fu))
             :use ((:instance sv-g3 (fu (- fu 1)))
                   (:instance sv-g4 (fr (mv-nth 1 (f-ex (nth 2 *sv-g*) fr heap procs (- fu 1)))) (fu (- fu 1))))))))

(make-event
 `(defthm sv-t2
    (implies (and (sv-hyps) (< i (len (nth *h-vmarki* hpg))) (rf-v-at fr "off_2" off) (int64p off) (natp off)
                  (int64p (sv-n)) (integerp fu) (< (+ 4 (sv-kb)) fu))
             (let ((r (f-ex-list (cdr *sv-g*) fr heap procs fu)) (n (sv-n)))
               (and (equal (car r) :normal)
                    (equal (mv-nth 2 r) (if (sv-c) (put key (hs-rep cm (hpg-scan-run off (+ off n) hpg)) heap) heap)))))
    :hints (("Goal" :do-not-induct t :in-theory (sv-c-thy)
             :expand ((f-ex-list ',(cdr *sv-g*) fr heap procs fu))
             :use ((:instance sv-g2 (fu (- fu 1)))
                   (:instance sv-t3 (fr (mv-nth 1 (f-ex (nth 1 *sv-g*) fr heap procs (- fu 1)))) (n (sv-n)) (fu (- fu 1))))))))

(defthm sv-elems
  (implies (and (sv-env procs heap key cm hpg i) (< i (len (nth *h-vmarki* hpg))))
           (and (int64p (sv-off)) (int64p (sv-n))))
  :hints (("Goal" :in-theory (e/d (sv-env int64p xd-lens-arena) (hpgp hpg-ok xd-lens nt-lens dr-heap-at))
           :use ((:instance xd-voff-elem (j i)) (:instance xd-vlen-elem (j i))))))

(make-event
 `(defthm sv-t1
    (implies (and (sv-hyps) (< i (len (nth *h-vmarki* hpg))) (integerp fu) (< (+ 6 (sv-kb)) fu))
             (let ((r (f-ex-list *sv-g* fr heap procs fu)) (off (sv-off)) (n (sv-n)))
               (and (equal (car r) :normal)
                    (equal (mv-nth 2 r) (if (sv-c) (put key (hs-rep cm (hpg-scan-run off (+ off n) hpg)) heap) heap)))))
    :hints (("Goal" :do-not-induct t :in-theory (sv-c-thy sv-env xd-lens-arena int64p)
             :expand ((f-ex-list ',*sv-g* fr heap procs fu))
             :use ((:instance xd-voff-elem (j i)) (:instance xd-vlen-elem (j i))
                   (:instance sv-g1 (fu (- fu 1)))
                   (:instance sv-t2 (fr (mv-nth 1 (f-ex (nth 0 *sv-g*) fr heap procs (- fu 1)))) (off (sv-off)) (fu (- fu 1))))))))

(defthm sv-vec-is
  (implies (and (sv-env procs heap key cm hpg i))
           (equal (hpg-scan-vec i hpg)
                  (if (< i (len (nth *h-vmarki* hpg)))
                      (let ((off (sv-off)) (n (sv-n))) (if (sv-c) (hpg-scan-run off (+ off n) hpg) hpg))
                    hpg)))
  :hints (("Goal" :in-theory (e/d (sv-env hpg-scan-vec h-voff-length h-vlen-length h-voffi h-vleni xd-lens-arena)
                                  (hpgp hpg-ok xd-lens nt-lens dr-heap-at hpg-scan-run)))))

(make-event
 `(defthm sv-run
    (implies (and (sv-hyps) (integerp fu) (< (+ 10 (sv-kb)) fu))
             (let ((r (f-ex-list *sv-body* fr heap procs fu)))
               (and (equal (mv-nth 0 r) :normal)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (hpg-scan-vec i hpg)) heap)))))
    :hints (("Goal" :do-not-induct t :in-theory (sv-c-thy sv-vec-is sv-env-heap xd-put-same)
             :use ((:instance sv-v1 (fu (- fu 1)))
                   (:instance sv-t1 (fr (mv-nth 1 (f-ex *sv-v1* fr heap procs (- fu 1)))) (fu (- fu 3))))
             :expand ((f-ex-list ',*sv-body* fr heap procs fu)
                      (:free (fr h) (f-ex-list ',(cdr *sv-body*) fr h procs (- fu 1)))
                      (:free (fr h) (f-ex ',(nth 1 *sv-body*) fr h procs (- fu 2)))
                      (:free (fr h) (f-ev '(:var "t_1") fr h procs (- fu 3)))
                      (:free (fr h k) (f-ex-list nil fr h procs k)))))))

; ---- hpg_scan_vec's invocation, and its CALL on an argument code

(defmacro sv-frame () '(undef-locals *sv-ls* (fb '(i) (list i) (put "hs" (list* :obj :inout key) nil))))

(defthm sv-frame-hyps
  (sv-fr (sv-frame))
  :hints (("Goal" :in-theory (enable fb dr-hs-at rf-v-at))))

(defmacro sv-kx () '(+ 20 (sv-kb)))

(defthm sv-env-int (implies (sv-env procs heap key cm hpg i) (int64-listp (list i)))
  :rule-classes nil :hints (("Goal" :in-theory (enable sv-env))))

(defthm sv-ok
  (implies (and (sv-env procs heap key cm hpg i) (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (integerp fuel) (< (sv-kx) fuel))
           (equal (f-invoke *sv-proc* (cons (list :var ob) (g-lits (list i))) caller heap procs fuel)
                  (mv nil caller (put key (hs-rep cm (hpg-scan-vec i hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(natp len car-cons cdr-cons (len) (g-dummies) (nth) (cons) (equal) (acl2-count) (binary-+) (unary--))
                                      (theory 'minimal-theory))
           :use (sv-proc-shape sv-env-int
                 (:instance sv-frame-hyps)
                 (:instance sv-run (fr (sv-frame)) (fu (1- fuel)))
                 (:instance f-invoke-sub-d (ks (list i)) (vs '(i)) (o "hs") (c "heap_state") (nm "hpg_scan_vec")
                            (rec (nth 2 *sv-proc*)) (ls *sv-ls*) (body *sv-body*))))))

(defthm svs-is-1
  (implies (not (mv-nth 0 (sv x1 fr heap))) (svs-is (list x1) (list (mv-nth 1 (sv x1 fr heap))) fr heap))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable svs-is))))

(defthm sv-okc
  (implies (and (sv-env procs heap key cm hpg i) (equal (cdr (lkp ob fr)) (list* :obj :inout key))
                (not (mv-nth 0 (sv c1 fr heap))) (equal (mv-nth 1 (sv c1 fr heap)) i)
                (integerp fuel) (< (+ (sv-kx) (acl2-count (list c1))) fuel))
           (equal (f-invoke *sv-proc* (list (list :var ob) c1) fr heap procs fuel)
                  (mv nil fr (put key (hs-rep cm (hpg-scan-vec i hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(len (len) (g-dummies) (kar) (nth) (true-list-fix) (equal) car-cons cdr-cons
                                        (:type-prescription acl2-count))
                                      (theory 'minimal-theory))
           :use (sv-proc-shape sv-env-int
                 (:instance svs-is-1 (x1 c1))
                 (:instance f-invoke-st-codes (p *sv-proc*) (d '("hs" :inout "heap_state")) (vs '(i))
                            (a (list :var ob)) (cs (list c1)) (ks (list i)) (caller fr))
                 (:instance sv-ok (caller fr))))))

(defthm xd-ex-sv
  (implies (and (equal (find-proc "hpg_scan_vec" procs) *sv-proc*)
                (sv-env procs heap key cm hpg i) (equal (cdr (lkp ob fr)) (list* :obj :inout key))
                (not (mv-nth 0 (sv c1 fr heap))) (equal (mv-nth 1 (sv c1 fr heap)) i)
                (integerp fuel) (< (+ 1 (sv-kx) (acl2-count (list c1))) fuel))
           (equal (f-ex (list :call "hpg_scan_vec" (list (list :var ob) c1)) fr heap procs fuel)
                  (mv :normal fr (put key (hs-rep cm (hpg-scan-vec i hpg)) heap))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable f-invoke sv-okc sv-env sv hs-rep put hpg-scan-vec)
           :expand ((f-ex (list :call "hpg_scan_vec" (list (list :var ob) c1)) fr heap procs fuel))
           :use ((:instance sv-okc (fuel (1- fuel)))))))

; ---- p-sorc-d: a CALL the oracle answers, f-ex answers the same

(defmacro ds-ob () '(kadr (car a)))
(defmacro ds-key () '(mv-nth 1 (obj-of (ds-ob) fr)))
(defmacro ds-e () '(cdr (lkp (ds-key) heap)))
(defmacro ds-hpg () '(hs-hpg (ds-e)))
(defmacro ds-v (c) `(mv-nth 1 (sv ,c fr heap)))

(defthm xd-scv-name
  (implies (not (mv-nth 0 (s-call-val-d name a fr heap)))
           (or (equal name "hpg_scan_obj") (equal name "hpg_scan_vec")))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s-call-val-d kar kdr kadr kaddr mv-nth zp car-cons cdr-cons len true-listp eq not natp
                                       (zp) (equal) (len) (true-listp) (mv-nth) (kar) (kdr) (cons) (binary-+) (unary--) (<) (natp))
                                     (theory 'minimal-theory)))))

(defthm xd-list-3 (implies (and (true-listp a) (equal (len a) 3)) (equal (list (car a) (cadr a) (caddr a)) a)) :rule-classes nil)
(defthm xd-list-2 (implies (and (true-listp a) (equal (len a) 2)) (equal (list (car a) (cadr a)) a)) :rule-classes nil)

(defthm xd-scv-obj
  (implies (and (equal name "hpg_scan_obj") (not (mv-nth 0 (s-call-val-d name a fr heap))))
           (and (equal a (list (list :var (ds-ob)) (cadr a) (caddr a)))
                (equal (cdr (lkp (ds-ob) fr)) (list* :obj :inout (ds-key)))
                (dr-heap-at heap (ds-key) (ds-e) (ds-hpg)) (hpgp (ds-hpg)) (hpg-ok (ds-hpg)) (xd-lens (ds-hpg)) (nt-lens (ds-hpg))
                (natp (ds-v (cadr a))) (< (ds-v (cadr a)) *hb40*) (natp (ds-v (caddr a))) (<= (ds-v (caddr a)) 5)
                (not (mv-nth 0 (sv (cadr a) fr heap))) (not (mv-nth 0 (sv (caddr a) fr heap)))
                (equal (mv-nth 1 (s-call-val-d name a fr heap)) fr)
                (equal (mv-nth 2 (s-call-val-d name a fr heap))
                       (put (ds-key) (hs-rep (ds-e) (hpg-scan-obj (ds-v (cadr a)) (ds-v (caddr a)) (ds-hpg))) heap))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(s-call-val-d kar kdr kadr kaddr mv-nth zp car-cons cdr-cons len true-listp eq not natp
                                       (zp) (equal) (len) (true-listp) (mv-nth) (kar) (kdr) (cons) (binary-+) (unary--) (<) (natp))
                                     (theory 'minimal-theory))
           :use (xd-list-3 (:instance obj-of-binding (ob (ds-ob)) (caller fr))))))

(defthm xd-scv-vec
  (implies (and (equal name "hpg_scan_vec") (not (mv-nth 0 (s-call-val-d name a fr heap))))
           (and (equal a (list (list :var (ds-ob)) (cadr a)))
                (equal (cdr (lkp (ds-ob) fr)) (list* :obj :inout (ds-key)))
                (dr-heap-at heap (ds-key) (ds-e) (ds-hpg)) (hpgp (ds-hpg)) (hpg-ok (ds-hpg)) (xd-lens (ds-hpg)) (nt-lens (ds-hpg))
                (natp (ds-v (cadr a))) (int64p (ds-v (cadr a)))
                (not (mv-nth 0 (sv (cadr a) fr heap)))
                (equal (mv-nth 1 (s-call-val-d name a fr heap)) fr)
                (equal (mv-nth 2 (s-call-val-d name a fr heap))
                       (put (ds-key) (hs-rep (ds-e) (hpg-scan-vec (ds-v (cadr a)) (ds-hpg))) heap))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(s-call-val-d kar kdr kadr kaddr mv-nth zp car-cons cdr-cons len true-listp eq not natp
                                       (zp) (equal) (len) (true-listp) (mv-nth) (kar) (kdr) (cons) (binary-+) (unary--) (<) (natp))
                                     (theory 'minimal-theory))
           :use (xd-list-2 (:instance obj-of-binding (ob (ds-ob)) (caller fr))))))

(defthm so-env-intro
  (implies (and (xp-finds) (natp i) (< i *hb40*) (natp k) (<= k 5)
                (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (dr-heap-at heap key cm hpg))
           (so-env procs heap key cm hpg i k))
  :rule-classes nil :hints (("Goal" :in-theory (union-theories '(so-env) (theory 'minimal-theory)))))
(defthm sv-env-intro
  (implies (and (xp-finds) (natp i) (int64p i) (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (dr-heap-at heap key cm hpg))
           (sv-env procs heap key cm hpg i))
  :rule-classes nil :hints (("Goal" :in-theory (union-theories '(sv-env) (theory 'minimal-theory)))))

(defthm xd-count-args
  (implies (equal (kar x) :call) (< (acl2-count (cdr (kaddr x))) (acl2-count x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable kaddr kar))))

(defthm xd-count-3
  (implies (and (equal (kar x) :call) (equal (kaddr x) (list a0 a1 a2))) (< (acl2-count (list a1 a2)) (acl2-count x)))
  :rule-classes nil :hints (("Goal" :use xd-count-args :in-theory (disable xd-count-args))))
(defthm xd-count-2
  (implies (and (equal (kar x) :call) (equal (kaddr x) (list a0 a1))) (< (acl2-count (list a1)) (acl2-count x)))
  :rule-classes nil :hints (("Goal" :use xd-count-args :in-theory (disable xd-count-args))))

(defconst *xd-b* (+ 2 (so-kx) (sv-kx)))

(defmacro xa () '(kaddr x))

(defmacro xd-call-thy ()
  '(union-theories '(xd-count-args car-cons cdr-cons mv-nth-01-cons posp (kar) (eq) (equal) (member-equal) (acl2-count) (binary-+)
                     (:type-prescription acl2-count))
                   (theory 'minimal-theory)))

(defthm xd-call-obj
  (implies (and (xp-finds) (equal (kar x) :call) (equal (kadr x) "hpg_scan_obj")
                (not (mv-nth 0 (s-call-val-d (kadr x) (kaddr x) fr heap)))
                (integerp fuel) (< (+ *xd-b* (acl2-count x)) fuel))
           (equal (f-ex x fr heap procs fuel)
                  (mv :normal (mv-nth 1 (s-call-val-d (kadr x) (kaddr x) fr heap))
                      (mv-nth 2 (s-call-val-d (kadr x) (kaddr x) fr heap)))))
  :hints (("Goal" :do-not-induct t :in-theory (xd-call-thy)
           :expand ((f-ex x fr heap procs fuel))
           :use ((:instance xd-scv-obj (name (kadr x)) (a (xa)))
                 (:instance xd-count-3 (a0 (list :var (kadr (car (xa))))) (a1 (cadr (xa))) (a2 (caddr (xa))))
                 (:instance so-env-intro (key (mv-nth 1 (obj-of (kadr (car (xa))) fr))) (cm (cdr (lkp (mv-nth 1 (obj-of (kadr (car (xa))) fr)) heap)))
                            (hpg (hs-hpg (cdr (lkp (mv-nth 1 (obj-of (kadr (car (xa))) fr)) heap))))
                            (i (mv-nth 1 (sv (cadr (xa)) fr heap))) (k (mv-nth 1 (sv (caddr (xa)) fr heap))))
                 (:instance so-okc (ob (kadr (car (xa)))) (c1 (cadr (xa))) (c2 (caddr (xa))) (fuel (1- fuel))
                            (key (mv-nth 1 (obj-of (kadr (car (xa))) fr))) (cm (cdr (lkp (mv-nth 1 (obj-of (kadr (car (xa))) fr)) heap)))
                            (hpg (hs-hpg (cdr (lkp (mv-nth 1 (obj-of (kadr (car (xa))) fr)) heap))))
                            (i (mv-nth 1 (sv (cadr (xa)) fr heap))) (k (mv-nth 1 (sv (caddr (xa)) fr heap))))))))

(defthm xd-call-vec
  (implies (and (xp-finds) (equal (kar x) :call) (equal (kadr x) "hpg_scan_vec")
                (not (mv-nth 0 (s-call-val-d (kadr x) (kaddr x) fr heap)))
                (integerp fuel) (< (+ *xd-b* (acl2-count x)) fuel))
           (equal (f-ex x fr heap procs fuel)
                  (mv :normal (mv-nth 1 (s-call-val-d (kadr x) (kaddr x) fr heap))
                      (mv-nth 2 (s-call-val-d (kadr x) (kaddr x) fr heap)))))
  :hints (("Goal" :do-not-induct t :in-theory (xd-call-thy)
           :expand ((f-ex x fr heap procs fuel))
           :use ((:instance xd-scv-vec (name (kadr x)) (a (xa)))
                 (:instance xd-count-2 (a0 (list :var (kadr (car (xa))))) (a1 (cadr (xa))))
                 (:instance sv-env-intro (key (mv-nth 1 (obj-of (kadr (car (xa))) fr))) (cm (cdr (lkp (mv-nth 1 (obj-of (kadr (car (xa))) fr)) heap)))
                            (hpg (hs-hpg (cdr (lkp (mv-nth 1 (obj-of (kadr (car (xa))) fr)) heap))))
                            (i (mv-nth 1 (sv (cadr (xa)) fr heap))))
                 (:instance sv-okc (ob (kadr (car (xa)))) (c1 (cadr (xa))) (fuel (1- fuel))
                            (key (mv-nth 1 (obj-of (kadr (car (xa))) fr))) (cm (cdr (lkp (mv-nth 1 (obj-of (kadr (car (xa))) fr)) heap)))
                            (hpg (hs-hpg (cdr (lkp (mv-nth 1 (obj-of (kadr (car (xa))) fr)) heap))))
                            (i (mv-nth 1 (sv (cadr (xa)) fr heap))))))))

(defthm xd-call-ok
  (implies (and (xp-finds) (eq (kar x) :call) (not (mv-nth 0 (s-call-val-d (kadr x) (kaddr x) fr heap)))
                (integerp fuel) (< (+ *xd-b* (acl2-count x)) fuel))
           (equal (f-ex x fr heap procs fuel)
                  (mv :normal (mv-nth 1 (s-call-val-d (kadr x) (kaddr x) fr heap))
                      (mv-nth 2 (s-call-val-d (kadr x) (kaddr x) fr heap)))))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(eq xd-call-obj xd-call-vec) (theory 'minimal-theory))
           :use ((:instance xd-scv-name (name (kadr x)) (a (kaddr x)))))))

(defmacro xdw (k) `(mv-nth ,k (p-sorc-d-witness procs *xd-b*)))

(defthm p-sorc-d-holds
  (implies (xp-finds) (p-sorc-d procs *xd-b*))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(p-sorc-d) (theory 'minimal-theory))
           :use ((:instance xd-call-ok (x (xdw 0)) (fr (xdw 1)) (heap (xdw 2)) (fuel (xdw 3)))))))

; ---- the theorem: no hypothesis on the procedures past the ground xp-finds; the state facts xd-lens, nt-lens

(defthm hpg-drain-fortran-correct-x
  (implies (and (xp-finds)
                (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (int64p n)
                (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (dr-heap-at heap key comps hpg)
                (integerp fuel) (< (+ 9 (* (+ 1 (nfix n)) (dr-k *xd-b*))) fuel))
           (equal (f-invoke *dr-proc* (cons (list :var ob) (g-lits (list n))) caller heap procs fuel)
                  (mv nil caller (put key (hs-rep comps (hpg-drain n hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-invoke hpg-drain hpgp hpg-ok xd-lens nt-lens hs-rep dr-heap-at p-sorc-d-holds hpg-drain-fortran-correct)
           :use (p-sorc-d-holds (:instance hpg-drain-fortran-correct (b *xd-b*))))))
