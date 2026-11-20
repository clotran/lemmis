; gen-st-xdrain: p-sorc-d, part 2 (GEN.md "Left of 4c step 3" (ii)). hpg_scan_obj and
; hpg_scan_run (DO loops CALLing hpg_push, gen-st-xpush) and hpg_scan_vec (CALLs hpg_scan_run) run on
; hs's entry; their CALLs as hpg_drain writes them answer s-call-val-d (p-sorc-d-holds), so
; hpg-drain-fortran-correct-x needs nothing past the ground xp-finds and the state facts xd-lens, nt-lens.
; Recipe (gen-st-xtake's runs_fill): one lemma per statement, composed by :use with the f-ex
; rewriters disabled (rf-c-thy), the DO by induction on its bound.

(in-package "ACL2")

(include-book "gen-st-xpush")

(in-theory (disable xd-lens))

(defthm nt-lens-oref (implies (nt-lens h) (equal (len (nth *h-orefi* h)) (len (nth *h-otagi* h)))))
(defthm xd-lens-arena
  (implies (xd-lens h) (and (equal (len (nth *h-atagi* h)) (len (nth *h-aivali* h))) (equal (len (nth *h-arefi* h)) (len (nth *h-aivali* h)))
                            (equal (len (nth *h-vleni* h)) (len (nth *h-vmarki* h))) (equal (len (nth *h-voffi* h)) (len (nth *h-vmarki* h)))))
  :hints (("Goal" :in-theory (enable xd-lens))))
(in-theory (disable xd-lens-arena))

; ---- hpg_scan_obj: one iteration on the ACL2 side

(defmacro so-j () '(+ (* 5 i) k))
(defun-nx so-go (i k hpg) (and (natp k) (< k 5) (< (so-j) (len (nth *h-otagi* hpg))) (< (so-j) (len (nth *h-orefi* hpg)))))
(defun-nx so-next (i k hpg) (hpg-push (nth (so-j) (nth *h-otagi* hpg)) (nth (so-j) (nth *h-orefi* hpg)) hpg))

(defthm so-step
  (implies (so-go i k hpg) (equal (hpg-scan-obj i k hpg) (hpg-scan-obj i (+ 1 k) (so-next i k hpg))))
  :hints (("Goal" :in-theory (enable so-go so-next h-otagi h-orefi h-otag-length h-oref-length) :expand ((hpg-scan-obj i k hpg)))))

(defthm so-stop
  (implies (not (so-go i k hpg)) (equal (hpg-scan-obj i k hpg) hpg))
  :hints (("Goal" :in-theory (enable so-go h-otag-length h-oref-length) :expand ((hpg-scan-obj i k hpg)))))

(defthm so-next-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (natp i) (so-go i k hpg))
           (and (hpgp (so-next i k hpg)) (hpg-ok (so-next i k hpg)) (xd-lens (so-next i k hpg)) (nt-lens (so-next i k hpg))))
  :hints (("Goal" :in-theory (e/d (so-go so-next) (hpgp hpg-ok hpg-push nt-lens)))))

(defthm so-go-k (implies (so-go i k hpg) (and (natp k) (< k 5))) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable so-go))))

(in-theory (disable so-go so-next))

; ---- one iteration, symbolically on f-ex

(defconst *so-ls* (nth 4 *so-proc*))
(defconst *so-body* (nth 5 *so-proc*))
(defconst *so-b* (cadr (car *so-body*)))

(defthm so-proc-shape
  (and (equal *so-proc* (list :subroutine "hpg_scan_obj" (nth 2 *so-proc*)
                              (cons (list "hs" :inout "heap_state") (g-dummies '(i k))) *so-ls* *so-body*))
       (equal *so-body* (list (list :do *so-b*))))
  :rule-classes nil)

(defconst *so-s1* (nth 0 *so-b*))
(defconst *so-s2* (nth 1 *so-b*))
(defconst *so-e* (nth 3 *so-s2*))
(defconst *so-f* (nth 2 (nth 2 *so-e*)))
(assert-event (and (equal (len *so-b*) 3) (equal (nth 2 *so-b*) '(:exit)) (equal (nth 2 *so-s2*) nil)
                   (equal (len *so-e*) 3) (equal (nth 3 (nth 2 *so-e*)) nil)))

(defmacro so-fr (fr) `(and (dr-frp ,fr *so-ls*) (dr-hs-at ,fr key) (rf-v-at ,fr "i_" i) (rf-v-at ,fr "k_" k)))
; the frame-free hypotheses, closed so a :use'd lemma's do not split the goal
(defun-nx so-env (procs heap key cm hpg i k)
  (and (xp-finds) (natp i) (< i *hb40*) (natp k) (<= k 5)
       (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (dr-heap-at heap key cm hpg)))
(defmacro so-hyps () '(and (so-env procs heap key cm hpg i k) (so-fr fr)))

(defthm so-env-heap (implies (so-env procs heap key cm hpg i k) (and (dr-heap-at heap key cm hpg) (natp k) (<= k 5)))
  :rule-classes :forward-chaining)
(defthm so-env-next
  (implies (and (so-env procs heap key cm hpg i k) (so-go i k hpg))
           (so-env procs (put key (hs-rep cm (so-next i k hpg)) heap) key cm (so-next i k hpg) i (+ 1 k)))
  :hints (("Goal" :in-theory (e/d (dr-heap-at-put) (hpgp hpg-ok xd-lens nt-lens dr-heap-at hs-rep put)))))
(in-theory (disable so-env))
(defmacro so-kb () '(+ 400 (acl2-count *so-b*)))

(defmacro so-iter-thy (&rest en)
  `(e/d (so-env obj-of int64p ext-op ext-read-p ext-write-p ext-dums ,@en)
        (f-ev f-bind f-ex hs-rep hpgp hpg-ok xd-lens nt-lens dr-heap-at hpg-push hpg-scan-obj)))

(make-event
 `(defthm so-s1
    (implies (and (so-hyps) (integerp fu) (< 40 fu))
             (let ((r (f-ex *so-s1* fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (so-fr (mv-nth 1 r))
                    (equal (lkp "t_1" (mv-nth 1 r)) (list* "t_1" :logical (not (< k 5)))))))
    :hints (("Goal" :do-not-induct t :in-theory (so-iter-thy)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *so-proc*)))))))

(make-event
 `(defthm so-e1
    (implies (and (so-hyps) (< k 5) (integerp fu) (< 40 fu))
             (let ((r (f-ex (nth 0 *so-e*) fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (so-fr (mv-nth 1 r))
                    (rf-v-at (mv-nth 1 r) "j_2" (so-j)))))
    :hints (("Goal" :do-not-induct t :in-theory (so-iter-thy)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *so-proc*)))))))

(make-event
 `(defthm so-e2
    (implies (and (so-hyps) (< k 5) (rf-v-at fr "j_2" (so-j)) (integerp fu) (< 40 fu))
             (let ((r (f-ex (nth 1 *so-e*) fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (so-fr (mv-nth 1 r))
                    (rf-v-at (mv-nth 1 r) "j_2" (so-j))
                    (equal (lkp "t_3" (mv-nth 1 r)) (list* "t_3" :logical (< (so-j) (len (nth *h-otagi* hpg))))))))
    :hints (("Goal" :do-not-induct t :in-theory (so-iter-thy)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *so-proc*)))))))

(make-event
 `(defthm so-f
    (implies (and (so-hyps) (so-go i k hpg) (rf-v-at fr "j_2" (so-j)) (integerp fu) (< 400 fu))
             (let ((r (f-ex-list *so-f* fr heap procs fu)))
               (and (equal (car r) :cycle)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (so-next i k hpg)) heap))
                    (dr-frp (mv-nth 1 r) *so-ls*) (dr-hs-at (mv-nth 1 r) key)
                    (rf-v-at (mv-nth 1 r) "i_" i) (rf-v-at (mv-nth 1 r) "k_" (+ 1 k)))))
    :hints (("Goal" :do-not-induct t :in-theory (so-iter-thy so-go so-next xd-ex-ps-obj)
             :expand ((:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *so-proc*)))))))

(defmacro so-c-thy (&rest en)
  `(union-theories (set-difference-theories (rf-c-thy)
                                            '(so-s1 so-e1 so-e2 so-f xd-ex-ps-obj hpg-scan-obj hpg-push xd-lens nt-lens hpg-ok
                                              so-go so-next ps-run ps-ok sp-run sp-ok))
                   ',en))

(defmacro so-tail (r)
  `(and (equal (car ,r) (if (so-go i k hpg) :cycle :normal))
        (equal (mv-nth 2 ,r) (if (so-go i k hpg) (put key (hs-rep cm (so-next i k hpg)) heap) heap))
        (implies (so-go i k hpg)
                 (and (dr-frp (mv-nth 1 ,r) *so-ls*) (dr-hs-at (mv-nth 1 ,r) key)
                      (rf-v-at (mv-nth 1 ,r) "i_" i) (rf-v-at (mv-nth 1 ,r) "k_" (+ 1 k))))))

(make-event
 `(defthm so-t3
    (implies (and (so-hyps) (< k 5) (rf-v-at fr "j_2" (so-j))
                  (equal (lkp "t_3" fr) (list* "t_3" :logical (< (so-j) (len (nth *h-otagi* hpg)))))
                  (integerp fu) (< 410 fu))
             (so-tail (f-ex-list (cddr *so-e*) fr heap procs fu)))
    :hints (("Goal" :do-not-induct t :in-theory (so-c-thy so-go nt-lens-oref so-env)
             :use ((:instance so-f (fu (- fu 2))))
             :expand ((f-ex-list ',(cddr *so-e*) fr heap procs fu)
                      (f-ex ',(nth 2 *so-e*) fr heap procs (- fu 1))
                      (:free (fr h k) (f-ex-list nil fr h procs k))
                      (:free (fr h k) (f-ev '(:var "t_3") fr h procs k)))))))

(make-event
 `(defthm so-t2
    (implies (and (so-hyps) (< k 5) (rf-v-at fr "j_2" (so-j)) (integerp fu) (< 420 fu))
             (so-tail (f-ex-list (cdr *so-e*) fr heap procs fu)))
    :hints (("Goal" :do-not-induct t :in-theory (so-c-thy)
             :expand ((f-ex-list ',(cdr *so-e*) fr heap procs fu))
             :use ((:instance so-e2 (fu (- fu 1)))
                   (:instance so-t3 (fr (mv-nth 1 (f-ex (nth 1 *so-e*) fr heap procs (- fu 1)))) (fu (- fu 1))))))))

(make-event
 `(defthm so-t1
    (implies (and (so-hyps) (< k 5) (integerp fu) (< 430 fu))
             (so-tail (f-ex-list *so-e* fr heap procs fu)))
    :hints (("Goal" :do-not-induct t :in-theory (so-c-thy)
             :expand ((f-ex-list ',*so-e* fr heap procs fu))
             :use ((:instance so-e1 (fu (- fu 1)))
                   (:instance so-t2 (fr (mv-nth 1 (f-ex (nth 0 *so-e*) fr heap procs (- fu 1)))) (fu (- fu 1))))))))

(defun so-c-expands ()
  (declare (xargs :mode :program))
  `((f-ex-list ',*so-b* fr heap procs fu) (:free (fr h) (f-ex-list ',(cdr *so-b*) fr h procs (- fu 1)))
    (:free (fr h) (f-ex ',*so-s2* fr h procs (- fu 2)))
    (:free (fr h) (f-ev '(:var "t_1") fr h procs (- fu 3)))
    (:free (fr h) (f-ex-list ',(cddr *so-b*) fr h procs (- fu 2)))
    (:free (fr h) (f-ex '(:exit) fr h procs (- fu 3)))
    (:free (fr h k) (f-ex-list nil fr h procs k))))

(make-event
 `(defthm so-iter-exit
    (implies (and (so-hyps) (not (so-go i k hpg)) (integerp fu) (< (so-kb) fu))
             (let ((r (f-ex-list *so-b* fr heap procs fu)))
               (and (equal (mv-nth 0 r) :exit) (equal (mv-nth 2 r) heap))))
    :hints (("Goal" :do-not-induct t :in-theory (so-c-thy)
             :use ((:instance so-s1 (fu (- fu 1)))
                   (:instance so-t1 (fr (mv-nth 1 (f-ex *so-s1* fr heap procs (- fu 1)))) (fu (- fu 3))))
             :expand ,(so-c-expands)))))

(make-event
 `(defthm so-iter-cycle
    (implies (and (so-hyps) (so-go i k hpg) (integerp fu) (< (so-kb) fu))
             (let ((r (f-ex-list *so-b* fr heap procs fu)))
               (and (equal (mv-nth 0 r) :cycle)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (so-next i k hpg)) heap))
                    (dr-frp (mv-nth 1 r) *so-ls*) (dr-hs-at (mv-nth 1 r) key)
                    (rf-v-at (mv-nth 1 r) "i_" i) (rf-v-at (mv-nth 1 r) "k_" (+ 1 k)))))
    :hints (("Goal" :do-not-induct t :in-theory (so-c-thy so-go-k)
             :use ((:instance so-s1 (fu (- fu 1)))
                   (:instance so-t1 (fr (mv-nth 1 (f-ex *so-s1* fr heap procs (- fu 1)))) (fu (- fu 3))))
             :expand ,(so-c-expands)))))

; ---- the DO, by induction on 5-k

(defmacro so-k () '(+ (so-kb) 2 (- 5 k)))

(defun-nx so-ind (i k hpg fr heap procs fu key cm)
  (declare (xargs :measure (nfix (- 5 k)) :hints (("Goal" :in-theory (enable so-go)))))
  (if (or (not (so-go i k hpg)) (zp fu)) (list fr heap)
    (so-ind i (+ 1 k) (so-next i k hpg) (mv-nth 1 (f-ex-list *so-b* fr heap procs (1- fu)))
            (put key (hs-rep cm (so-next i k hpg)) heap) procs (1- fu) key cm)))

(defthm so-loop
  (implies (and (so-hyps) (integerp fu) (< (so-k) fu))
           (and (equal (mv-nth 0 (f-ex (list :do *so-b*) fr heap procs fu)) :normal)
                (equal (mv-nth 2 (f-ex (list :do *so-b*) fr heap procs fu)) (put key (hs-rep cm (hpg-scan-obj i k hpg)) heap))))
  :hints (("Goal" :induct (so-ind i k hpg fr heap procs fu key cm) :do-not-induct t
           :in-theory (so-c-thy f-ex-do-cycle f-ex-do-exit2 so-iter-exit so-iter-cycle so-step so-stop so-go-k
                                so-env-next so-env-heap xd-put-same))))

; ---- hpg_scan_obj's invocation, and its CALL from any frame on argument codes

(defmacro so-frame () '(undef-locals *so-ls* (fb '(i k) (list i k) (put "hs" (list* :obj :inout key) nil))))

(defthm so-frame-hyps
  (so-fr (so-frame))
  :hints (("Goal" :in-theory (enable fb dr-hs-at rf-v-at))))

(defthm so-body-run
  (implies (and (so-env procs heap key cm hpg i k) (integerp fu) (< (+ 2 (so-k)) fu))
           (and (equal (mv-nth 0 (f-ex-list *so-body* (so-frame) heap procs fu)) :normal)
                (equal (mv-nth 2 (f-ex-list *so-body* (so-frame) heap procs fu)) (put key (hs-rep cm (hpg-scan-obj i k hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-ex f-ex-list so-loop dr-frp undef-locals fb hpgp hpg-ok hs-rep int64p put hpg-scan-obj so-env)
           :expand ((f-ex-list *so-body* (so-frame) heap procs fu)
                    (:free (fr h) (f-ex-list nil fr h procs (+ -1 fu))))
           :use ((:instance so-loop (fr (so-frame)) (fu (1- fu)))))))

(defmacro so-kx () '(+ 20 (so-kb)))

(defthm so-env-int (implies (so-env procs heap key cm hpg i k) (int64-listp (list i k)))
  :rule-classes nil :hints (("Goal" :in-theory (enable so-env int64p))))

(defthm so-ok
  (implies (and (so-env procs heap key cm hpg i k) (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (integerp fuel) (< (so-kx) fuel))
           (equal (f-invoke *so-proc* (cons (list :var ob) (g-lits (list i k))) caller heap procs fuel)
                  (mv nil caller (put key (hs-rep cm (hpg-scan-obj i k hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(natp len car-cons cdr-cons (len) (g-dummies) (nth) (cons) (equal) (acl2-count) (binary-+) (unary--))
                                      (theory 'minimal-theory))
           :use (so-proc-shape so-env-int so-env-heap
                 (:instance so-body-run (fu (1- fuel)))
                 (:instance f-invoke-sub-d (ks (list i k)) (vs '(i k)) (o "hs") (c "heap_state") (nm "hpg_scan_obj")
                            (rec (nth 2 *so-proc*)) (ls *so-ls*) (body *so-body*))))))

(defthm so-okc
  (implies (and (so-env procs heap key cm hpg i k) (equal (cdr (lkp ob fr)) (list* :obj :inout key))
                (not (mv-nth 0 (sv c1 fr heap))) (equal (mv-nth 1 (sv c1 fr heap)) i)
                (not (mv-nth 0 (sv c2 fr heap))) (equal (mv-nth 1 (sv c2 fr heap)) k)
                (integerp fuel) (< (+ (so-kx) (acl2-count (list c1 c2))) fuel))
           (equal (f-invoke *so-proc* (list (list :var ob) c1 c2) fr heap procs fuel)
                  (mv nil fr (put key (hs-rep cm (hpg-scan-obj i k hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(len (len) (g-dummies) (kar) (nth) (true-list-fix) (equal) car-cons cdr-cons
                                        (:type-prescription acl2-count))
                                      (theory 'minimal-theory))
           :use (so-proc-shape so-env-int
                 (:instance svs-is-2 (x1 c1) (x2 c2))
                 (:instance f-invoke-st-codes (p *so-proc*) (d '("hs" :inout "heap_state")) (vs '(i k))
                            (a (list :var ob)) (cs (list c1 c2)) (ks (list i k)) (caller fr))
                 (:instance so-ok (caller fr))))))

(defthm xd-ex-so
  (implies (and (equal (find-proc "hpg_scan_obj" procs) *so-proc*)
                (so-env procs heap key cm hpg i k) (equal (cdr (lkp ob fr)) (list* :obj :inout key))
                (not (mv-nth 0 (sv c1 fr heap))) (equal (mv-nth 1 (sv c1 fr heap)) i)
                (not (mv-nth 0 (sv c2 fr heap))) (equal (mv-nth 1 (sv c2 fr heap)) k)
                (integerp fuel) (< (+ 1 (so-kx) (acl2-count (list c1 c2))) fuel))
           (equal (f-ex (list :call "hpg_scan_obj" (list (list :var ob) c1 c2)) fr heap procs fuel)
                  (mv :normal fr (put key (hs-rep cm (hpg-scan-obj i k hpg)) heap))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable f-invoke so-okc so-env sv hs-rep put hpg-scan-obj)
           :expand ((f-ex (list :call "hpg_scan_obj" (list (list :var ob) c1 c2)) fr heap procs fuel))
           :use ((:instance so-okc (fuel (1- fuel)))))))

; ---- hpg_scan_run (the arena words j..e-1), the same way: the ACL2 side

(defun-nx sr-go (j e hpg) (and (natp j) (natp e) (< j e) (< j (len (nth *h-atagi* hpg))) (< j (len (nth *h-arefi* hpg)))))
(defun-nx sr-next (j hpg) (hpg-push (nth j (nth *h-atagi* hpg)) (nth j (nth *h-arefi* hpg)) hpg))

(defthm sr-step
  (implies (sr-go j e hpg) (equal (hpg-scan-run j e hpg) (hpg-scan-run (+ 1 j) e (sr-next j hpg))))
  :hints (("Goal" :in-theory (enable sr-go sr-next h-atagi h-arefi h-atag-length h-aref-length) :expand ((hpg-scan-run j e hpg)))))

(defthm sr-stop
  (implies (not (sr-go j e hpg)) (equal (hpg-scan-run j e hpg) hpg))
  :hints (("Goal" :in-theory (enable sr-go h-atag-length h-aref-length) :expand ((hpg-scan-run j e hpg)))))

(defthm sr-next-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (sr-go j e hpg))
           (and (hpgp (sr-next j hpg)) (hpg-ok (sr-next j hpg)) (xd-lens (sr-next j hpg)) (nt-lens (sr-next j hpg))))
  :hints (("Goal" :in-theory (e/d (sr-go sr-next) (hpgp hpg-ok hpg-push nt-lens)))))

(defthm sr-go-j (implies (sr-go j e hpg) (and (natp j) (natp e) (< j e))) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable sr-go))))

(in-theory (disable sr-go sr-next))

(defun-nx sr-env (procs heap key cm hpg j e)
  (and (xp-finds) (natp j) (<= j *hb40*) (natp e) (<= e *hb40*)
       (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (dr-heap-at heap key cm hpg)))
(defthm sr-env-heap
  (implies (sr-env procs heap key cm hpg j e) (and (dr-heap-at heap key cm hpg) (natp j) (<= j *hb40*) (natp e) (<= e *hb40*)))
  :rule-classes :forward-chaining)
(defthm sr-env-next
  (implies (and (sr-env procs heap key cm hpg j e) (sr-go j e hpg))
           (sr-env procs (put key (hs-rep cm (sr-next j hpg)) heap) key cm (sr-next j hpg) (+ 1 j) e))
  :hints (("Goal" :in-theory (e/d (dr-heap-at-put) (hpgp hpg-ok xd-lens nt-lens dr-heap-at hs-rep put)))))
(in-theory (disable sr-env))

; ---- one iteration, symbolically

(defconst *sr-ls* (nth 4 *sr-proc*))
(defconst *sr-body* (nth 5 *sr-proc*))
(defconst *sr-b* (cadr (car *sr-body*)))

(defthm sr-proc-shape
  (and (equal *sr-proc* (list :subroutine "hpg_scan_run" (nth 2 *sr-proc*)
                              (cons (list "hs" :inout "heap_state") (g-dummies '(j e))) *sr-ls* *sr-body*))
       (equal *sr-body* (list (list :do *sr-b*))))
  :rule-classes nil)

(defconst *sr-s1* (nth 0 *sr-b*))
(defconst *sr-s2* (nth 1 *sr-b*))
(defconst *sr-e* (nth 3 *sr-s2*))
(defconst *sr-f* (nth 2 (nth 1 *sr-e*)))
(assert-event (and (equal (len *sr-b*) 3) (equal (nth 2 *sr-b*) '(:exit)) (equal (nth 2 *sr-s2*) nil)
                   (equal (len *sr-e*) 2) (equal (nth 3 (nth 1 *sr-e*)) nil)))

(defmacro sr-fr (fr) `(and (dr-frp ,fr *sr-ls*) (dr-hs-at ,fr key) (rf-v-at ,fr "j_" j) (rf-v-at ,fr "e_" e)))
(defmacro sr-hyps () '(and (sr-env procs heap key cm hpg j e) (sr-fr fr)))
(defmacro sr-kb () '(+ 400 (acl2-count *sr-b*)))

(defmacro sr-iter-thy (&rest en)
  `(e/d (sr-env obj-of int64p ext-op ext-read-p ext-write-p ext-dums ,@en)
        (f-ev f-bind f-ex hs-rep hpgp hpg-ok xd-lens nt-lens dr-heap-at hpg-push hpg-scan-run)))

(make-event
 `(defthm sr-s1
    (implies (and (sr-hyps) (integerp fu) (< 40 fu))
             (let ((r (f-ex *sr-s1* fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (sr-fr (mv-nth 1 r))
                    (equal (lkp "t_2" (mv-nth 1 r)) (list* "t_2" :logical (not (< j e)))))))
    :hints (("Goal" :do-not-induct t :in-theory (sr-iter-thy)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *sr-proc*)))))))

(make-event
 `(defthm sr-e1
    (implies (and (sr-hyps) (< j e) (integerp fu) (< 40 fu))
             (let ((r (f-ex (nth 0 *sr-e*) fr heap procs fu)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (sr-fr (mv-nth 1 r))
                    (equal (lkp "t_3" (mv-nth 1 r)) (list* "t_3" :logical (< j (len (nth *h-aivali* hpg))))))))
    :hints (("Goal" :do-not-induct t :in-theory (sr-iter-thy)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *sr-proc*)))))))

(make-event
 `(defthm sr-f
    (implies (and (sr-hyps) (sr-go j e hpg) (integerp fu) (< 400 fu))
             (let ((r (f-ex-list *sr-f* fr heap procs fu)))
               (and (equal (car r) :cycle)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (sr-next j hpg)) heap))
                    (dr-frp (mv-nth 1 r) *sr-ls*) (dr-hs-at (mv-nth 1 r) key)
                    (rf-v-at (mv-nth 1 r) "j_" (+ 1 j)) (rf-v-at (mv-nth 1 r) "e_" e))))
    :hints (("Goal" :do-not-induct t :in-theory (sr-iter-thy sr-go sr-next xd-ex-ps-run)
             :expand ((:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *sr-proc*)))))))

(defmacro sr-c-thy (&rest en)
  `(union-theories (set-difference-theories (rf-c-thy)
                                            '(sr-s1 sr-e1 sr-f xd-ex-ps-run so-s1 so-e1 so-e2 so-f xd-ex-ps-obj hpg-scan-obj hpg-scan-run
                                              hpg-push xd-lens nt-lens hpg-ok sr-go sr-next ps-run ps-ok sp-run sp-ok))
                   ',en))

(defmacro sr-tail (r)
  `(and (equal (car ,r) (if (sr-go j e hpg) :cycle :normal))
        (equal (mv-nth 2 ,r) (if (sr-go j e hpg) (put key (hs-rep cm (sr-next j hpg)) heap) heap))
        (implies (sr-go j e hpg)
                 (and (dr-frp (mv-nth 1 ,r) *sr-ls*) (dr-hs-at (mv-nth 1 ,r) key)
                      (rf-v-at (mv-nth 1 ,r) "j_" (+ 1 j)) (rf-v-at (mv-nth 1 ,r) "e_" e)))))

(make-event
 `(defthm sr-t2
    (implies (and (sr-hyps) (< j e)
                  (equal (lkp "t_3" fr) (list* "t_3" :logical (< j (len (nth *h-aivali* hpg)))))
                  (integerp fu) (< 410 fu))
             (sr-tail (f-ex-list (cdr *sr-e*) fr heap procs fu)))
    :hints (("Goal" :do-not-induct t :in-theory (sr-c-thy sr-go xd-lens-arena sr-env)
             :use ((:instance sr-f (fu (- fu 2))))
             :expand ((f-ex-list ',(cdr *sr-e*) fr heap procs fu)
                      (f-ex ',(nth 1 *sr-e*) fr heap procs (- fu 1))
                      (:free (fr h k) (f-ex-list nil fr h procs k))
                      (:free (fr h k) (f-ev '(:var "t_3") fr h procs k)))))))

(make-event
 `(defthm sr-t1
    (implies (and (sr-hyps) (< j e) (integerp fu) (< 420 fu))
             (sr-tail (f-ex-list *sr-e* fr heap procs fu)))
    :hints (("Goal" :do-not-induct t :in-theory (sr-c-thy)
             :expand ((f-ex-list ',*sr-e* fr heap procs fu))
             :use ((:instance sr-e1 (fu (- fu 1)))
                   (:instance sr-t2 (fr (mv-nth 1 (f-ex (nth 0 *sr-e*) fr heap procs (- fu 1)))) (fu (- fu 1))))))))

(defun sr-c-expands ()
  (declare (xargs :mode :program))
  `((f-ex-list ',*sr-b* fr heap procs fu) (:free (fr h) (f-ex-list ',(cdr *sr-b*) fr h procs (- fu 1)))
    (:free (fr h) (f-ex ',*sr-s2* fr h procs (- fu 2)))
    (:free (fr h) (f-ev '(:var "t_2") fr h procs (- fu 3)))
    (:free (fr h) (f-ex-list ',(cddr *sr-b*) fr h procs (- fu 2)))
    (:free (fr h) (f-ex '(:exit) fr h procs (- fu 3)))
    (:free (fr h k) (f-ex-list nil fr h procs k))))

(make-event
 `(defthm sr-iter-exit
    (implies (and (sr-hyps) (not (sr-go j e hpg)) (integerp fu) (< (sr-kb) fu))
             (let ((r (f-ex-list *sr-b* fr heap procs fu)))
               (and (equal (mv-nth 0 r) :exit) (equal (mv-nth 2 r) heap))))
    :hints (("Goal" :do-not-induct t :in-theory (sr-c-thy)
             :use ((:instance sr-s1 (fu (- fu 1)))
                   (:instance sr-t1 (fr (mv-nth 1 (f-ex *sr-s1* fr heap procs (- fu 1)))) (fu (- fu 3))))
             :expand ,(sr-c-expands)))))

(make-event
 `(defthm sr-iter-cycle
    (implies (and (sr-hyps) (sr-go j e hpg) (integerp fu) (< (sr-kb) fu))
             (let ((r (f-ex-list *sr-b* fr heap procs fu)))
               (and (equal (mv-nth 0 r) :cycle)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (sr-next j hpg)) heap))
                    (dr-frp (mv-nth 1 r) *sr-ls*) (dr-hs-at (mv-nth 1 r) key)
                    (rf-v-at (mv-nth 1 r) "j_" (+ 1 j)) (rf-v-at (mv-nth 1 r) "e_" e))))
    :hints (("Goal" :do-not-induct t :in-theory (sr-c-thy sr-go-j)
             :use ((:instance sr-s1 (fu (- fu 1)))
                   (:instance sr-t1 (fr (mv-nth 1 (f-ex *sr-s1* fr heap procs (- fu 1)))) (fu (- fu 3))))
             :expand ,(sr-c-expands)))))

; ---- the DO, by induction on e-j

(defmacro sr-k () '(+ (sr-kb) 2 (nfix (- e j))))

(defun-nx sr-ind (j e hpg fr heap procs fu key cm)
  (declare (xargs :measure (nfix (- e j)) :hints (("Goal" :in-theory (enable sr-go)))))
  (if (or (not (sr-go j e hpg)) (zp fu)) (list fr heap)
    (sr-ind (+ 1 j) e (sr-next j hpg) (mv-nth 1 (f-ex-list *sr-b* fr heap procs (1- fu)))
            (put key (hs-rep cm (sr-next j hpg)) heap) procs (1- fu) key cm)))

(defthm sr-loop
  (implies (and (sr-hyps) (integerp fu) (< (sr-k) fu))
           (and (equal (mv-nth 0 (f-ex (list :do *sr-b*) fr heap procs fu)) :normal)
                (equal (mv-nth 2 (f-ex (list :do *sr-b*) fr heap procs fu)) (put key (hs-rep cm (hpg-scan-run j e hpg)) heap))))
  :hints (("Goal" :induct (sr-ind j e hpg fr heap procs fu key cm) :do-not-induct t
           :in-theory (sr-c-thy f-ex-do-cycle f-ex-do-exit2 sr-iter-exit sr-iter-cycle sr-step sr-stop sr-go-j
                                sr-env-next sr-env-heap xd-put-same))))

; ---- hpg_scan_run's invocation, and its CALL on argument codes

(defmacro sr-frame () '(undef-locals *sr-ls* (fb '(j e) (list j e) (put "hs" (list* :obj :inout key) nil))))

(defthm sr-frame-hyps
  (sr-fr (sr-frame))
  :hints (("Goal" :in-theory (enable fb dr-hs-at rf-v-at))))

(defthm sr-body-run
  (implies (and (sr-env procs heap key cm hpg j e) (integerp fu) (< (+ 2 (sr-k)) fu))
           (and (equal (mv-nth 0 (f-ex-list *sr-body* (sr-frame) heap procs fu)) :normal)
                (equal (mv-nth 2 (f-ex-list *sr-body* (sr-frame) heap procs fu)) (put key (hs-rep cm (hpg-scan-run j e hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-ex f-ex-list sr-loop dr-frp undef-locals fb hpgp hpg-ok hs-rep int64p put hpg-scan-run sr-env)
           :expand ((f-ex-list *sr-body* (sr-frame) heap procs fu)
                    (:free (fr h) (f-ex-list nil fr h procs (+ -1 fu))))
           :use ((:instance sr-loop (fr (sr-frame)) (fu (1- fu)))))))

(defmacro sr-kx () '(+ 20 (sr-kb) *hb40*))

(defthm sr-env-int (implies (sr-env procs heap key cm hpg j e) (int64-listp (list j e)))
  :rule-classes nil :hints (("Goal" :in-theory (enable sr-env int64p))))

(defthm sr-ok
  (implies (and (sr-env procs heap key cm hpg j e) (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (integerp fuel) (< (sr-kx) fuel))
           (equal (f-invoke *sr-proc* (cons (list :var ob) (g-lits (list j e))) caller heap procs fuel)
                  (mv nil caller (put key (hs-rep cm (hpg-scan-run j e hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(natp nfix len car-cons cdr-cons (len) (g-dummies) (nth) (cons) (equal) (acl2-count) (binary-+) (unary--))
                                      (theory 'minimal-theory))
           :use (sr-proc-shape sr-env-int sr-env-heap
                 (:instance sr-body-run (fu (1- fuel)))
                 (:instance f-invoke-sub-d (ks (list j e)) (vs '(j e)) (o "hs") (c "heap_state") (nm "hpg_scan_run")
                            (rec (nth 2 *sr-proc*)) (ls *sr-ls*) (body *sr-body*))))))

(defthm sr-okc
  (implies (and (sr-env procs heap key cm hpg j e) (equal (cdr (lkp ob fr)) (list* :obj :inout key))
                (not (mv-nth 0 (sv c1 fr heap))) (equal (mv-nth 1 (sv c1 fr heap)) j)
                (not (mv-nth 0 (sv c2 fr heap))) (equal (mv-nth 1 (sv c2 fr heap)) e)
                (integerp fuel) (< (+ (sr-kx) (acl2-count (list c1 c2))) fuel))
           (equal (f-invoke *sr-proc* (list (list :var ob) c1 c2) fr heap procs fuel)
                  (mv nil fr (put key (hs-rep cm (hpg-scan-run j e hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(len (len) (g-dummies) (kar) (nth) (true-list-fix) (equal) car-cons cdr-cons
                                        (:type-prescription acl2-count))
                                      (theory 'minimal-theory))
           :use (sr-proc-shape sr-env-int
                 (:instance svs-is-2 (x1 c1) (x2 c2))
                 (:instance f-invoke-st-codes (p *sr-proc*) (d '("hs" :inout "heap_state")) (vs '(j e))
                            (a (list :var ob)) (cs (list c1 c2)) (ks (list j e)) (caller fr))
                 (:instance sr-ok (caller fr))))))

(defthm xd-ex-sr
  (implies (and (equal (find-proc "hpg_scan_run" procs) *sr-proc*)
                (sr-env procs heap key cm hpg j e) (equal (cdr (lkp ob fr)) (list* :obj :inout key))
                (not (mv-nth 0 (sv c1 fr heap))) (equal (mv-nth 1 (sv c1 fr heap)) j)
                (not (mv-nth 0 (sv c2 fr heap))) (equal (mv-nth 1 (sv c2 fr heap)) e)
                (integerp fuel) (< (+ 1 (sr-kx) (acl2-count (list c1 c2))) fuel))
           (equal (f-ex (list :call "hpg_scan_run" (list (list :var ob) c1 c2)) fr heap procs fuel)
                  (mv :normal fr (put key (hs-rep cm (hpg-scan-run j e hpg)) heap))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable f-invoke sr-okc sr-env sv hs-rep put hpg-scan-run)
           :expand ((f-ex (list :call "hpg_scan_run" (list (list :var ob) c1 c2)) fr heap procs fuel))
           :use ((:instance sr-okc (fuel (1- fuel)))))))
