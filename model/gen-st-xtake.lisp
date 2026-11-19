; gen-st-xtake: p-sorc-t discharged (GEN.md "What remains" 4c, step 3).
; hpg_run_take_c CALLs hpg_runs_fill (a tail DO loop CALLing hpg_run_new and
; hpg_run_push), hpg_run_from_batch and hpg_run_new; all are g-st-module's
; output (gen-st-heap's *heapg-xmod*). hpg_run_push is run symbolically on
; hs's entry as gen-st-xrfb's callees are; hpg_runs_fill's DO by induction on
; the fuel (as gen-st-drain's), one iteration run on f-ex directly; then
; hpg_run_take_c's body. p-sorc-t holds of any procs holding these
; procedures, gen-st-xrfb's and the externs (`xt-finds`), and
; hpg-run-take is correct with no hypothesis on the procedures past that and
; the ground rt-finds (`hpg-run-take-fortran-correct-x`).

(in-package "ACL2")

(include-book "gen-st-xrfb")
(include-book "gen-st-take")

; ---- the ACL2 side: run-new, run-push and runs-fill keep hpgp and hpg-rn-ok

(in-theory (enable h-cheadp h-aivalp h-rbp))
(hsb64-elems h-cheadp) (hsb64-update h-cheadp) (hsb64-elems h-aivalp) (hsb64-update h-rbp)
(in-theory (disable h-cheadp h-aivalp h-rbp))

(defthm hpg-run-new-ok
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*))
           (and (hpgp (mv-nth 1 (hpg-run-new c l hpg))) (hpg-rn-ok (mv-nth 1 (hpg-run-new c l hpg)))
                (natp (mv-nth 0 (hpg-run-new c l hpg))) (<= (mv-nth 0 (hpg-run-new c l hpg)) *hb40*)))
  :hints (("Goal" :in-theory (e/d (hpg-run-new hpgp hpg-rn-ok hpg-al-ok hpg-sw-ok hpg-ok hpg-lens hpg-s64)
                                  (nth update-nth)))))

(defthm hpg-run-new-keeps
  (and (equal (nth *h-nrbi* (mv-nth 1 (hpg-run-new c l hpg))) (nth *h-nrbi* hpg))
       (equal (nth *h-rbi* (mv-nth 1 (hpg-run-new c l hpg))) (nth *h-rbi* hpg)))
  :hints (("Goal" :in-theory (enable hpg-run-new))))

(defthm hpg-run-push-ok
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c) (<= 1 c) (< c (len (nth *h-nrbi* hpg))) (natp n) (< n *run-batch*)
                (< (rb-at c (+ 1 n)) (len (nth *h-rbi* hpg))) (natp off) (<= off *hb40*))
           (and (hpgp (hpg-run-push c n off hpg)) (hpg-rn-ok (hpg-run-push c n off hpg))))
  :hints (("Goal" :in-theory (e/d (hpgp hpg-rn-ok hpg-al-ok hpg-sw-ok hpg-ok hpg-lens) (nth update-nth)))))

(defthm hpg-runs-fill-ok
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*))
           (and (hpgp (hpg-runs-fill c l fuel hpg)) (hpg-rn-ok (hpg-runs-fill c l fuel hpg))))
  :hints (("Goal" :induct (hpg-runs-fill c l fuel hpg)
           :in-theory (e/d (h-nrbi h-nrb-length h-rb-length) (hpgp hpg-rn-ok hpg-run-push hpg-run-push-ok hpg-run-new-ok)))
          ("Subgoal *1/4" :use (hpg-run-new-ok
                                (:instance hpg-run-push-ok (hpg (mv-nth 1 (hpg-run-new c l hpg))) (n (nth c (nth *h-nrbi* hpg)))
                                           (off (mv-nth 0 (hpg-run-new c l hpg))))))))

(in-theory (disable hpg-run-push hpg-runs-fill))

; ---- the procedures and the externs they use past gen-st-xrfb's

(defconst *pu-proc* (find-proc "hpg_run_push" *heapg-xmod*))
(defconst *rf-proc* (find-proc "hpg_runs_fill" *heapg-xmod*))
(defconst *tc-proc* (find-proc "hpg_run_take_c" *heapg-xmod*))

(assert-event (and *pu-proc* *rf-proc* *tc-proc* (equal (find-proc "hpg_run_from_batch" *heapg-xmod*) *rfb-proc*)))

(defmacro xt-finds ()
  '(and (xr-finds) (equal (find-proc "hp_set_rb" procs) (list :extern "hp_set_rb" :set-elem *h-rbi*))
        (equal (find-proc "hpg_run_push" procs) *pu-proc*) (equal (find-proc "hpg_runs_fill" procs) *rf-proc*)
        (equal (find-proc "hpg_run_from_batch" procs) *rfb-proc*) (equal (find-proc "hpg_run_take_c" procs) *tc-proc*)))

; ---- hpg_run_push: its body's run on hs's entry, its invocation

(defconst *pu-ls* (nth 4 *pu-proc*))
(defconst *pu-body* (nth 5 *pu-proc*))

(defthm pu-proc-shape
  (equal *pu-proc* (list :subroutine "hpg_run_push" (nth 2 *pu-proc*)
                         (cons (list "hs" :inout "heap_state") (g-dummies '(c n off))) *pu-ls* *pu-body*))
  :rule-classes nil)

(defmacro pu-fr () '(undef-locals *pu-ls* (fb '(c n off) (list c n off) (put "hs" (list* :obj :inout key) nil))))

(defmacro pu-pre ()
  '(and (natp c) (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg))) (natp n) (< n 64)
        (< (rb-at c (+ 1 n)) (len (nth *h-rbi* hpg))) (natp off) (<= off *hb40*)))

(make-event
 `(defthm pu-run
    (implies (and (xt-finds) (hpgp hpg) (hpg-rn-ok hpg) (pu-pre)
                  (dr-heap-at heap key cm hpg) (integerp k) (< 50 k))
             (let ((r (f-ex-list *pu-body* (pu-fr) heap procs k)))
               (and (equal (mv-nth 0 r) :normal)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (hpg-run-push c n off hpg)) heap)))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (hpg-run-push update-h-rbi update-h-nrbi h-rb-length h-nrb-length obj-of int64p
                              ext-op ext-read-p ext-write-p ext-dums fb)
                             (f-ev f-bind f-ex hs-rep hpgp hpg-rn-ok dr-heap-at))
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      ,@(xr-expands (list *pu-proc*)))))))

(defthm pu-ok
  (implies (and (xt-finds) (hpgp hpg) (hpg-rn-ok hpg) (pu-pre)
                (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (dr-heap-at heap key cm hpg) (integerp fuel) (< 60 fuel))
           (equal (f-invoke *pu-proc* (cons (list :var ob) (g-lits (list c n off))) caller heap procs fuel)
                  (mv nil caller (put key (hs-rep cm (hpg-run-push c n off hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(int64p natp int64-listp len car-cons cdr-cons (int64-listp) (len) (g-dummies)
                                        (nth) (cons) (equal) (binary-+) (unary--))
                                      (theory 'minimal-theory))
           :use (pu-proc-shape (:instance pu-run (k (1- fuel)))
                 (:instance f-invoke-sub-d (ks (list c n off)) (vs '(c n off)) (o "hs") (c "heap_state")
                            (nm "hpg_run_push") (rec (nth 2 *pu-proc*)) (ls *pu-ls*) (body *pu-body*))))))

; ---- a CALL of a heap procedure from its argument codes: what the codes answer (sv), the object's entry
; canonical (an hs-rep of its own stobj)

;; the CALL's arguments explicit: the object variable, three codes
(defmacro xk-key () '(mv-nth 1 (obj-of ob fr)))
(defmacro xk-e () '(cdr (lkp (xk-key) heap)))
(defmacro xk-hpg () '(hs-hpg (xk-e)))
(defmacro xk-v (cc) `(mv-nth 1 (sv ,cc fr heap)))
(defmacro xk-ok (cc) `(not (mv-nth 0 (sv ,cc fr heap))))
(defmacro xk-obj ()
  '(and (not (mv-nth 0 (obj-of ob fr))) (eq (mv-nth 2 (obj-of ob fr)) :inout)
        (dr-heap-at heap (xk-key) (xk-e) (xk-hpg)) (hpgp (xk-hpg)) (hpg-rn-ok (xk-hpg))))

(defun-nx scv-pu (ob c1 c2 c3 fr heap)
  (let ((c (xk-v c1)) (n (xk-v c2)) (off (xk-v c3)) (hpg (xk-hpg)))
    (if (and (xk-obj) (xk-ok c1) (xk-ok c2) (xk-ok c3) (pu-pre))
        (mv nil fr (put (xk-key) (hs-rep (xk-e) (hpg-run-push c n off hpg)) heap))
      (mv :orc fr heap))))

; scv-pu's answer, in pieces (opened inside pu-okc, its IFs split the goal 500-fold)
(defthm scv-pu-cond
  (implies (not (mv-nth 0 (scv-pu ob c1 c2 c3 fr heap)))
           (let ((c (xk-v c1)) (n (xk-v c2)) (off (xk-v c3)) (hpg (xk-hpg)))
             (and (xk-obj) (xk-ok c1) (xk-ok c2) (xk-ok c3) (pu-pre)
                  (equal (cdr (lkp ob fr)) (list* :obj :inout (xk-key)))
                  (int64-listp (list c n off))
                  (equal (mv-nth 1 (scv-pu ob c1 c2 c3 fr heap)) fr)
                  (equal (mv-nth 2 (scv-pu ob c1 c2 c3 fr heap))
                         (put (xk-key) (hs-rep (xk-e) (hpg-run-push c n off hpg)) heap)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(scv-pu mv-nth car-cons cdr-cons eq not natp int64p int64-listp (int64-listp)
                                        (zp) (equal) (cons) (expt) (unary--) (binary-+))
                                      (theory 'minimal-theory))
           :use ((:instance obj-of-binding (caller fr))))))

(defthm svs-is-3
  (implies (and (not (mv-nth 0 (sv x1 fr heap))) (not (mv-nth 0 (sv x2 fr heap))) (not (mv-nth 0 (sv x3 fr heap))))
           (svs-is (list x1 x2 x3) (list (mv-nth 1 (sv x1 fr heap)) (mv-nth 1 (sv x2 fr heap)) (mv-nth 1 (sv x3 fr heap)))
                   fr heap))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable svs-is))))

(defthm pu-okc
  (implies (and (xt-finds) (not (mv-nth 0 (scv-pu ob c1 c2 c3 fr heap)))
                (integerp fuel) (< (+ 70 (acl2-count (list c1 c2 c3))) fuel))
           (equal (f-invoke *pu-proc* (list (list :var ob) c1 c2 c3) fr heap procs fuel)
                  (mv nil fr (mv-nth 2 (scv-pu ob c1 c2 c3 fr heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(len (len) (g-dummies) (kar) (nth) (true-list-fix) (equal) car-cons cdr-cons (:type-prescription acl2-count))
                                      (theory 'minimal-theory))
           :use (scv-pu-cond pu-proc-shape
                 (:instance svs-is-3 (x1 c1) (x2 c2) (x3 c3))
                 (:instance f-invoke-st-codes (p *pu-proc*) (d '("hs" :inout "heap_state")) (vs '(c n off))
                            (a (list :var ob)) (cs (list c1 c2 c3)) (ks (list (xk-v c1) (xk-v c2) (xk-v c3))) (caller fr))
                 (:instance pu-ok (caller fr) (key (xk-key)) (cm (xk-e)) (hpg (xk-hpg))
                            (c (xk-v c1)) (n (xk-v c2)) (off (xk-v c3)))))))

; the CALL statement as the generated code writes it
(defthm xt-ex-pu
  (implies (and (xt-finds) (not (mv-nth 0 (scv-pu ob c1 c2 c3 fr heap)))
                (integerp fuel) (< (+ 71 (acl2-count (list c1 c2 c3))) fuel))
           (equal (f-ex (list :call "hpg_run_push" (list (list :var ob) c1 c2 c3)) fr heap procs fuel)
                  (mv :normal fr (mv-nth 2 (scv-pu ob c1 c2 c3 fr heap)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-invoke pu-okc scv-pu)
           :expand ((f-ex (list :call "hpg_run_push" (list (list :var ob) c1 c2 c3)) fr heap procs fuel))
           :use ((:instance pu-okc (fuel (1- fuel)))))))

; ---- hpg_runs_fill: one iteration of its DO, on the ACL2 side

(defmacro rf-m () '(nth c (nth *h-nrbi* hpg)))

(defun-nx rf-go (c l n hpg)
  (and (not (zp n)) (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg))) (<= 0 (rf-m)) (< (rf-m) 64)
       (< (rb-at c (+ 1 (rf-m))) (len (nth *h-rbi* hpg))) (not (equal (mv-nth 0 (hpg-run-new c l hpg)) 0))))

(defun-nx rf-next (c l hpg)
  (hpg-run-push c (rf-m) (mv-nth 0 (hpg-run-new c l hpg)) (mv-nth 1 (hpg-run-new c l hpg))))

(defthm rf-fill-step
  (implies (rf-go c l n hpg) (equal (hpg-runs-fill c l n hpg) (hpg-runs-fill c l (1- n) (rf-next c l hpg))))
  :hints (("Goal" :in-theory (enable hpg-runs-fill h-nrbi h-nrb-length h-rb-length) :expand ((hpg-runs-fill c l n hpg)))))

(defthm rf-next-ok
  (implies (and (rf-go c l n hpg) (hpgp hpg) (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*))
           (and (hpgp (rf-next c l hpg)) (hpg-rn-ok (rf-next c l hpg))))
  :hints (("Goal" :in-theory (disable hpg-run-push-ok hpg-run-new-ok hpgp hpg-rn-ok)
           :use (hpg-run-new-ok
                 (:instance hpg-run-push-ok (hpg (mv-nth 1 (hpg-run-new c l hpg))) (n (rf-m))
                            (off (mv-nth 0 (hpg-run-new c l hpg))))))))

(defthm rf-fill-zero
  (implies (zp n) (equal (hpg-runs-fill c l n hpg) hpg))
  :hints (("Goal" :expand ((hpg-runs-fill c l n hpg)))))

(in-theory (disable rf-go rf-next))

; ---- one iteration, symbolically on f-ex

(defconst *rf-ls* (nth 4 *rf-proc*))
(defconst *rf-body* (nth 5 *rf-proc*))
(defconst *rf-b* (cadr (car *rf-body*)))

(defthm rf-proc-shape
  (and (equal *rf-proc* (list :subroutine "hpg_runs_fill" (nth 2 *rf-proc*)
                              (cons (list "hs" :inout "heap_state") (g-dummies '(c l fuel))) *rf-ls* *rf-body*))
       (equal *rf-body* (list (list :do *rf-b*))))
  :rule-classes nil)

(defun rf-v-at (fr nm v) (equal (lkp nm fr) (list* nm :int64 v)))
(defthm rf-v-at-lkp (implies (rf-v-at fr nm v) (equal (lkp nm fr) (list* nm :int64 v))))
(defthm rf-v-at-put
  (equal (rf-v-at (put k w fr) nm v) (if (equal k nm) (equal w (cons :int64 v)) (rf-v-at fr nm v))))
(in-theory (disable rf-v-at))

(defmacro rf-hyps ()
  '(and (xt-finds) (dr-frp fr *rf-ls*) (dr-hs-at fr key)
        (rf-v-at fr "c_" c) (rf-v-at fr "l_" l) (rf-v-at fr "fuel_" n)
        (natp c) (<= c 64) (natp l) (<= l *hb40*) (natp n) (int64p n)
        (hpgp hpg) (hpg-rn-ok hpg) (dr-heap-at heap key cm hpg)))

(defmacro rf-kb () '(+ 200 (acl2-count *rf-b*)))

(defmacro rf-iter-hints ()
  ''(:in-theory (e/d (obj-of int64p ext-op ext-read-p ext-write-p ext-dums s-call-val-r rfb-res rfb-shape scv-pu
                     h-nrbi h-nrb-length h-rb-length rf-go rf-next)
                    (f-ev f-bind f-ex hs-rep hpgp hpg-rn-ok dr-heap-at hpg-run-new hpg-run-push hpg-runs-fill))))

(defconst *rf-s1* (nth 0 *rf-b*))
(defconst *rf-s2* (nth 1 *rf-b*))
(defconst *rf-e* (nth 3 *rf-s2*))

(defmacro rf-fr (fr) `(and (dr-frp ,fr *rf-ls*) (dr-hs-at ,fr key) (rf-v-at ,fr "c_" c) (rf-v-at ,fr "l_" l) (rf-v-at ,fr "fuel_" n)))

(make-event
 `(defthm rf-s1
    (implies (and (rf-hyps) (integerp k) (< 40 k))
             (let ((r (f-ex *rf-s1* fr heap procs k)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (rf-fr (mv-nth 1 r))
                    (equal (lkp "t_3" (mv-nth 1 r))
                           (list* "t_3" :logical (not (and (not (zp n)) (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg))))))))))
    :hints (("Goal" :do-not-induct t ,@(rf-iter-hints)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *rf-proc*)))))))

(make-event
 `(defthm rf-e1
    (implies (and (rf-hyps) (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg))) (integerp k) (< 40 k))
             (let ((r (f-ex (nth 0 *rf-e*) fr heap procs k)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (rf-fr (mv-nth 1 r))
                    (rf-v-at (mv-nth 1 r) "n_4" (rf-m)))))
    :hints (("Goal" :do-not-induct t ,@(rf-iter-hints)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *rf-proc*)))))))

(make-event
 `(defthm rf-e2
    (implies (and (rf-hyps) (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg))) (rf-v-at fr "n_4" (rf-m)) (integerp k) (< 40 k))
             (let ((r (f-ex (nth 1 *rf-e*) fr heap procs k)))
               (and (equal (car r) :normal) (equal (mv-nth 2 r) heap) (rf-fr (mv-nth 1 r))
                    (rf-v-at (mv-nth 1 r) "n_4" (rf-m))
                    (equal (lkp "t_6" (mv-nth 1 r))
                           (list* "t_6" :logical (and (<= 0 (rf-m)) (< (rf-m) 64)
                                                     (< (rb-at c (+ 1 (rf-m))) (len (nth *h-rbi* hpg)))))))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (obj-of s-call-val-r rfb-res rfb-shape scv-pu rf-go rf-next int64p ext-op ext-read-p ext-write-p ext-dums h-nrbi h-nrb-length h-rb-length)
                             (f-ev f-bind f-ex hs-rep hpgp hpg-rn-ok dr-heap-at hpg-run-new hpg-run-push hpg-runs-fill))
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *rf-proc*)))))))

(defmacro rf-lv (nm) `(cddr (lkp ,nm fr)))
(defmacro rf-lt (nm) `(and (consp (cdr (lkp ,nm fr))) (equal (cadr (lkp ,nm fr)) :int64)))

(defthm rf-scv-pu
  (implies (and (dr-hs-at fr key) (rf-lt "c_") (rf-lt "n_4") (rf-lt "off_8") (hpgp hpg) (hpg-rn-ok hpg)
                (let ((c (rf-lv "c_")) (n (rf-lv "n_4")) (off (rf-lv "off_8"))) (pu-pre)))
           (equal (scv-pu "hs" '(:var "c_") '(:var "n_4") '(:var "off_8") fr (put key (hs-rep cm hpg) h))
                  (mv nil fr (put key (hs-rep cm (hpg-run-push (rf-lv "c_") (rf-lv "n_4") (rf-lv "off_8") hpg))
                                  (put key (hs-rep cm hpg) h)))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (scv-pu obj-of int64p) (hs-rep hpgp hpg-rn-ok hpg-run-push))
           :expand ((:free (e) (sv e fr (put key (hs-rep cm hpg) h)))))))

(defconst *rf-f* (nth 3 (nth 2 *rf-e*)))

(defthm hpg-run-new-car
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*))
           (and (natp (car (hpg-run-new c l hpg))) (<= (car (hpg-run-new c l hpg)) *hb40*)
                (integerp (car (hpg-run-new c l hpg))) (<= 0 (car (hpg-run-new c l hpg))) (int64p (car (hpg-run-new c l hpg)))
                (<= -9223372036854775808 (car (hpg-run-new c l hpg))) (<= (car (hpg-run-new c l hpg)) 9223372036854775807)
                (not (equal (car (hpg-run-new c l hpg)) :undef))))
  :hints (("Goal" :in-theory (disable hpg-run-new hpg-run-new-ok hpgp hpg-rn-ok) :use hpg-run-new-ok)))

(make-event
 `(defthm rf-f
    (implies (and (rf-hyps) (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg))) (rf-v-at fr "n_4" (rf-m))
                  (<= 0 (rf-m)) (< (rf-m) 64) (< (rb-at c (+ 1 (rf-m))) (len (nth *h-rbi* hpg)))
                  (integerp k) (< 200 k))
             (let ((r (f-ex-list *rf-f* fr heap procs k)) (off (mv-nth 0 (hpg-run-new c l hpg))))
               (and (equal (car r) (if (equal off 0) :normal :cycle))
                    (equal (mv-nth 2 r) (put key (hs-rep cm (if (equal off 0) (mv-nth 1 (hpg-run-new c l hpg)) (rf-next c l hpg)))
                                             heap))
                    (implies (not (equal off 0))
                             (and (dr-frp (mv-nth 1 r) *rf-ls*) (dr-hs-at (mv-nth 1 r) key)
                                  (rf-v-at (mv-nth 1 r) "c_" c) (rf-v-at (mv-nth 1 r) "l_" l) (rf-v-at (mv-nth 1 r) "fuel_" (1- n)))))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (obj-of int64p ext-op ext-read-p ext-write-p ext-dums h-nrbi h-nrb-length h-rb-length rf-next)
                             (f-ev f-bind f-ex hs-rep hpgp hpg-rn-ok dr-heap-at hpg-run-new hpg-run-push hpg-runs-fill scv-pu))
             :expand ((:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *rf-proc*)))))))

(defmacro rf-c-thy (&rest en)
  `(e/d (h-nrbi h-nrb-length h-rb-length rf-go rf-next ,@en)
        ,(set-difference-eq '(f-ev f-bind hs-rep hpgp hpg-rn-ok dr-heap-at hpg-run-new hpg-run-push scv-pu rf-s1 rf-e1 rf-e2 rf-f dr-frp
         xt-ex-pu rt-call xr-call-ok xr-call-rn xr-call-rp xr-ex-rn xr-ex-rp g-st-fn-call f-ex-do-exit2 f-ex-do-cycle sxc-assign-f-ex sxc-call-f-ex f-ex-xcall-set-elem f-ex-xcall-set-scalar sxf-assign-f-ex f-ex-do-exit sx-ok-assign-f-ex sx-is-f-ex f-ex-jump f-ex-assign-obj fx-is-f-ex fx-f-ex-select fx-f-ex-if fx-f-ex-cycle fx-f-ex-return fx-f-ex-assign f-ex-return f-ex-select f-ex-if f-ex-assign-var f-ex sxc-r-ok-is-f-ex-list sxc-d-ok-is-f-ex-list sxc-ok-is-f-ex-list sxf-n-ok-is-f-ex-list sxf-h-ok-is-f-ex-list sxf-lits-ok-is-f-ex-list sxf-ok-is-f-ex-list f-ex-list-do-exit f-ex-list-one-normal f-ex-list-exit-tail sx-ok-is-f-ex-list sx-list-is-f-ex-list fx-list-is-f-ex-list fx-f-ex-list-cons fx-f-ex-list-nil f-ex-list-open f-ex-list pu-run rt-run rn-run rp-run dr-body-run dr-loop stfn-body) en)))

(defmacro rf-pre () '(and (rf-hyps) (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg)))))
(defmacro rf-ok-m () '(and (<= 0 (rf-m)) (< (rf-m) 64) (< (rb-at c (+ 1 (rf-m))) (len (nth *h-rbi* hpg)))))
(defmacro rf-off () '(car (hpg-run-new c l hpg)))
; what the rest of the body does once c is in range
(defmacro rf-tail (r)
  `(and (equal (car ,r) (if (and (rf-ok-m) (not (equal (rf-off) 0))) :cycle :normal))
        (equal (mv-nth 2 ,r) (if (rf-ok-m)
                                 (put key (hs-rep cm (if (equal (rf-off) 0) (mv-nth 1 (hpg-run-new c l hpg)) (rf-next c l hpg))) heap)
                               heap))
        (implies (and (rf-ok-m) (not (equal (rf-off) 0)))
                 (and (dr-frp (mv-nth 1 ,r) *rf-ls*) (dr-hs-at (mv-nth 1 ,r) key)
                      (rf-v-at (mv-nth 1 ,r) "c_" c) (rf-v-at (mv-nth 1 ,r) "l_" l) (rf-v-at (mv-nth 1 ,r) "fuel_" (1- n))))))

(make-event
 `(defthm rf-t3
    (implies (and (rf-pre) (rf-v-at fr "n_4" (rf-m)) (equal (lkp "t_6" fr) (list* "t_6" :logical (rf-ok-m)))
                  (integerp k) (< 210 k))
             (rf-tail (f-ex-list (cddr *rf-e*) fr heap procs k)))
    :hints (("Goal" :do-not-induct t :in-theory (rf-c-thy)
             :use ((:instance rf-f (k (- k 2))))
             :expand ((f-ex-list ',(cddr *rf-e*) fr heap procs k)
                      (f-ex ',(nth 2 *rf-e*) fr heap procs (- k 1))
                      (:free (fr h k) (f-ev '(:var "t_6") fr h procs k))
                      (:free (fr h k) (f-ev '(:not (:var "t_6")) fr h procs k)))))))

(make-event
 `(defthm rf-t2
    (implies (and (rf-pre) (rf-v-at fr "n_4" (rf-m)) (integerp k) (< 220 k))
             (rf-tail (f-ex-list (cdr *rf-e*) fr heap procs k)))
    :hints (("Goal" :do-not-induct t :in-theory (rf-c-thy)
             :expand ((f-ex-list ',(cdr *rf-e*) fr heap procs k))
             :use ((:instance rf-e2 (k (- k 1)))
                   (:instance rf-t3 (fr (mv-nth 1 (f-ex (nth 1 *rf-e*) fr heap procs (- k 1)))) (k (- k 1))))))))

(make-event
 `(defthm rf-t1
    (implies (and (rf-pre) (integerp k) (< 230 k))
             (rf-tail (f-ex-list *rf-e* fr heap procs k)))
    :hints (("Goal" :do-not-induct t :in-theory (rf-c-thy)
             :expand ((f-ex-list ',*rf-e* fr heap procs k))
             :use ((:instance rf-e1 (k (- k 1)))
                   (:instance rf-t2 (fr (mv-nth 1 (f-ex (nth 0 *rf-e*) fr heap procs (- k 1)))) (k (- k 1))))))))

(defun rf-c-expands ()
  (declare (xargs :mode :program))
  `((f-ex-list ',*rf-b* fr heap procs k) (:free (fr h) (f-ex-list ',(cdr *rf-b*) fr h procs (- k 1)))
    (:free (fr h) (f-ex ',*rf-s2* fr h procs (- k 2)))
    (:free (fr h) (f-ev '(:var "t_3") fr h procs (- k 3)))
    (:free (fr h) (f-ex-list ',(cddr *rf-b*) fr h procs (- k 2)))
    (:free (fr h) (f-ex '(:exit) fr h procs (- k 3)))))

(make-event
 `(defthm rf-iter-exit
    (implies (and (rf-hyps) (not (rf-go c l n hpg)) (integerp k) (< (rf-kb) k))
             (let ((r (f-ex-list *rf-b* fr heap procs k)))
               (and (equal (mv-nth 0 r) :exit)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (hpg-runs-fill c l n hpg)) heap)))))
    :hints (("Goal" :do-not-induct t :in-theory (rf-c-thy dr-heap-at-put-same)
             :use ((:instance rf-s1 (k (- k 1)))
                   (:instance rf-t1 (fr (mv-nth 1 (f-ex *rf-s1* fr heap procs (- k 1)))) (k (- k 3))))
             :expand ((hpg-runs-fill c l n hpg) ,@(rf-c-expands))))))

(make-event
 `(defthm rf-iter-cycle
    (implies (and (rf-hyps) (rf-go c l n hpg) (integerp k) (< (rf-kb) k))
             (let ((r (f-ex-list *rf-b* fr heap procs k)))
               (and (equal (mv-nth 0 r) :cycle)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (rf-next c l hpg)) heap))
                    (dr-frp (mv-nth 1 r) *rf-ls*) (dr-hs-at (mv-nth 1 r) key)
                    (rf-v-at (mv-nth 1 r) "c_" c) (rf-v-at (mv-nth 1 r) "l_" l) (rf-v-at (mv-nth 1 r) "fuel_" (1- n)))))
    :hints (("Goal" :do-not-induct t :in-theory (rf-c-thy)
             :use ((:instance rf-s1 (k (- k 1)))
                   (:instance rf-t1 (fr (mv-nth 1 (f-ex *rf-s1* fr heap procs (- k 1)))) (k (- k 3))))
             :expand ,(rf-c-expands)))))

; ---- the DO, by induction on the fuel

(defmacro rf-k () '(* (+ 1 (nfix n)) (+ 2 (rf-kb))))

(defun-nx rf-ind (c l n hpg fr heap procs k key cm)
  (declare (xargs :measure (nfix n)))
  (if (or (not (rf-go c l n hpg)) (zp k)) (list fr heap)
    (rf-ind c l (1- n) (rf-next c l hpg) (mv-nth 1 (f-ex-list *rf-b* fr heap procs (1- k)))
            (put key (hs-rep cm (rf-next c l hpg)) heap) procs (1- k) key cm)))

(defthm rf-go-n (implies (rf-go c l n hpg) (and (integerp n) (< 0 n)))
  :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable rf-go))))

(defthm rf-loop
  (implies (and (rf-hyps) (integerp k) (< (rf-k) k))
           (and (equal (mv-nth 0 (f-ex (list :do *rf-b*) fr heap procs k)) :normal)
                (equal (mv-nth 2 (f-ex (list :do *rf-b*) fr heap procs k)) (put key (hs-rep cm (hpg-runs-fill c l n hpg)) heap))))
  :hints (("Goal" :induct (rf-ind c l n hpg fr heap procs k key cm) :do-not-induct t
           :in-theory (rf-c-thy f-ex-do-cycle f-ex-do-exit2 rf-iter-exit rf-iter-cycle rf-fill-step rf-next-ok dr-heap-at-put))))
