; gen-st-rfb: hpg-run-from-batch-fortran-correct (GEN.md "What remains" 4b).
; hpg-run-from-batch CALLs hpg_run_pop and then, when the batch is empty,
; hpg_run_new; both take an INTENT(OUT) result and read `hp_*` externs
; (h-nrb, h-rb, h-chead, h-aival, the arena's counters: 4c), so their
; correctness is the named hypothesis `p-sorc-r`: gen-stcall's p-sorc on a
; concrete oracle answering each callee's ACL2 value, on hs's entry laid out
; by gen-st-drain's hs-rep (the externs in the ghost component "%ext"), its
; result copied out to the CALL's last argument. The body has no loop: its
; run is symbolic.

(in-package "ACL2")

(include-book "gen-st-drain")

; ---- clotran's definitions (heapsw, heapal, heaprn), compared by check-gen

(defun hpg-s64 (x)
  (declare (xargs :guard t))
  (if (and (integerp x) (<= -9223372036854775808 x) (< x 9223372036854775808)) x 0))

(defun hpg-sw-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-ok hpg)
       (<= (h-okind-length hpg) *hb40*) (<= (h-ofree-length hpg) *hb40*) (<= (h-onext-length hpg) *hb40*)
       (<= (h-vfree-length hpg) *hb40*) (<= (h-vnext-length hpg) *hb40*)
       (<= (h-sfree-length hpg) *hb40*) (<= (h-snext-length hpg) *hb40*)
       (<= (h-aival-length hpg) *hb40*) (<= (h-chead-length hpg) *hb40*)
       (<= (h-ofin-length hpg) *hb40*) (<= (h-srel-length hpg) *hb40*)
       (natp (h-nswo hpg)) (<= (h-nswo hpg) *hb40*)
       (natp (h-nswv hpg)) (<= (h-nswv hpg) *hb40*)
       (natp (h-nsws hpg)) (<= (h-nsws hpg) *hb40*)
       (natp (h-afree hpg)) (<= (h-afree hpg) *hb40*)))

(defun hpg-al-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-sw-ok hpg)
       (natp (h-oused hpg)) (<= (h-oused hpg) *hb40*) (natp (h-ocap hpg)) (<= (h-ocap hpg) *hb40*)
       (<= (h-ob-length hpg) *hb40*) (natp (h-nob hpg)) (< (h-nob hpg) (h-ob-length hpg))
       (natp (h-vused hpg)) (<= (h-vused hpg) *hb40*) (natp (h-vcap hpg)) (<= (h-vcap hpg) *hb40*)
       (<= (h-vb-length hpg) *hb40*) (natp (h-nvb hpg)) (< (h-nvb hpg) (h-vb-length hpg))
       (natp (h-sused hpg)) (<= (h-sused hpg) *hb40*) (natp (h-scap hpg)) (<= (h-scap hpg) *hb40*)
       (<= (h-sb-length hpg) *hb40*) (natp (h-nsb hpg)) (< (h-nsb hpg) (h-sb-length hpg))))

(defconst *run-batch* 64)
(defconst *run-classes* 8)

(defun hpg-rn-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-al-ok hpg)
       (natp (h-aused hpg)) (<= (h-aused hpg) *hb40*) (natp (h-acap hpg)) (<= (h-acap hpg) *hb40*)
       (natp (h-areu hpg)) (<= (h-areu hpg) *hb40*) (natp (h-afre hpg)) (<= (h-afre hpg) *hb40*)
       (natp (h-asince hpg)) (<= (h-asince hpg) *hb40*)
       (<= (h-rb-length hpg) *hb40*) (<= (h-nrb-length hpg) *hb40*)
       (<= (h-aival-length hpg) *hb40*) (<= (h-chead-length hpg) *hb40*)))

(defmacro rb-at (c k) `(+ (* (- ,c 1) *run-batch*) ,k))

(defun hpg-run-pop (c hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (and (hpg-rn-ok hpg) (natp c))))
  (if (and (<= 1 c) (<= c *run-classes*) (< c (h-nrb-length hpg)))
      (let ((n (h-nrbi c hpg)))
        (if (and (< 0 n) (<= n *run-batch*) (< (rb-at c n) (h-rb-length hpg)))
            (let ((off (h-rbi (rb-at c n) hpg)))
              (if (< 0 off)
                  (let ((hpg (update-h-nrbi c (- n 1) hpg)))
                    (mv off hpg))
                (mv 0 hpg)))
          (mv 0 hpg)))
    (mv 0 hpg)))

(defun hpg-run-new (c l hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*))))
  (let ((h (if (< c (h-chead-length hpg)) (h-cheadi c hpg) 0)))
    (if (and (< 0 h) (< h (h-aival-length hpg)))
        (let* ((hpg (update-h-cheadi c (hpg-s64 (h-aivali h hpg)) hpg))
               (hpg (update-h-areu (hpg-add (h-areu hpg) 1) hpg))
               (hpg (update-h-asince (hpg-add (h-asince hpg) l) hpg)))
          (mv h hpg))
      (if (and (< 0 l) (<= (+ (h-aused hpg) l) (h-acap hpg)))
          (let* ((off (+ 1 (h-aused hpg)))
                 (hpg (update-h-aused (+ (h-aused hpg) l) hpg))
                 (hpg (update-h-afre (hpg-add (h-afre hpg) 1) hpg))
                 (hpg (update-h-asince (hpg-add (h-asince hpg) l) hpg)))
            (mv off hpg))
        (mv 0 hpg)))))

(defun hpg-run-from-batch (c l hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*))))
  (mv-let (off hpg) (hpg-run-pop c hpg)
    (if (< 0 off)
        (mv off hpg)
      (hpg-run-new c l hpg))))

; ---- run-pop keeps the stobj's type and hpg-rn-ok; its offset is an int64

(hsb64-elems h-nrbp) (hsb64-update h-nrbp) (hsb64-elems h-rbp)

(defthm hpgp-arrs-r
  (implies (hpgp hpg) (and (h-nrbp (nth 53 hpg)) (h-rbp (nth 52 hpg))))
  :hints (("Goal" :in-theory (e/d (hpgp) (nth h-nrbp h-rbp)))))

(defthm hpgp-update-nrb
  (implies (and (hpgp hpg) (h-nrbp v)) (hpgp (update-nth 53 v hpg)))
  :hints (("Goal" :in-theory (enable hpgp))))

(defthm hpg-rn-ok-update-nrb
  (implies (and (hpg-rn-ok hpg) (equal (len v) (len (nth 53 hpg)))) (hpg-rn-ok (update-nth 53 v hpg)))
  :hints (("Goal" :in-theory (enable hpg-rn-ok hpg-al-ok hpg-sw-ok hpg-ok hpg-lens))))

(defthm hpg-run-pop-ok
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c))
           (and (hpgp (mv-nth 1 (hpg-run-pop c hpg))) (hpg-rn-ok (mv-nth 1 (hpg-run-pop c hpg)))
                (int64p (mv-nth 0 (hpg-run-pop c hpg)))))
  :hints (("Goal" :in-theory (e/d (nfix int64p h-nrbi h-rbi update-h-nrbi h-nrb-length h-rb-length)
                           (hpgp hpg-rn-ok nth update-nth h-nrbp h-rbp h-nrbp-nth h-rbp-nth h-nrbp-update-nth hpgp-arrs-r hpgp-update-nrb))
           :use (hpgp-arrs-r
                 (:instance h-nrbp-nth (l (nth 53 hpg)) (i c))
                 (:instance h-rbp-nth (l (nth 52 hpg)) (i (rb-at c (nth c (nth 53 hpg)))))
                 (:instance h-nrbp-update-nth (l (nth 53 hpg)) (i c) (v (+ -1 (nth c (nth 53 hpg)))))
                 (:instance hpgp-update-nrb (v (update-nth c (+ -1 (nth c (nth 53 hpg))) (nth 53 hpg))))))))

(defthm hpg-run-pop-int
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c))
           (and (integerp (car (hpg-run-pop c hpg)))
                (<= -9223372036854775808 (car (hpg-run-pop c hpg))) (<= (car (hpg-run-pop c hpg)) 9223372036854775807)))
  :rule-classes ((:type-prescription :corollary (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c))
                                                         (integerp (car (hpg-run-pop c hpg)))))
                 (:linear :corollary (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c))
                                              (and (<= -9223372036854775808 (car (hpg-run-pop c hpg)))
                                                   (<= (car (hpg-run-pop c hpg)) 9223372036854775807)))))
  :hints (("Goal" :use hpg-run-pop-ok :in-theory (e/d (int64p) (hpg-run-pop-ok hpg-run-pop hpgp hpg-rn-ok)))))

(in-theory (disable hpg-run-pop hpg-run-new hpg-rn-ok))

; ---- the procedure acl2-fortran prints (check-gen compares it)

(defconst *rfb-proc*
  (mv-let (e ps) (g-st-module *heapg-st-raw* '(hpg-obj-at) '(hpg-drain hpg-run-from-batch hpg-run-take hpg-next-tail hpg-seq-op)
                              *heapg-st*)
    (and (not e) (find-proc "hpg_run_from_batch" ps))))

(defconst *rfb-ls* (nth 4 *rfb-proc*))
(defconst *rfb-body* (nth 5 *rfb-proc*))

(defthm rfb-proc-shape
  (equal *rfb-proc*
         (list :subroutine "hpg_run_from_batch" (nth 2 *rfb-proc*)
               (list (list "hs" :inout "heap_state") (list "c_" :value :int64) (list "l_" :value :int64) (list "r" :out :int64))
               *rfb-ls* *rfb-body*))
  :rule-classes nil)

; ---- the oracle: the callee's ACL2 value on the stobj the entry holds, the offset to the last argument

(defun rfb-res (fr heap key e d r)
  (mv nil (put d (cons :int64 (car r)) fr) (put key (hs-rep e (mv-nth 1 r)) heap)))

(defun-nx s-call-val-r (name args fr heap)
  (mv-let (err key intent) (obj-of (kadr (kar args)) fr)
    (let* ((e (cdr (lkp key heap))) (hpg (hs-hpg e)) (d (car (last args))) (db (cdr (lkp (kadr d) fr))))
      (mv-let (e1 c) (sv (kadr args) fr heap)
        (mv-let (e2 l) (sv (kaddr args) fr heap)
          (cond ((or err (not (eq (kar (kar args)) :var)) (not (eq intent :inout)) e1
                     (not (eq (kar d) :var)) (not (consp db)) (not (eq (car db) :int64))
                     (not (hpgp hpg)) (not (hpg-rn-ok hpg)) (not (natp c)))
                 (mv :orc fr heap))
                ((and (equal name "hpg_run_pop") (equal (len args) 3))
                 (rfb-res fr heap key e (kadr d) (hpg-run-pop c hpg)))
                ((and (equal name "hpg_run_new") (equal (len args) 4) (not e2) (natp l) (<= l *hb40*))
                 (rfb-res fr heap key e (kadr d) (hpg-run-new c l hpg)))
                (t (mv :orc fr heap))))))))

(mutual-recursion
 (defun sxc-r (x frame heap)
   (declare (xargs :guard t :measure (acl2-count x) :verify-guards nil
                   :hints (("Goal" :in-theory (union-theories
                                               '(acl2-count eql fix kadddr kaddr kadr kar kdr lkp mv-nth not o-finp o< synp
                                                 count-lkp-arm-cadr g-count-parts commutativity-2-of-+ fold-consts-in-+
                                                 kar-atom sv-atom unicity-of-0 (:type-prescription acl2-count)
                                                 (:type-prescription lkp) (:type-prescription sv) (:type-prescription sx))
                                               (executable-counterpart-theory :here))))))
   (case (kar x)
     (:assign (sx x frame heap))
     (:if (mv-let (err c) (sv (kadr x) frame heap)
            (cond (err (mv (errst err) frame heap))
                  ((not (booleanp c)) (mv (errst :type) frame heap))
                  (c (sxc-list-r (kaddr x) frame heap))
                  (t (sxc-list-r (kadddr x) frame heap)))))
     (:select (mv-let (err k) (sv (kadr x) frame heap)
                (cond (err (mv (errst err) frame heap))
                      ((not (integerp k)) (mv (errst :type) frame heap))
                      (t (let ((arm (lkp k (kaddr x))))
                           (sxc-list-r (if arm (kadr arm) (kadddr x)) frame heap))))))
     ((:cycle :exit :return) (mv (kar x) frame heap))
     (:call (mv-let (err fr2 h2) (s-call-val-r (kadr x) (kaddr x) frame heap)
              (if err (mv (errst err) frame heap) (mv :normal fr2 h2))))
     (otherwise (mv (errst :syntax) frame heap))))
 (defun sxc-list-r (ss frame heap)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) (mv :normal frame heap)
     (mv-let (sta fr2 h2) (sxc-r (car ss) frame heap)
       (if (eq sta :normal) (sxc-list-r (cdr ss) fr2 h2) (mv sta fr2 h2))))))

(in-theory (disable sxc-r sxc-list-r))

; ---- the named hypothesis: the callees' procedures answer the oracle (p-sorc on it)

(defun-sk p-sorc-r (procs b)
  (forall (x fr heap fuel)
    (implies (and (eq (kar x) :call) (not (mv-nth 0 (s-call-val-r (kadr x) (kaddr x) fr heap)))
                  (integerp fuel) (< (+ b (acl2-count x)) fuel))
             (equal (f-ex x fr heap procs fuel)
                    (mv :normal (mv-nth 1 (s-call-val-r (kadr x) (kaddr x) fr heap))
                        (mv-nth 2 (s-call-val-r (kadr x) (kaddr x) fr heap)))))))

(in-theory (disable p-sorc-r))

(defthm sxc-r-ok-is-f-ex-list
  (implies (and (p-sorc-r procs b) (natp b) (not (errstp (mv-nth 0 (sxc-list-r ss fr heap))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxc-list-r ss fr heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable s-call-val-r p-sorc-r f-ex-list f-ex sxc-r sxc-list-r)
           :use ((:functional-instance sxc-ok-is-f-ex-list
                  (s-call-val s-call-val-r) (sxc sxc-r) (sxc-list sxc-list-r)
                  (p-sorc p-sorc-r) (p-sorc-witness p-sorc-r-witness))))
          (dr-hint id clause '(f-ex-list) '(p-sorc-r-witness) '(p-sorc-r)
           '(:in-theory (union-theories '(p-sorc-r kadr kaddr kadddr) (theory 'minimal-theory)))
           '(:in-theory (union-theories '(kadr kaddr kadddr) (theory 'minimal-theory)) :use ((:instance p-sorc-r-necc)))
           '(:in-theory (disable s-call-val-r p-sorc-r f-ex f-ex-list sxc-r sxc-list-r)
             :expand ((:free (x frame heap) (sxc-r x frame heap)) (:free (ss frame heap) (sxc-list-r ss frame heap)))))))

; ---- f-invoke of a subroutine of this shape (object, two values, an OUT result)

(defmacro rfb-fr ()
  '(undef-locals ls (put "r" (cons :int64 :undef) (put "l_" (cons :int64 l) (put "c_" (cons :int64 c)
                                                                               (put o (list* :obj :inout key) nil))))))

(defthm f-invoke-sub-r
  (implies (and (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (consp (cdr (lkp d caller))) (equal (cadr (lkp d caller)) :int64)
                (int64p c) (int64p l) (integerp fuel) (< 10 fuel)
                (equal (mv-nth 0 (f-ex-list body (rfb-fr) heap procs (1- fuel))) :normal))
           (equal (f-invoke (list :subroutine nm rec
                                  (list (list o :inout cc) (list "c_" :value :int64) (list "l_" :value :int64)
                                        (list "r" :out :int64))
                                  ls body)
                            (list (list :var ob) (g-lit c) (g-lit l) (list :var d)) caller heap procs fuel)
                  (mv nil (copy-out (list (cons "r" d)) (mv-nth 1 (f-ex-list body (rfb-fr) heap procs (1- fuel))) caller)
                      (mv-nth 2 (f-ex-list body (rfb-fr) heap procs (1- fuel))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-ex-list undef-locals g-lit copy-out put)
           :expand ((:free (p) (f-invoke p (list (list :var ob) (g-lit c) (g-lit l) (list :var d)) caller heap procs fuel))
                    (:free (ds as callee outs f) (f-bind ds as caller callee outs heap procs f))))))

; ---- the body's run, symbolically

(defmacro rfb-fr0 ()
  '(undef-locals *rfb-ls* (put "r" (cons :int64 :undef) (put "l_" (cons :int64 l) (put "c_" (cons :int64 c)
                                                                                     (put "hs" (list* :obj :inout key) nil))))))

(defthm rfb-run
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c) (int64p c) (int64p l) (natp l) (<= l *hb40*)
                (dr-heap-at heap key comps hpg))
           (let ((r (sxc-list-r *rfb-body* (rfb-fr0) heap)))
             (and (equal (mv-nth 0 r) :normal)
                  (equal (cdr (lkp "r" (mv-nth 1 r))) (cons :int64 (mv-nth 0 (hpg-run-from-batch c l hpg))))
                  (equal (mv-nth 2 r) (put key (hs-rep comps (mv-nth 1 (hpg-run-from-batch c l hpg))) heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (s-call-val-r comp-of) (hpgp hpg-rn-ok hs-rep put hpg-run-pop hpg-run-new int64p))
           :expand ((:free (x frame heap) (sxc-r x frame heap)) (:free (ss frame heap) (sxc-list-r ss frame heap))
                    (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))))
          (and stable-under-simplificationp '(:in-theory (e/d (s-call-val-r comp-of int64p) (hpgp hpg-rn-ok hs-rep put hpg-run-pop hpg-run-new))))))

; ---- the theorem: the callees' correctness (p-sorc-r) the only hypothesis about the procedures;
; hs's heap entry holds the stobj as hs-rep lays it out, the result goes to the caller's d

(defthm hpg-run-from-batch-fortran-correct
  (implies (and (p-sorc-r procs b) (natp b)
                (hpgp hpg) (hpg-rn-ok hpg) (natp c) (int64p c) (natp l) (<= l *hb40*)
                (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (consp (cdr (lkp d caller))) (equal (cadr (lkp d caller)) :int64)
                (dr-heap-at heap key comps hpg)
                (integerp fuel) (< (+ 11 b (acl2-count *rfb-body*)) fuel))
           (equal (f-invoke *rfb-proc* (list (list :var ob) (g-lit c) (g-lit l) (list :var d)) caller heap procs fuel)
                  (mv nil (put d (cons :int64 (mv-nth 0 (hpg-run-from-batch c l hpg))) caller)
                      (put key (hs-rep comps (mv-nth 1 (hpg-run-from-batch c l hpg))) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (int64p) (f-invoke f-ex-list hpg-run-from-batch hpgp hpg-rn-ok g-lit undef-locals put
                                     f-invoke-sub-r rfb-run p-sorc-r hs-rep sxc-list-r sxc-r-ok-is-f-ex-list))
           :expand ((:free (fr) (copy-out (list (cons "r" d)) fr caller)) (:free (fr) (copy-out nil fr caller)))
           :use (rfb-proc-shape rfb-run
                 (:instance sxc-r-ok-is-f-ex-list (ss *rfb-body*) (fr (rfb-fr0)) (k (1- fuel)))
                 (:instance f-invoke-sub-r (o "hs") (cc "heap_state") (nm "hpg_run_from_batch")
                            (rec (nth 2 *rfb-proc*)) (ls *rfb-ls*) (body *rfb-body*))))))
