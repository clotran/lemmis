; gen-st-take: hpg-run-take-fortran-correct (GEN.md "What remains" 4b).
; hpg-run-take's body assigns two function calls, c_1 = hpg_size_class(n_,1,1)
; and l_2 = hpg_class_len(c_1,1,1), then CALLs hpg_run_take_c (INTENT(OUT)
; result r). sxc-t is gen-st-rfb's sxc-r plus an :fcall right-hand side in an
; assignment, answered by f-asg-val-t: the arguments by sv, then the callee's
; ACL2 value. Its hypothesis p-asg-t ("f-ev of the call is the oracle's") is
; discharged here (p-asg-t-holds) from hpg-size-class-fortran-correct and
; hpg-class-len-fortran-correct, through gen-callarg's f-invoke-args, when the
; procedures' hpg_size_class, hpg_class_len and hpg_n40 are the generated
; ones. hpg_run_take_c reads and writes `hp_*` externs (through
; hpg-runs-fill, hpg-run-from-batch, hpg-run-new: 4c), so its correctness is
; the named hypothesis p-sorc-t, on hs's entry laid out by gen-st-drain's
; hs-rep (the externs in the ghost component "%ext": a modelling choice, see
; GEN.md), as gen-st-rfb's p-sorc-r.

(in-package "ACL2")

(include-book "gen-st-rfb")
(include-book "gen-st-tkfn")

; ---- clotran's definitions (heaprn), compared by check-gen

(defun hpg-run-push (c n off hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp c) (<= 1 c) (< c (h-nrb-length hpg)) (natp n) (< n *run-batch*)
                              (< (rb-at c (+ 1 n)) (h-rb-length hpg)) (natp off) (<= off *hb40*))))
  (let ((hpg (update-h-rbi (rb-at c (+ 1 n)) off hpg)))
    (update-h-nrbi c (+ 1 n) hpg)))

(defun hpg-runs-fill (c l fuel hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix fuel)
                  :guard (and (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*) (natp fuel))))
  (if (or (zp fuel) (not (and (<= 1 c) (<= c *run-classes*) (< c (h-nrb-length hpg)))))
      hpg
    (let ((n (h-nrbi c hpg)))
      (if (not (and (<= 0 n) (< n *run-batch*) (< (rb-at c (+ 1 n)) (h-rb-length hpg))))
          hpg
        (mv-let (off hpg) (hpg-run-new c l hpg)
          (if (equal off 0)
              hpg
            (let ((hpg (hpg-run-push c n off hpg)))
              (hpg-runs-fill c l (- fuel 1) hpg))))))))

(defun hpg-run-take-c (c l batching hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*) (integerp batching))))
  (if (and (not (equal batching 0)) (<= c *run-classes*))
      (if (and (< c (h-nrb-length hpg)) (equal (h-nrbi c hpg) 0))
          (let ((hpg (hpg-runs-fill c l *run-batch* hpg)))
            (hpg-run-from-batch c l hpg))
        (hpg-run-from-batch c l hpg))
    (hpg-run-new c l hpg)))

(defun hpg-run-take (n batching hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp n) (<= n *hb40*) (integerp batching))))
  (if (not (< 0 n))
      (mv 0 hpg)
    (let* ((c (hpg-size-class n 1 1))
           (l (hpg-class-len c 1 1)))
      (hpg-run-take-c c l batching hpg))))

(in-theory (disable hpg-run-take-c))

; the class and its length: what hpg_run_take_c's guard asks
(defthm hpg-size-class-bounds
  (implies (and (natp c) (<= c 64)) (and (natp (hpg-size-class n c p)) (<= (hpg-size-class n c p) 64))))

(defthm hpg-class-len-bounds
  (and (natp (hpg-class-len c k p)) (<= (hpg-class-len c k p) *hb40*)))

; ---- the procedure acl2-fortran prints (check-gen compares it)

(defconst *rt-proc*
  (mv-let (e ps) (g-st-module *heapg-st-raw* '(hpg-obj-at) '(hpg-drain hpg-run-from-batch hpg-run-take hpg-next-tail hpg-seq-op)
                              *heapg-st*)
    (and (not e) (find-proc "hpg_run_take" ps))))

(defconst *rt-ls* (nth 4 *rt-proc*))
(defconst *rt-body* (nth 5 *rt-proc*))

(defthm rt-proc-shape
  (equal *rt-proc*
         (list :subroutine "hpg_run_take" (nth 2 *rt-proc*)
               (list (list "hs" :inout "heap_state") (list "n_" :value :int64) (list "batching_" :value :int64)
                     (list "r" :out :int64))
               *rt-ls* *rt-body*))
  :rule-classes nil)

; ---- the CALL oracle: hpg-run-take-c's ACL2 value on the stobj the entry holds, the offset to the last argument

(defun-nx s-call-val-t (name args fr heap)
  (mv-let (err key intent) (obj-of (kadr (kar args)) fr)
    (let* ((e (cdr (lkp key heap))) (hpg (hs-hpg e)) (d (car (last args))) (db (cdr (lkp (kadr d) fr))))
      (mv-let (e1 c) (sv (kadr args) fr heap)
        (mv-let (e2 l) (sv (kaddr args) fr heap)
          (mv-let (e3 bt) (sv (kadddr args) fr heap)
            ; the entry canonical (an hs-rep of its own stobj): the procedures leave "%ext" written in it
            (if (or err (not (eq (kar (kar args)) :var)) (not (eq intent :inout)) e1 e2 e3 (not (dr-heap-at heap key e hpg))
                    (not (eq (kar d) :var)) (not (consp db)) (not (eq (car db) :int64))
                    (not (hpgp hpg)) (not (hpg-rn-ok hpg)) (not (natp c)) (not (int64p c)) (not (natp l)) (< *hb40* l)
                    (not (int64p bt)) (not (equal name "hpg_run_take_c")) (not (equal (len args) 5)))
                (mv :orc fr heap)
              (rfb-res fr heap key e (kadr d) (hpg-run-take-c c l bt hpg)))))))))

; ---- the named hypothesis: hpg_run_take_c's procedure answers the oracle (p-sorc on it)

(defun-sk p-sorc-t (procs b)
  (forall (x fr heap fuel)
    (implies (and (eq (kar x) :call) (not (mv-nth 0 (s-call-val-t (kadr x) (kaddr x) fr heap)))
                  (integerp fuel) (< (+ b (acl2-count x)) fuel))
             (equal (f-ex x fr heap procs fuel)
                    (mv :normal (mv-nth 1 (s-call-val-t (kadr x) (kaddr x) fr heap))
                        (mv-nth 2 (s-call-val-t (kadr x) (kaddr x) fr heap)))))))

(in-theory (disable p-sorc-t))

; ---- f-invoke of a subroutine of this shape (object, two values, an OUT result)

(defmacro rt-fr ()
  '(undef-locals ls (put "r" (cons :int64 :undef) (put "batching_" (cons :int64 bt) (put "n_" (cons :int64 n)
                                                                                     (put o (list* :obj :inout key) nil))))))

(defthm f-invoke-sub-t
  (implies (and (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (consp (cdr (lkp d caller))) (equal (cadr (lkp d caller)) :int64)
                (int64p n) (int64p bt) (integerp fuel) (< 10 fuel)
                (equal (mv-nth 0 (f-ex-list body (rt-fr) heap procs (1- fuel))) :normal))
           (equal (f-invoke (list :subroutine nm rec
                                  (list (list o :inout cc) (list "n_" :value :int64) (list "batching_" :value :int64)
                                        (list "r" :out :int64))
                                  ls body)
                            (list (list :var ob) (g-lit n) (g-lit bt) (list :var d)) caller heap procs fuel)
                  (mv nil (copy-out (list (cons "r" d)) (mv-nth 1 (f-ex-list body (rt-fr) heap procs (1- fuel))) caller)
                      (mv-nth 2 (f-ex-list body (rt-fr) heap procs (1- fuel))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-ex-list undef-locals g-lit copy-out put)
           :expand ((:free (p) (f-invoke p (list (list :var ob) (g-lit n) (g-lit bt) (list :var d)) caller heap procs fuel))
                    (:free (ds as callee outs f) (f-bind ds as caller callee outs heap procs f))))))

; ---- the body's run, symbolically

(defmacro rt-fr0 ()
  '(undef-locals *rt-ls* (put "r" (cons :int64 :undef) (put "batching_" (cons :int64 bt) (put "n_" (cons :int64 n)
                                                                                           (put "hs" (list* :obj :inout key) nil))))))

(defthm dr-heap-at-put-same
  (implies (dr-heap-at heap key c hpg) (equal (put key (hs-rep c hpg) heap) heap))
  :hints (("Goal" :in-theory (e/d (dr-heap-at) (hs-rep)) :use ((:instance put-lkp-same (k key) (al heap))))))

(defconst *rt-call* (caddr (kadddr (car *rt-body*))))

; the CALL, on any frame binding its arguments
(defmacro rtv (nm) `(cddr (lkp ,nm fr)))
(defmacro rt-key () '(cdddr (lkp "hs" fr)))
(defmacro rt-hpg () '(hs-hpg (cdr (lkp (rt-key) heap))))
(defmacro rt-int (nm) `(and (consp (cdr (lkp ,nm fr))) (equal (cadr (lkp ,nm fr)) :int64)))

(defthm rt-call
  (implies (and (p-sorc-t procs b) (natp b)
                (equal (lkp "hs" fr) (list* "hs" :obj :inout (rt-key)))
                (rt-int "c_1") (rt-int "l_2") (rt-int "batching_") (rt-int "r")
                (natp (rtv "c_1")) (int64p (rtv "c_1")) (natp (rtv "l_2")) (<= (rtv "l_2") *hb40*) (int64p (rtv "batching_"))
                (hpgp (rt-hpg)) (hpg-rn-ok (rt-hpg)) (dr-heap-at heap (rt-key) (cdr (lkp (rt-key) heap)) (rt-hpg))
                (integerp k) (< (+ b (acl2-count *rt-call*)) k))
           (equal (f-ex *rt-call* fr heap procs k)
                  (let ((r (hpg-run-take-c (rtv "c_1") (rtv "l_2") (rtv "batching_") (rt-hpg))))
                    (mv :normal (put "r" (cons :int64 (car r)) fr)
                        (put (rt-key) (hs-rep (cdr (lkp (rt-key) heap)) (mv-nth 1 r)) heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (s-call-val-t obj-of) (f-ex hpgp hpg-rn-ok hs-rep put hpg-run-take-c p-sorc-t-necc))
           :use ((:instance p-sorc-t-necc (x *rt-call*) (fuel k)))
           :expand ((:free (e fr heap) (sv e fr heap))))))

; f-ex itself, opened by gen-cf's per-statement openers; the two calls by asg-t-fcall, the CALL by p-sorc-t
(defthm rt-run
  (implies (and (p-sorc-t procs b) (natp b) (<= *rt-b0* b) (rt-finds)
                (hpgp hpg) (hpg-rn-ok hpg) (natp n) (<= n *hb40*) (int64p bt)
                (dr-heap-at heap key comps hpg)
                (integerp k) (< (+ 10 b (acl2-count *rt-body*)) k))
           (let ((r (f-ex-list *rt-body* (rt-fr0) heap procs k)))
             (and (equal (mv-nth 0 r) :normal)
                  (equal (cdr (lkp "r" (mv-nth 1 r))) (cons :int64 (mv-nth 0 (hpg-run-take n bt hpg))))
                  (equal (mv-nth 2 r) (put key (hs-rep comps (mv-nth 1 (hpg-run-take n bt hpg))) heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (s-call-val-t f-asg-val-t comp-of int64p f-ex-list-open f-ex-if f-ex-assign-var
                            sv-ok-is-f-ev asg-t-fcall rt-call)
                           (f-ex f-ev f-ex-list f-invoke hpgp hpg-rn-ok hs-rep put hpg-run-take-c hpg-size-class p-sorc-t-necc
                            hpg-class-len))
           :expand ((:free (e fr heap) (sv e fr heap)) (:free (as fr heap) (svl-t as fr heap))
                    (:free (fr heap k) (f-ex-list nil fr heap procs k))))))

; ---- the theorem: hpg_run_take_c's correctness (p-sorc-t) the only hypothesis about the procedures past
; the generated hpg_size_class, hpg_class_len and hpg_n40; hs's heap entry holds the stobj as hs-rep
; lays it out, the result goes to the caller's d

(defthm hpg-run-take-fortran-correct
  (implies (and (p-sorc-t procs b) (natp b) (<= *rt-b0* b) (rt-finds)
                (hpgp hpg) (hpg-rn-ok hpg) (natp n) (<= n *hb40*) (int64p bt)
                (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (consp (cdr (lkp d caller))) (equal (cadr (lkp d caller)) :int64)
                (dr-heap-at heap key comps hpg)
                (integerp fuel) (< (+ 11 b (acl2-count *rt-body*)) fuel))
           (equal (f-invoke *rt-proc* (list (list :var ob) (g-lit n) (g-lit bt) (list :var d)) caller heap procs fuel)
                  (mv nil (put d (cons :int64 (mv-nth 0 (hpg-run-take n bt hpg))) caller)
                      (put key (hs-rep comps (mv-nth 1 (hpg-run-take n bt hpg))) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (int64p) (f-invoke f-ex-list hpg-run-take hpgp hpg-rn-ok g-lit undef-locals put
                                     f-invoke-sub-t rt-run p-sorc-t hs-rep))
           :expand ((:free (fr) (copy-out (list (cons "r" d)) fr caller)) (:free (fr) (copy-out nil fr caller)))
           :use (rt-proc-shape
                 (:instance rt-run (k (1- fuel)))
                 (:instance f-invoke-sub-t (o "hs") (cc "heap_state") (nm "hpg_run_take")
                            (rec (nth 2 *rt-proc*)) (ls *rt-ls*) (body *rt-body*))))))
