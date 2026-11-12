; gen-st-spush: clotran's hpg-spush (a stobj update: two array writes, a
; field write, and the bounds error) carried to hpg-spush-fortran-correct.
; The definitions are copied from clotran's model/heapg.lisp (check-gen.bb
; checks the copies, the accessors included, against clotran's certified
; book); the procedure is gen-st's g-st-module output.

(in-package "ACL2")

(include-book "gen-st")

(defconst *hb40* 1099511627776)

(defstobj hpg
  (h-err :type (signed-byte 64) :initially 0)
  (h-otag :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-oref :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-omark :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-voff :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vlen :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vmark :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-atag :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-aref :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-smark :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-mtag :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-mref :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-msp :type (signed-byte 64) :initially 0)
  (h-nobj :type (signed-byte 64) :initially 0)
  (h-nvec :type (signed-byte 64) :initially 0)
  (h-nstr :type (signed-byte 64) :initially 0)
  (h-alive :type (signed-byte 64) :initially 0)
  ;; THE SWEEP (stage 1b): each pool's free flags and free list, the
  ;; arena's words' third field (a free run's link) and its size classes'
  ;; heads, and the two things the runtime does as a slot is freed -- an
  ;; object's finalizer, a text's storage released -- as writes to h-ofin
  ;; and h-srel
  (h-okind :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-ofree :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-onext :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vfree :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vnext :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-sfree :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-snext :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-aival :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-chead :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-ofin :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-srel :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-ohead :type (signed-byte 64) :initially 0)
  (h-vhead :type (signed-byte 64) :initially 0)
  (h-shead :type (signed-byte 64) :initially 0)
  (h-nswo :type (signed-byte 64) :initially 0)
  (h-nswv :type (signed-byte 64) :initially 0)
  (h-nsws :type (signed-byte 64) :initially 0)
  (h-afree :type (signed-byte 64) :initially 0)
  ;; ALLOCATION (stage 1b): how far each pool is used and how big it is,
  ;; and the calling thread's batch of free slots, 1-based as GC.f90's
  (h-oused :type (signed-byte 64) :initially 0)
  (h-ocap :type (signed-byte 64) :initially 0)
  (h-ob :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-nob :type (signed-byte 64) :initially 0)
  (h-vused :type (signed-byte 64) :initially 0)
  (h-vcap :type (signed-byte 64) :initially 0)
  (h-vb :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-nvb :type (signed-byte 64) :initially 0)
  (h-sused :type (signed-byte 64) :initially 0)
  (h-scap :type (signed-byte 64) :initially 0)
  (h-sb :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-nsb :type (signed-byte 64) :initially 0)
  ;; THE ARENA's allocation (stage 1b): how far it is used and how big it
  ;; is, runs reused and fresh and words handed out since the last
  ;; collection, and the calling thread's batches of runs, class c's k-th at
  ;; (c-1)*64 + k
  (h-aused :type (signed-byte 64) :initially 0)
  (h-acap :type (signed-byte 64) :initially 0)
  (h-areu :type (signed-byte 64) :initially 0)
  (h-afre :type (signed-byte 64) :initially 0)
  (h-asince :type (signed-byte 64) :initially 0)
  (h-rb :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-nrb :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  ;; THE SEQ OPERATIONS (stage 2, model/heapsq.lisp): an object's first
  ;; integer field, a list's count or a lazy cell's state
  (h-oi1 :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  ;; AGING (stage 1c, model/heapgn.lisp): an object or run aged by the last
  ;; collection, survived once and young again
  (h-oaged :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vaged :type (array (signed-byte 64) (0)) :initially 0 :resizable t))

(defun hpg-lens (hpg)
  (declare (xargs :stobjs hpg))
  (and (<= (h-otag-length hpg) *hb40*) (<= (h-oref-length hpg) *hb40*) (<= (h-omark-length hpg) *hb40*)
       (<= (h-voff-length hpg) *hb40*) (<= (h-vlen-length hpg) *hb40*) (<= (h-vmark-length hpg) *hb40*)
       (<= (h-atag-length hpg) *hb40*) (<= (h-aref-length hpg) *hb40*) (<= (h-smark-length hpg) *hb40*)
       (<= (h-mtag-length hpg) *hb40*) (<= (h-mtag-length hpg) (h-mref-length hpg))))

(defun hpg-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-lens hpg)
       (natp (h-msp hpg)) (<= (h-msp hpg) (h-mtag-length hpg))
       (natp (h-nobj hpg)) (<= (h-nobj hpg) *hb40*)
       (natp (h-nvec hpg)) (<= (h-nvec hpg) *hb40*)
       (natp (h-nstr hpg)) (<= (h-nstr hpg) *hb40*)
       (natp (h-alive hpg)) (<= (h-alive hpg) *hb40*)))

(defun hpg-spush (tag ref hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (and (hpg-ok hpg) (integerp tag) (integerp ref)
                                         (<= -9223372036854775808 tag) (< tag 9223372036854775808)
                                         (<= -9223372036854775808 ref) (< ref 9223372036854775808))))
  (let ((sp (h-msp hpg)))
    (if (< sp (h-mtag-length hpg))
        (let* ((hpg (update-h-mtagi sp tag hpg))
               (hpg (update-h-mrefi sp ref hpg)))
          (update-h-msp (+ 1 sp) hpg))
      (update-h-err 1 hpg))))

; ---- the procedure

(defconst *spush-proc* (mv-let (e ps) (g-st-module *spush-raw* nil '(hpg-spush) *heapg-st*) (and (not e) (car ps))))

(defthm spush-proc-is-generated
  (equal (mv-nth 1 (g-st-module *spush-raw* nil '(hpg-spush) *heapg-st*)) (list *spush-proc*))
  :rule-classes nil)

; comps with those four replaced by the stobj's
(defun hs-put (comps hpg)
  (put "msp" (nth 12 hpg) (put "mref" (cons :array (nth 11 hpg)) (put "mtag" (cons :array (nth 10 hpg))
                                                                       (put "err" (nth 0 hpg) comps)))))

(defthm lkp-put-st
  (equal (lkp n (put k v al)) (if (equal n k) (cons k v) (lkp n al))))

(defthm put-same-st
  (implies (equal (lkp k al) (cons k v)) (equal (put k v al) al)))

(defthm put-put-same-st
  (equal (put k v1 (put k v2 al)) (put k v1 al)))

; existing components' puts sorted by name (constant names only)
(defthm put-put-diff-st
  (implies (and (syntaxp (and (quotep k1) (quotep k2) (stringp (cadr k1)) (stringp (cadr k2))
                              (string< (cadr k2) (cadr k1))))
                (not (equal k1 k2)) (consp (lkp k1 al)) (consp (lkp k2 al)))
           (equal (put k1 v1 (put k2 v2 al)) (put k2 v2 (put k1 v1 al))))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm h-mtagp-true-listp (implies (h-mtagp x) (true-listp x)) :rule-classes :forward-chaining)
(defthm h-mrefp-true-listp (implies (h-mrefp x) (true-listp x)) :rule-classes :forward-chaining)

(defthm hpgp-facts
  (implies (hpgp hpg)
           (and (int64p (nth 0 hpg)) (int64p (nth 12 hpg))
                (true-listp (nth 10 hpg)) (true-listp (nth 11 hpg))))
  :hints (("Goal" :in-theory (enable hpgp))))

(in-theory (disable hpgp))

; the bounds error: mref shorter than mtag (which hpg-ok forbids), msp
; in mtag but past mref -- hs%mref(i_4) is outside its array
(defthm hpg-spush-fortran-bounds
  (implies (and (hpgp hpg) (int64p tag) (int64p ref)
                (natp (nth 12 hpg)) (< (nth 12 hpg) (len (nth 10 hpg))) (<= (len (nth 11 hpg)) (nth 12 hpg))
                (<= (len (nth 10 hpg)) *hb40*)
                (consp (lkp "err" comps)) (consp (lkp "mtag" comps)) (consp (lkp "mref" comps)) (consp (lkp "msp" comps))
                (integerp fuel) (< 100 fuel))
           (equal (f-invoke *spush-proc* (list '(:var "hs") (g-lit tag) (g-lit ref))
                            (put "hs" (list* :obj :inout key) frame) (put key (hs-put comps hpg) heap) procs fuel)
                  (mv :bounds nil (put key (hs-put comps hpg) heap))))
  :hints (("Goal" :do-not-induct t :expand ((:free (x frame heap procs fuel) (f-ev x frame heap procs fuel))
                      (:free (x frame heap procs fuel) (f-ex x frame heap procs fuel))
                      (:free (x frame heap procs fuel) (f-ex-list x frame heap procs fuel))
                      (:free (ds as caller callee outs heap procs fuel) (f-bind ds as caller callee outs heap procs fuel))
                      (:free (p as caller heap procs fuel) (f-invoke p as caller heap procs fuel)))
      :in-theory (e/d (hpg-ok hpg-lens) (f-ev f-ex f-ex-list f-bind f-invoke nth update-nth)))))

; the general theorem, included after the symbolic-execution proof above
; (whose theory its rules would change)
(include-book "gen-stfn")

;; ---- hpg-spush-fortran-correct, an instance of g-st-fn-sem
;
; st restricted to the roles hpg-spush's body uses (and its :sub entry):
; the procedure is the same (spush-proc-small), and st-ok/st-wf then ask
; only of err, msp, mtag and mref -- not, say, that every array's length
; is an int64, which hpg-ok does not say of the ones it does not bound.
(defconst *spush-st*
  (append '((hpg :stobj "hs" "heap_state") (h-err :field "hs" "err") (update-h-err :set "hs" "err")
            (h-msp :field "hs" "msp") (update-h-msp :set "hs" "msp") (h-mtag-length :size "hs" "mtag")
            (update-h-mtagi :seti "hs" "mtag") (update-h-mrefi :seti "hs" "mref"))
          (g-st-subs *spush-raw*)))

(defconst *spush-body* (nth 4 (car *spush-raw*)))

(defthm spush-proc-small
  (and (equal (car *spush-raw*) (list 'hpg-spush '(tag ref hpg) '(hpg) t *spush-body*))
       (equal (mv-list 2 (g-st-fn (car *spush-raw*) (g-defs *spush-raw*) (g-sigs *spush-raw* nil) *spush-st*))
              (list nil *spush-proc*)))
  :rule-classes nil)

(defthm h-mtagp-int64 (implies (h-mtagp x) (int64-listp x)) :hints (("Goal" :in-theory (enable int64p))))
(defthm h-mrefp-int64 (implies (h-mrefp x) (int64-listp x)) :hints (("Goal" :in-theory (enable int64p))))

(defthm spush-st-ok
  (implies (and (hpgp hpg) (hpg-ok hpg))
           (and (st-ok *spush-st* "hs" (hs-put comps hpg)) (st-wf *spush-st* (hs-put comps hpg))))
  :hints (("Goal" :in-theory (e/d (st-ok st-wf hpg-ok hpg-lens hpgp int64p) (nth))
           :expand ((st-ok *spush-st* "hs" (hs-put comps hpg)) (st-wf *spush-st* (hs-put comps hpg))))))

; a-st on the body: hpg-spush, on hs-put's components
(defthm spush-a-st
  (implies (and (hpgp hpg) (hpg-ok hpg) (int64p tag) (int64p ref)
                (consp (lkp "err" comps)) (consp (lkp "mtag" comps)) (consp (lkp "mref" comps)) (consp (lkp "msp" comps)))
           (equal (a-st *spush-body* (list (cons 'tag tag) (cons 'ref ref)) (hs-put comps hpg) *spush-st* nil 100)
                  (mv nil (hs-put comps (hpg-spush tag ref hpg)))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (x env s n) (a-st x env s *spush-st* nil n))
                    (:free (x env s n) (a-sx x env s *spush-st* nil n))
                    (:free (x env s n) (a-sx-list x env s *spush-st* nil n))
                    (:free (v x env s0 s n) (a-st-args v x env s0 s *spush-st* nil n)))
           :in-theory (e/d (hpg-ok hpg-lens) (a-st a-sx a-sx-list a-st-args nth update-nth)))))

; on a stobj satisfying hpg-ok (the guard), the subroutine updates hs as
; hpg-spush updates hpg, at every fuel past 196 (g-st-fn-sem's bound: 6,
; the two values, the body's size 188): hs's object any components comps
; with err, mtag, mref and msp the stobj's (hs-put), and only those four
; changed
(defthm hpg-spush-fortran-correct
  (implies (and (hpgp hpg) (hpg-ok hpg) (int64p tag) (int64p ref)
                (consp (lkp "err" comps)) (consp (lkp "mtag" comps)) (consp (lkp "mref" comps)) (consp (lkp "msp" comps))
                (integerp fuel) (< 196 fuel))
           (equal (f-invoke *spush-proc* (list '(:var "hs") (g-lit tag) (g-lit ref))
                            (put "hs" (list* :obj :inout key) frame) (put key (hs-put comps hpg) heap) procs fuel)
                  (mv nil (put "hs" (list* :obj :inout key) frame) (put key (hs-put comps (hpg-spush tag ref hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (int64-listp) (g-st-fn-sem spush-a-st spush-st-ok g-st-fn a-st f-invoke hs-put hpg-spush hpg-ok hpgp))
           :use (spush-proc-small spush-a-st spush-st-ok
                 (:instance g-st-fn-sem (fn 'hpg-spush) (formals '(tag ref hpg)) (sv 'hpg) (x *spush-body*)
                            (gdefs (g-defs *spush-raw*)) (sigs (g-sigs *spush-raw* nil)) (st *spush-st*)
                            (o "hs") (c "heap_state") (ob "hs") (caller (put "hs" (list* :obj :inout key) frame))
                            (heap (put key (hs-put comps hpg) heap)) (ks (list tag ref)) (s (hs-put comps hpg))
                            (defs nil) (n 100))))))
