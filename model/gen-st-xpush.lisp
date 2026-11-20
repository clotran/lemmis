; gen-st-xpush: p-sorc-d, part 1 (GEN.md "Left of 4c step 3" (ii)). hpg_push
; (hs's components nobj/nvec/alive/nstr, the hp_* mark externs, a CALL of
; hpg_spush) run on hs's entry, as gen-st-xtake runs hpg_run_push; its CALL
; statement as hpg_scan_obj and hpg_scan_run write it (part 2, gen-st-xdrain).
; Route: the bespoke instance, not VALIDATION-DESIGN step 3's general module
; theorem -- GEN.md says why.

(in-package "ACL2")

(include-book "gen-st-xtake")

; ---- the procedures and the externs past xt-finds and nt-finds

(defconst *sp-proc* (mv-let (e ps) (g-st-module *heapg-st-raw* '(hpg-obj-at hpg-text-tag) '(hpg-spush) *heapg-xst*)
                      (and (not e) (car ps))))
(defconst *ps-proc* (find-proc "hpg_push" *heapg-xmod*))
(defconst *x-tt* (find-proc "hpg_text_tag"
                            (mv-let (e ps) (g-module (list (assoc-eq 'hpg-text-tag *heapg-st-raw*)) '(hpg-text-tag))
                              (if e nil ps))))

(assert-event (and (equal *sp-proc* *spush-proc*) *ps-proc* *x-tt*))

(defconst *xd-externs*
  `((:extern "hp_omark" :elem ,*h-omarki*) (:extern "hp_set_omark" :set-elem ,*h-omarki*)
    (:extern "hp_n_vec" :size ,*h-vmarki*) (:extern "hp_vmark" :elem ,*h-vmarki*) (:extern "hp_set_vmark" :set-elem ,*h-vmarki*)
    (:extern "hp_vlen" :elem ,*h-vleni*) (:extern "hp_voff" :elem ,*h-voffi*)
    (:extern "hp_n_str" :size ,*h-smarki*) (:extern "hp_set_smark" :set-elem ,*h-smarki*)
    (:extern "hp_atag" :elem ,*h-atagi*) (:extern "hp_aref" :elem ,*h-arefi*)))

(make-event
 `(defmacro xp-finds ()
    '(and (xt-finds) (nt-finds) ,@(xr-finds-fn *xd-externs*)
          (equal (find-proc "hpg_spush" procs) *sp-proc*) (equal (find-proc "hpg_push" procs) *ps-proc*)
          (equal (find-proc "hpg_text_tag" procs) *x-tt*))))

; the state fact (as nt-lens): the lengths one GC.f90 size answers are equal
; (hp_n_obj: okind, omark; hp_n_vec: vmark, vlen, voff; hp_n_arena: aival, atag, aref)
(defun xd-lens (h)
  (and (equal (len (nth *h-omarki* h)) (len (nth *h-okindi* h)))
       (equal (len (nth *h-vleni* h)) (len (nth *h-vmarki* h))) (equal (len (nth *h-voffi* h)) (len (nth *h-vmarki* h)))
       (equal (len (nth *h-atagi* h)) (len (nth *h-aivali* h))) (equal (len (nth *h-arefi* h)) (len (nth *h-aivali* h)))))

; ---- hs-rep: a component write is the stobj's update-nth; its reads

(defthm put-in-past
  (implies (and (not (equal k1 k2)) (consp (lkp k1 al)))
           (equal (put k1 v1 (put k2 v2 al)) (put k2 v2 (put k1 v1 al))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable put lkp))))

(defmacro hs-rep-put (name key i arr)
  `(progn
     (local (defthm ,(packn (list name '-in))
              (implies (and (not (equal ,key k2)) (consp (lkp ,key al)))
                       (equal (put ,key v1 (put k2 v2 al)) (put k2 v2 (put ,key v1 al))))
              :hints (("Goal" :use (:instance put-in-past (k1 ,key))))))
     (defthm ,(packn (list name '-ext)) (equal (hs-ext (update-nth ,i v h)) (hs-ext h))
       :hints (("Goal" :in-theory (enable hs-ext))))
     (defthm ,name (equal (put ,key ,(if arr '(cons :array v) 'v) (hs-rep c hpg)) (hs-rep c (update-nth ,i v hpg)))
       :hints (("Goal" :in-theory (e/d (hs-rep lkp-put-st put-put-same-st) (hs-ext hs-del put put-put-diff-st update-nth)))))))
(hs-rep-put hs-rep-err "err" 0 nil)
(hs-rep-put hs-rep-mtag "mtag" 10 t)
(hs-rep-put hs-rep-mref "mref" 11 t)
(hs-rep-put hs-rep-nobj "nobj" 13 nil)
(hs-rep-put hs-rep-nvec "nvec" 14 nil)
(hs-rep-put hs-rep-nstr "nstr" 15 nil)
(hs-rep-put hs-rep-alive "alive" 16 nil)

(defthm hs-rep-reads-d
  (and (equal (lkp "nobj" (hs-rep c hpg)) (cons "nobj" (nth 13 hpg)))
       (equal (lkp "nvec" (hs-rep c hpg)) (cons "nvec" (nth 14 hpg)))
       (equal (lkp "nstr" (hs-rep c hpg)) (cons "nstr" (nth 15 hpg)))
       (equal (lkp "alive" (hs-rep c hpg)) (cons "alive" (nth 16 hpg))))
  :hints (("Goal" :in-theory (e/d (hs-rep) (put hs-ext hs-del)))))

(defthm hpgp-arrs-x
  (implies (hpgp hpg)
           (and (h-omarkp (nth *h-omarki* hpg)) (h-vmarkp (nth *h-vmarki* hpg)) (h-vlenp (nth *h-vleni* hpg))
                (h-voffp (nth *h-voffi* hpg)) (h-smarkp (nth *h-smarki* hpg)) (h-okindp (nth *h-okindi* hpg))))
  :hints (("Goal" :in-theory (e/d (hpgp) (nth h-omarkp h-vmarkp h-vlenp h-voffp h-smarkp h-okindp)))))
(xr-tl h-omarkp-tl h-omarkp)
(xr-tl h-vmarkp-tl h-vmarkp)
(xr-tl h-vlenp-tl h-vlenp)
(xr-tl h-voffp-tl h-voffp)
(xr-tl h-smarkp-tl h-smarkp)
(xr-tl h-atagp-tl h-atagp)
(xr-tl h-arefp-tl h-arefp)

(defthm hpgp-xd-tl
  (implies (hpgp hpg)
           (and (true-listp (nth *h-omarki* hpg)) (true-listp (nth *h-vmarki* hpg)) (true-listp (nth *h-vleni* hpg))
                (true-listp (nth *h-voffi* hpg)) (true-listp (nth *h-smarki* hpg))
                (true-listp (nth *h-atagi* hpg)) (true-listp (nth *h-arefi* hpg))))
  :hints (("Goal" :in-theory (disable hpgp hpgp-arrs-x hpgp-arrs-d h-omarkp h-vmarkp h-vlenp h-voffp h-smarkp h-okindp h-atagp h-arefp)
           :use (hpgp-arrs-x hpgp-arrs-d))))
(in-theory (disable h-omarkp h-vmarkp h-vlenp h-voffp h-smarkp h-atagp h-arefp))
(defthm hpgp-ot-tl (implies (hpgp hpg) (and (true-listp (nth *h-otagi* hpg)) (true-listp (nth *h-orefi* hpg))))
  :hints (("Goal" :in-theory (disable hpgp hpgp-arrs-d h-otagp h-orefp h-otagp-tl h-orefp-tl)
           :use (hpgp-arrs-d (:instance h-otagp-tl (x (nth *h-otagi* hpg))) (:instance h-orefp-tl (x (nth *h-orefi* hpg)))))))
(defthm xd-hs-ext-tl (true-listp (hs-ext h)) :hints (("Goal" :in-theory (enable hs-ext))))
(defthm hpgp-okind-tl (implies (hpgp hpg) (true-listp (nth *h-okindi* hpg)))
  :hints (("Goal" :in-theory (disable hpgp hpgp-arrs h-okindp h-okindp-tl) :use (hpgp-arrs (:instance h-okindp-tl (x (nth *h-okindi* hpg)))))))

; an element within the array is an int64
(defmacro xd-elem (name i recog)
  `(defthm ,name
     (implies (and (hpgp hpg) (natp j) (< j (len (nth ,i hpg))))
              (and (integerp (nth j (nth ,i hpg)))
                   (<= -9223372036854775808 (nth j (nth ,i hpg))) (<= (nth j (nth ,i hpg)) 9223372036854775807)))
     :rule-classes nil
     :hints (("Goal" :in-theory (disable hpgp hpgp-arrs-x ,recog ,(packn (list recog '-nth)))
              :use (hpgp-arrs-x (:instance ,(packn (list recog '-nth)) (l (nth ,i hpg)) (i j)))))))
(xd-elem xd-omark-elem *h-omarki* h-omarkp)
(xd-elem xd-vmark-elem *h-vmarki* h-vmarkp)
(xd-elem xd-vlen-elem *h-vleni* h-vlenp)
(xd-elem xd-voff-elem *h-voffi* h-voffp)
(defthm xd-vlen-elem2
  (implies (and (hpgp hpg) (equal (len (nth *h-vleni* hpg)) (len (nth *h-voffi* hpg)))
                (natp j) (< j (len (nth *h-voffi* hpg))))
           (and (integerp (nth j (nth *h-vleni* hpg)))
                (<= -9223372036854775808 (nth j (nth *h-vleni* hpg))) (<= (nth j (nth *h-vleni* hpg)) 9223372036854775807)))
  :rule-classes nil
  :hints (("Goal" :use xd-vlen-elem)))
(defthm xd-vlen-int
  (implies (and (hpgp hpg) (equal (len (nth *h-vleni* hpg)) (len (nth *h-voffi* hpg)))
                (natp j) (< j (len (nth *h-voffi* hpg))))
           (not (equal (nth j (nth *h-vleni* hpg)) :undef)))
  :hints (("Goal" :use xd-vlen-elem)))

(defmacro hs-ext-nth (name i)
  `(defthm ,name (equal (nth ,i (hs-ext h)) (nth ,i h)) :hints (("Goal" :in-theory (enable hs-ext)))))
(hs-ext-nth xd-okind-nth *h-okindi*)
(hs-ext-nth xd-vlen-nth *h-vleni*)
(hs-ext-nth xd-voff-nth *h-voffi*)
(hs-ext-nth xd-otag-nth *h-otagi*)
(hs-ext-nth xd-oref-nth *h-orefi*)
(hs-ext-nth xd-atag-nth *h-atagi*)
(hs-ext-nth xd-aref-nth *h-arefi*)
(xr-ext-write xw-omark *h-omarki*)
(xr-ext-write xw-vmark *h-vmarki*)
(xr-ext-write xw-smark *h-smarki*)

; ---- hpg_spush on hs's entry

(defthm hpgp-err-int64
  (implies (hpgp hpg) (and (integerp (car hpg)) (<= -9223372036854775808 (car hpg)) (<= (car hpg) 9223372036854775807)))
  :rule-classes ((:rewrite) (:linear :corollary (implies (hpgp hpg) (and (<= -9223372036854775808 (car hpg)) (<= (car hpg) 9223372036854775807)))))
  :hints (("Goal" :in-theory (enable int64p) :use hpgp-facts)))

(defconst *sp-ls* (nth 4 *sp-proc*))
(defconst *sp-body* (nth 5 *sp-proc*))

(defthm sp-proc-shape
  (equal *sp-proc* (list :subroutine "hpg_spush" (nth 2 *sp-proc*)
                         (cons (list "hs" :inout "heap_state") (g-dummies '(tag ref))) *sp-ls* *sp-body*))
  :rule-classes nil)

(defmacro sp-fr () '(undef-locals *sp-ls* (fb '(tag ref) (list tag ref) (put "hs" (list* :obj :inout key) nil))))

(make-event
 `(defthm sp-run
    (implies (and (hpgp hpg) (hpg-ok hpg) (int64p tag) (int64p ref)
                  (dr-heap-at heap key cm hpg) (integerp k) (< 50 k))
             (let ((r (f-ex-list *sp-body* (sp-fr) heap procs k)))
               (and (equal (mv-nth 0 r) :normal)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (hpg-spush tag ref hpg)) heap)))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (hpg-spush update-h-mtagi update-h-mrefi update-h-msp update-h-err h-msp h-mtag-length
                              obj-of int64p fb hpg-ok hpg-lens comp-of read-elem)
                             (f-ev f-bind f-ex hs-rep hpgp dr-heap-at))
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      ,@(xr-expands (list *sp-proc*)))))))

(defthm sp-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (int64p tag) (int64p ref)
                (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (dr-heap-at heap key cm hpg) (integerp fuel) (< 60 fuel))
           (equal (f-invoke *sp-proc* (cons (list :var ob) (g-lits (list tag ref))) caller heap procs fuel)
                  (mv nil caller (put key (hs-rep cm (hpg-spush tag ref hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(int64p natp int64-listp len car-cons cdr-cons (int64-listp) (len) (g-dummies)
                                        (nth) (cons) (equal) (binary-+) (unary--))
                                      (theory 'minimal-theory))
           :use (sp-proc-shape (:instance sp-run (k (1- fuel)))
                 (:instance f-invoke-sub-d (ks (list tag ref)) (vs '(tag ref)) (o "hs") (c "heap_state")
                            (nm "hpg_spush") (rec (nth 2 *sp-proc*)) (ls *sp-ls*) (body *sp-body*))))))

; a CALL of a heap procedure on hs's canonical entry (an hs-rep of an hpg-ok stobj), its codes int64
(defmacro xd-obj ()
  '(and (not (mv-nth 0 (obj-of ob fr))) (eq (mv-nth 2 (obj-of ob fr)) :inout)
        (dr-heap-at heap (xk-key) (xk-e) (xk-hpg)) (hpgp (xk-hpg)) (hpg-ok (xk-hpg))))
(defmacro xd-code (cc) `(and (xk-ok ,cc) (int64p (xk-v ,cc))))

(defthm svs-is-2
  (implies (and (not (mv-nth 0 (sv x1 fr heap))) (not (mv-nth 0 (sv x2 fr heap))))
           (svs-is (list x1 x2) (list (mv-nth 1 (sv x1 fr heap)) (mv-nth 1 (sv x2 fr heap))) fr heap))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable svs-is))))

(defun-nx scv-sp (ob c1 c2 fr heap)
  (if (and (xd-obj) (xd-code c1) (xd-code c2))
      (mv nil fr (put (xk-key) (hs-rep (xk-e) (hpg-spush (xk-v c1) (xk-v c2) (xk-hpg))) heap))
    (mv :orc fr heap)))

(defthm scv-sp-cond
  (implies (not (mv-nth 0 (scv-sp ob c1 c2 fr heap)))
           (and (xd-obj) (xd-code c1) (xd-code c2)
                (equal (cdr (lkp ob fr)) (list* :obj :inout (xk-key)))
                (int64-listp (list (xk-v c1) (xk-v c2)))
                (equal (mv-nth 1 (scv-sp ob c1 c2 fr heap)) fr)
                (equal (mv-nth 2 (scv-sp ob c1 c2 fr heap))
                       (put (xk-key) (hs-rep (xk-e) (hpg-spush (xk-v c1) (xk-v c2) (xk-hpg))) heap))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(scv-sp mv-nth car-cons cdr-cons eq not int64-listp (int64-listp) (int64p) (zp) (equal) (cons))
                                      (theory 'minimal-theory))
           :use ((:instance obj-of-binding (caller fr))))))

(defthm sp-okc
  (implies (and (not (mv-nth 0 (scv-sp ob c1 c2 fr heap))) (integerp fuel) (< (+ 70 (acl2-count (list c1 c2))) fuel))
           (equal (f-invoke *sp-proc* (list (list :var ob) c1 c2) fr heap procs fuel)
                  (mv nil fr (mv-nth 2 (scv-sp ob c1 c2 fr heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(len (len) (g-dummies) (kar) (nth) (true-list-fix) (equal) car-cons cdr-cons
                                        (:type-prescription acl2-count))
                                      (theory 'minimal-theory))
           :use (scv-sp-cond sp-proc-shape
                 (:instance svs-is-2 (x1 c1) (x2 c2))
                 (:instance f-invoke-st-codes (p *sp-proc*) (d '("hs" :inout "heap_state")) (vs '(tag ref))
                            (a (list :var ob)) (cs (list c1 c2)) (ks (list (xk-v c1) (xk-v c2))) (caller fr))
                 (:instance sp-ok (caller fr) (key (xk-key)) (cm (xk-e)) (hpg (xk-hpg)) (tag (xk-v c1)) (ref (xk-v c2)))))))

(defthm xd-ex-sp
  (implies (and (equal (find-proc "hpg_spush" procs) *sp-proc*)
                (not (mv-nth 0 (scv-sp ob c1 c2 fr heap))) (integerp fuel) (< (+ 71 (acl2-count (list c1 c2))) fuel))
           (equal (f-ex (list :call "hpg_spush" (list (list :var ob) c1 c2)) fr heap procs fuel)
                  (mv :normal fr (mv-nth 2 (scv-sp ob c1 c2 fr heap)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-invoke sp-okc scv-sp)
           :expand ((f-ex (list :call "hpg_spush" (list (list :var ob) c1 c2)) fr heap procs fuel))
           :use ((:instance sp-okc (fuel (1- fuel)))))))

; ---- hpg_push on hs's entry

(defconst *ps-ls* (nth 4 *ps-proc*))
(defconst *ps-body* (nth 5 *ps-proc*))

(defthm ps-proc-shape
  (equal *ps-proc* (list :subroutine "hpg_push" (nth 2 *ps-proc*)
                         (cons (list "hs" :inout "heap_state") (g-dummies '(tag ref))) *ps-ls* *ps-body*))
  :rule-classes nil)

(defmacro ps-fr () '(undef-locals *ps-ls* (fb '(tag ref) (list tag ref) (put "hs" (list* :obj :inout key) nil))))

(defconst *ps-s0* (car *ps-body*))
(defconst *ps-s1* (car (nth 3 *ps-s0*)))
(defconst *ps-a* (nth 2 *ps-s1*))
(defconst *ps-s2* (car (nth 3 *ps-s1*)))
(defconst *ps-b* (nth 2 *ps-s2*))
(defconst *ps-s3* (car (nth 3 *ps-s2*)))
(defconst *ps-c* (nth 2 *ps-s3*))
(assert-event (and (equal *ps-body* (list *ps-s0*)) (equal (nth 2 *ps-s0*) nil) (equal (nth 3 *ps-s3*) nil)))

; the stobj facts kept by hpg_push's writes: a mark set, a counter put within 2^40
(defmacro xd-upd-arr (name i recog)
  `(defthm ,name
     (implies (and (hpgp hpg) (natp j) (< j (len (nth ,i hpg))) (integerp v) (<= -9223372036854775808 v) (<= v 9223372036854775807))
              (and (hpgp (update-nth ,i (update-nth j v (nth ,i hpg)) hpg))
                   (equal (hpg-ok (update-nth ,i (update-nth j v (nth ,i hpg)) hpg)) (hpg-ok hpg))))
     :hints (("Goal" :in-theory (e/d (hpgp hpg-ok hpg-lens ,recog) (nth update-nth))))))
(xd-upd-arr xd-upd-omark *h-omarki* h-omarkp)
(xd-upd-arr xd-upd-vmark *h-vmarki* h-vmarkp)
(xd-upd-arr xd-upd-smark *h-smarki* h-smarkp)

(defmacro xd-upd-cnt (name i)
  `(defthm ,name
     (implies (and (hpgp hpg) (hpg-ok hpg) (natp v) (<= v *hb40*))
              (and (hpgp (update-nth ,i v hpg)) (hpg-ok (update-nth ,i v hpg))))
     :hints (("Goal" :in-theory (e/d (hpgp hpg-ok hpg-lens) (nth update-nth))))))
(xd-upd-cnt xd-upd-nobj 13)
(xd-upd-cnt xd-upd-nvec 14)
(xd-upd-cnt xd-upd-nstr 15)
(xd-upd-cnt xd-upd-alive 16)

(defthm xd-int-plus (implies (and (integerp a) (integerp b)) (integerp (+ a b))))

(defmacro ps-finds ()
  '(and (equal (find-proc "hp_n_obj" procs) (nth 5 *nt-externs*))
        (equal (find-proc "hp_omark" procs) (nth 0 *xd-externs*)) (equal (find-proc "hp_set_omark" procs) (nth 1 *xd-externs*))
        (equal (find-proc "hp_n_vec" procs) (nth 2 *xd-externs*)) (equal (find-proc "hp_vmark" procs) (nth 3 *xd-externs*))
        (equal (find-proc "hp_set_vmark" procs) (nth 4 *xd-externs*)) (equal (find-proc "hp_vlen" procs) (nth 5 *xd-externs*))
        (equal (find-proc "hp_n_str" procs) (nth 7 *xd-externs*)) (equal (find-proc "hp_set_smark" procs) (nth 8 *xd-externs*))
        (equal (find-proc "hpg_add" procs) *x-add*) (equal (find-proc "hpg_text_tag" procs) *x-tt*)
        (equal (find-proc "hpg_spush" procs) *sp-proc*)))

(defmacro ps-hyps ()
  '(and (ps-finds) (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (int64p tag) (int64p ref) (< 0 ref)
        (dr-heap-at heap key cm hpg) (integerp k) (< 200 k)))

(defmacro ps-thy (&rest en)
  `(e/d (,@en obj-of int64p fb comp-of read-elem ext-op ext-read-p ext-write-p ext-dums hpg-ok hpg-add scv-sp)
        (f-ev f-bind f-ex f-invoke hs-rep hpgp hpg-spush dr-heap-at)))

(make-event
 `(defthm ps-a-run
    (implies (and (ps-hyps) (equal tag 8))
             (let ((r (f-ex-list *ps-a* (ps-fr) heap procs k)))
               (and (equal (mv-nth 0 r) :normal)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (hpg-push tag ref hpg)) heap)))))
    :hints (("Goal" :do-not-induct t
             :in-theory (ps-thy hpg-push update-h-omarki update-h-nobj h-omarki h-omark-length h-nobj)
             :use ((:instance xd-omark-elem (j ref)))
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      (:free (as cl h k) (f-invoke ',*x-add* as cl h procs k))
                      ,@(xr-expands (list (list :subroutine "a" nil nil nil *ps-a*) *x-add*)))))))

(make-event
 `(defthm ps-b-run
    (implies (and (ps-hyps) (equal tag 9))
             (let ((r (f-ex-list *ps-b* (ps-fr) heap procs k)))
               (and (equal (mv-nth 0 r) :normal)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (hpg-push tag ref hpg)) heap)))))
    :hints (("Goal" :do-not-induct t
             :cases ((integerp (nth ref (nth *h-vleni* hpg))))
             :use ((:instance xd-vmark-elem (j ref)) (:instance xd-vlen-elem2 (j ref)))
             :in-theory (ps-thy hpg-push update-h-vmarki update-h-nvec update-h-alive h-vmarki h-vleni h-vmark-length
                                h-vlen-length h-nvec h-alive)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      (:free (as cl h k) (f-invoke ',*x-add* as cl h procs k))
                      ,@(xr-expands (list (list :subroutine "b" nil nil nil *ps-b*) *x-add*)))))))

(make-event
 `(defthm ps-c-run
    (implies (and (ps-hyps) (not (equal tag 8)) (not (equal tag 9)))
             (let ((r (f-ex-list (list *ps-s3*) (ps-fr) heap procs k)))
               (and (equal (mv-nth 0 r) :normal)
                    (equal (mv-nth 2 r) (put key (hs-rep cm (hpg-push tag ref hpg)) heap)))))
    :hints (("Goal" :do-not-induct t
             :cases ((equal tag 5) (equal tag 6) (equal tag 7) (equal tag 11) (equal tag 12) (equal tag 13) (equal tag 15)
                     (not (member tag '(5 6 7 11 12 13 15))))
             :in-theory (ps-thy hpg-push hpg-text-tag update-h-smarki update-h-nstr h-smark-length h-nstr)
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))
                      (:free (as cl h k) (f-invoke ',*x-add* as cl h procs k))
                      (:free (as cl h k) (f-invoke ',*x-tt* as cl h procs k))
                      ,@(xr-expands (list (list :subroutine "c" nil nil nil (list *ps-s3*)) *x-add* *x-tt*)))))))

(defthm xd-put-same (implies (dr-heap-at heap key cm hpg) (equal (put key (hs-rep cm hpg) heap) heap))
  :hints (("Goal" :in-theory (e/d (dr-heap-at) (hs-rep)) :induct (put key v heap))))

(defthm hpg-push-nonpos (implies (not (< 0 ref)) (equal (hpg-push tag ref hpg) hpg))
  :hints (("Goal" :in-theory (enable hpg-push))))

(defthm ps-fr-lkp
  (and (equal (lkp "tag_" (ps-fr)) (list* "tag_" :int64 tag)) (equal (lkp "ref_" (ps-fr)) (list* "ref_" :int64 ref)))
  :hints (("Goal" :in-theory (enable fb))))

(defthm ps-run
  (implies (and (ps-finds) (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (int64p tag) (int64p ref)
                (dr-heap-at heap key cm hpg) (integerp k) (< 210 k))
           (let ((r (f-ex-list *ps-body* (ps-fr) heap procs k)))
             (and (equal (mv-nth 0 r) :normal)
                  (equal (mv-nth 2 r) (put key (hs-rep cm (hpg-push tag ref hpg)) heap)))))
  :hints (("Goal" :do-not-induct t
           :cases ((not (< 0 ref)) (equal tag 8) (equal tag 9))
           :in-theory (e/d (int64p) (f-ex f-ex-list f-ex-list-open f-ex-if f-ev hs-rep hpgp hpg-ok xd-lens hpg-push dr-heap-at put
                                    undef-locals fb))
           :expand ((:free (fr h k) (f-ex *ps-s0* fr h procs k)) (:free (fr h k) (f-ex *ps-s1* fr h procs k))
                    (:free (fr h k) (f-ex *ps-s2* fr h procs k))
                    (:free (fr h k) (f-ex-list (list *ps-s0*) fr h procs k)) (:free (fr h k) (f-ex-list (list *ps-s1*) fr h procs k))
                    (:free (fr h k) (f-ex-list (list *ps-s2*) fr h procs k)) (:free (fr h k) (f-ex-list nil fr h procs k))
                    (:free (e fr h) (sv e fr h))))))

(defthm ps-ok
  (implies (and (ps-finds) (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (int64p tag) (int64p ref)
                (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (dr-heap-at heap key cm hpg) (integerp fuel) (< 220 fuel))
           (equal (f-invoke *ps-proc* (cons (list :var ob) (g-lits (list tag ref))) caller heap procs fuel)
                  (mv nil caller (put key (hs-rep cm (hpg-push tag ref hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(int64p natp int64-listp len car-cons cdr-cons (int64-listp) (len) (g-dummies)
                                        (nth) (cons) (equal) (binary-+) (unary--))
                                      (theory 'minimal-theory))
           :use (ps-proc-shape (:instance ps-run (k (1- fuel)))
                 (:instance f-invoke-sub-d (ks (list tag ref)) (vs '(tag ref)) (o "hs") (c "heap_state")
                            (nm "hpg_push") (rec (nth 2 *ps-proc*)) (ls *ps-ls*) (body *ps-body*))))))

; the CALL as hpg_scan_obj and hpg_scan_run write it: the tag and ref read from two extern arrays at j
(defmacro xd-ex-ps-thm (name xt xr var ti ri et er)
  `(make-event (xd-ex-ps-form ',name ,xt ,xr ,var ',ti ',ri ',et ',er)))
(defun xd-rd-form (name xt var ti et)
  (declare (xargs :mode :program))
  `(defthm ,name
     (implies (and (equal (find-proc ,xt procs) ',et) (dr-hs-at fr key) (rf-v-at fr ,var j) (natp j) (< j (len (nth ,ti hpg)))
                   (hpgp hpg) (hpg-ok hpg) (dr-heap-at heap key cm hpg) (integerp fuel) (< 3 fuel))
              (equal (f-ev '(:xcall ,xt "hs" ((:var ,var))) fr heap procs fuel) (mv nil (nth j (nth ,ti hpg)))))
     :hints (("Goal" :in-theory (e/d (obj-of int64p hpg-ok hpg-lens) (f-ev f-ev-xcall-elem hpgp hs-rep dr-hs-at dr-heap-at rf-v-at))
              :use ((:instance f-ev-xcall-elem (nm ,xt) (o "hs") (x ,var) (p ',et)))))))

(defun xd-ex-ps-form (name xt xr var ti ri et er)
  (declare (xargs :mode :program))
  `(progn ,(xd-rd-form (packn (list name '-rt)) xt var ti et) ,(xd-rd-form (packn (list name '-rr)) xr var ri er)
   (defthm ,name
     (implies (and (ps-finds) (equal (find-proc "hpg_push" procs) *ps-proc*)
                   (equal (find-proc ,xt procs) ',et) (equal (find-proc ,xr procs) ',er)
                   (dr-hs-at fr key) (rf-v-at fr ,var j) (natp j) (< j (len (nth ,ti hpg))) (< j (len (nth ,ri hpg)))
                   (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (dr-heap-at heap key cm hpg) (integerp fuel) (< 300 fuel))
              (equal (f-ex '(:call "hpg_push" ((:var "hs") (:xcall ,xt "hs" ((:var ,var))) (:xcall ,xr "hs" ((:var ,var)))))
                           fr heap procs fuel)
                     (mv :normal fr (put key (hs-rep cm (hpg-push (nth j (nth ,ti hpg)) (nth j (nth ,ri hpg)) hpg)) heap))))
     :hints (("Goal" :do-not-induct t
              :in-theory (e/d (obj-of int64p g-lits) (f-invoke f-ev f-bind ps-ok hs-rep hpgp hpg-ok xd-lens hpg-push dr-heap-at put g-lit))
              :expand ((f-ex '(:call "hpg_push" ((:var "hs") (:xcall ,xt "hs" ((:var ,var))) (:xcall ,xr "hs" ((:var ,var)))))
                             fr heap procs fuel)
                       (:free (as ce k) (f-bind ',(nth 3 *ps-proc*) as fr ce nil heap procs k))
                       (:free (as ce k) (f-bind ',(cdr (nth 3 *ps-proc*)) as fr ce nil heap procs k))
                       (:free (as ce k) (f-bind ',(cddr (nth 3 *ps-proc*)) as fr ce nil heap procs k))
                       (:free (as ce k) (f-bind nil as fr ce nil heap procs k)))
              :use ((:instance f-invoke-same-bind (p *ps-proc*) (caller fr) (fuel (1- fuel))
                               (a1 '((:var "hs") (:xcall ,xt "hs" ((:var ,var))) (:xcall ,xr "hs" ((:var ,var)))))
                               (a2 (cons '(:var "hs") (g-lits (list (nth j (nth ,ti hpg)) (nth j (nth ,ri hpg)))))))
                    (:instance ps-ok (caller fr) (ob "hs") (fuel (1- fuel))
                               (tag (nth j (nth ,ti hpg))) (ref (nth j (nth ,ri hpg))))))))))

(xd-ex-ps-thm xd-ex-ps-obj "hp_otag" "hp_oref" "j_2" *h-otagi* *h-orefi*
              (:extern "hp_otag" :elem 1) (:extern "hp_oref" :elem 2))
