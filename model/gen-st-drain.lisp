; gen-st-drain: hpg-drain-fortran-correct (GEN.md "What remains" 4b), the
; subroutine tail loop. hpg-drain pops the mark stack, CALLing hpg_scan_obj or
; hpg_scan_vec on each entry; both read and write `hp_*` externs (4c), so
; their correctness is a named hypothesis, `p-sorc-d`: gen-stcall's p-sorc on
; a concrete oracle s-call-val-d answering each callee's ACL2 value.
;
; The externs' state: fsem has no externs, so the heap entry of hs carries
; them as a ghost component "%ext" (hs-rep: the twelve heap_state fields from
; the stobj, "%ext" the rest of it). hs-hpg reads the stobj back from an
; entry. The oracle runs the callee on hs-hpg of the entry and answers hs-rep
; of the result: the callees' externs change (omark, vmark, smark), so a
; fixed extern state (gen-st-ntail's hpg0) does not do here.
;
; The loop: sxc (gen-stcall) copied as sxc-d on the oracle, one iteration of
; the DO's body run symbolically (dr-iter), the DO by induction on fuel
; (dr-loop), then f-invoke.

(in-package "ACL2")

(include-book "gen-st-ntail")
(include-book "gen-stcall")

; gen-stinst's functional-instance hint (that book clashes with gen-st-ntail's includes)
(defun dr-occ (syms x) (declare (xargs :mode :program))
  (if (atom x) (member-eq x syms) (or (dr-occ syms (car x)) (dr-occ syms (cdr x)))))

(defun dr-hint (id clause main wits sks hdef hnecc hother)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :pool-lst) nil) (equal (access clause-id id :primes) 0)
       (equal (len (access clause-id id :case-lst)) 1)
       (cond ((dr-occ main clause) (quote (:in-theory (theory (quote minimal-theory)))))
             ((dr-occ wits clause) hdef)
             ((dr-occ sks clause) hnecc)
             (t hother))))

; ---- clotran's definitions (heapg.lisp), compared by check-gen

(defun hpg-add (n k)
  (declare (xargs :guard (and (natp n) (<= n 1099511627776) (natp k) (<= k 1099511627776))))
  (let ((s (+ (nfix n) (nfix k)))) (if (< s 1099511627776) s 1099511627776)))

(defun hpg-text-tag (tag)
  (declare (xargs :guard t))
  (or (equal tag 5) (equal tag 6) (equal tag 7) (equal tag 11) (equal tag 12) (equal tag 13) (equal tag 15)))

(defun hpg-push (tag ref hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (and (hpg-ok hpg) (sb64p tag) (sb64p ref))))
  (cond ((not (< 0 ref)) hpg)
        ((equal tag 8)
         (if (and (< ref (h-omark-length hpg)) (equal (h-omarki ref hpg) 0))
             (let* ((hpg (update-h-omarki ref 1 hpg))
                    (hpg (update-h-nobj (hpg-add (h-nobj hpg) 1) hpg)))
               (hpg-spush tag ref hpg))
           hpg))
        ((equal tag 9)
         (if (and (< ref (h-vmark-length hpg)) (< ref (h-vlen-length hpg)) (equal (h-vmarki ref hpg) 0))
             (let* ((hpg (update-h-vmarki ref 1 hpg))
                    (hpg (update-h-nvec (hpg-add (h-nvec hpg) 1) hpg))
                    (n (h-vleni ref hpg))
                    (hpg (update-h-alive (hpg-add (h-alive hpg) (if (and (<= 0 n) (<= n *hb40*)) n 0)) hpg)))
               (hpg-spush tag ref hpg))
           hpg))
        ((hpg-text-tag tag)
         (if (< ref (h-smark-length hpg))
             (let ((hpg (update-h-smarki ref 1 hpg)))
               (update-h-nstr (hpg-add (h-nstr hpg) 1) hpg))
           hpg))
        (t hpg)))

(defun hpg-scan-obj (i k hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- 5 (nfix k)))
                  :guard (and (hpg-ok hpg) (natp i) (< i *hb40*) (natp k) (<= k 5))))
  (if (or (not (natp k)) (<= 5 k))
      hpg
    (let ((j (+ (* 5 i) k)))
      (if (and (< j (h-otag-length hpg)) (< j (h-oref-length hpg)))
          (let ((hpg (hpg-push (h-otagi j hpg) (h-orefi j hpg) hpg)))
            (hpg-scan-obj i (+ 1 k) hpg))
        hpg))))

(defun hpg-scan-run (j e hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- (nfix e) (nfix j)))
                  :guard (and (hpg-ok hpg) (natp j) (natp e) (<= e *hb40*))))
  (if (or (not (natp j)) (not (natp e)) (<= e j))
      hpg
    (if (and (< j (h-atag-length hpg)) (< j (h-aref-length hpg)))
        (let ((hpg (hpg-push (h-atagi j hpg) (h-arefi j hpg) hpg)))
          (hpg-scan-run (+ 1 j) e hpg))
      hpg)))

(defun hpg-scan-vec (i hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (and (hpg-ok hpg) (natp i))))
  (if (and (< i (h-voff-length hpg)) (< i (h-vlen-length hpg)))
      (let ((off (nfix (h-voffi i hpg))) (n (nfix (h-vleni i hpg))))
        (if (and (<= off *hb40*) (<= n *hb40*) (<= (+ off n) *hb40*))
            (hpg-scan-run off (+ off n) hpg)
          hpg))
    hpg))

(defun hpg-drain (fuel hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix fuel) :guard (and (hpg-ok hpg) (natp fuel))))
  (if (or (zp fuel) (zp (h-msp hpg)) (not (equal (h-err hpg) 0)))
      hpg
    (let* ((sp (- (h-msp hpg) 1))
           (tag (h-mtagi sp hpg))
           (ref (h-mrefi sp hpg))
           (hpg (update-h-msp sp hpg))
           (hpg (cond ((and (equal tag 8) (< 0 ref) (< ref *hb40*)) (hpg-scan-obj ref 0 hpg))
                      ((and (equal tag 9) (< 0 ref)) (hpg-scan-vec ref hpg))
                      (t hpg))))
      (hpg-drain (- fuel 1) hpg))))

; ---- the callees keep the stobj's type and hpg-ok (clotran heapg.lisp's guard lemmas)

(defmacro hsb64-elems (p)
  `(defthm ,(intern-in-package-of-symbol (concatenate (quote string) (symbol-name p) "-NTH") p)
     (implies (and (,p l) (< (nfix i) (len l)))
              (and (integerp (nth i l)) (rationalp (nth i l)) (acl2-numberp (nth i l))
                   (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808)))
     :rule-classes ((:rewrite) (:type-prescription :corollary (implies (and (,p l) (< (nfix i) (len l))) (integerp (nth i l))))
                    (:linear :corollary (implies (and (,p l) (< (nfix i) (len l)))
                                                 (and (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808)))))
     :hints (("Goal" :in-theory (enable nth)))))
(hsb64-elems h-otagp) (hsb64-elems h-orefp) (hsb64-elems h-omarkp) (hsb64-elems h-voffp) (hsb64-elems h-vlenp)
(hsb64-elems h-vmarkp) (hsb64-elems h-atagp) (hsb64-elems h-arefp) (hsb64-elems h-smarkp) (hsb64-elems h-mtagp)
(hsb64-elems h-mrefp)

(defmacro hsb64-update (p)
  `(defthm ,(intern-in-package-of-symbol (concatenate (quote string) (symbol-name p) "-UPDATE-NTH") p)
     (implies (and (,p l) (natp i) (< i (len l)) (integerp v) (<= -9223372036854775808 v) (< v 9223372036854775808))
              (,p (update-nth i v l)))
     :hints (("Goal" :in-theory (enable update-nth) :induct (update-nth i v l)))))
(hsb64-update h-otagp) (hsb64-update h-orefp) (hsb64-update h-omarkp) (hsb64-update h-voffp) (hsb64-update h-vlenp)
(hsb64-update h-vmarkp) (hsb64-update h-atagp) (hsb64-update h-arefp) (hsb64-update h-smarkp) (hsb64-update h-mtagp)
(hsb64-update h-mrefp)

(defthm hpg-add-bounds
  (and (natp (hpg-add n k)) (<= (hpg-add n k) *hb40*))
  :rule-classes ((:rewrite) (:linear :corollary (<= (hpg-add n k) *hb40*))
                 (:type-prescription :corollary (natp (hpg-add n k)))))
(in-theory (disable hpg-add))

(defthm hpg-spush-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (sb64p tag) (sb64p ref))
           (and (hpgp (hpg-spush tag ref hpg)) (hpg-ok (hpg-spush tag ref hpg))))
  :hints (("Goal" :in-theory (e/d (hpgp hpg-ok hpg-lens) (nth update-nth)))))

(defthm hpg-push-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (sb64p tag) (sb64p ref))
           (and (hpgp (hpg-push tag ref hpg)) (hpg-ok (hpg-push tag ref hpg))))
  :hints (("Goal" :in-theory (e/d (hpgp hpg-ok hpg-lens) (nth update-nth hpg-spush)))))
; the state facts the CALLed procedures need (gen-st-xdrain): the lengths one GC.f90 size answers
; are equal (hp_n_obj: okind, omark; hp_n_vec: vmark, vlen, voff; hp_n_arena: aival, atag, aref);
; hpg_push keeps them, and nt-lens
(defun xd-lens (h)
  (and (equal (len (nth *h-omarki* h)) (len (nth *h-okindi* h)))
       (equal (len (nth *h-vleni* h)) (len (nth *h-vmarki* h))) (equal (len (nth *h-voffi* h)) (len (nth *h-vmarki* h)))
       (equal (len (nth *h-atagi* h)) (len (nth *h-aivali* h))) (equal (len (nth *h-arefi* h)) (len (nth *h-aivali* h)))))

(defthm hpg-push-len-nth
  (implies (and (hpg-ok hpg) (natp i) (not (member i '(0 12 13 14 15 16))))
           (equal (len (nth i (hpg-push tag ref hpg))) (len (nth i hpg))))
  :hints (("Goal" :in-theory (e/d (hpg-ok hpg-lens hpg-push hpg-spush update-h-omarki update-h-nobj update-h-vmarki update-h-nvec update-h-alive
                                   update-h-smarki update-h-nstr update-h-mtagi update-h-mrefi update-h-msp update-h-err
                                   h-omarki h-vmarki h-vleni h-omark-length h-vmark-length h-vlen-length h-smark-length
                                   h-nobj h-nvec h-alive h-nstr h-msp h-mtag-length)
                                  (nth update-nth)))))

(defthm hpg-push-lens
  (implies (hpg-ok hpg) (and (equal (xd-lens (hpg-push tag ref hpg)) (xd-lens hpg)) (equal (nt-lens (hpg-push tag ref hpg)) (nt-lens hpg))))
  :hints (("Goal" :in-theory (e/d (xd-lens nt-lens) (hpg-push nth hpg-ok)))))

(defthm xd-lens-msp
  (and (equal (xd-lens (update-nth 12 v h)) (xd-lens h)) (equal (nt-lens (update-nth 12 v h)) (nt-lens h))))
(in-theory (disable hpg-push xd-lens))

(defmacro hpg-elem (fld)
  (let ((ix (intern-in-package-of-symbol (concatenate 'string "*H-" (symbol-name fld) "I*") 'hpg))
        (nm (intern-in-package-of-symbol (concatenate 'string "HPG-" (symbol-name fld) "-ELEM") 'hpg)))
    `(defthm ,nm
       (implies (and (hpgp hpg) (< (nfix j) (len (nth ,ix hpg))))
                (and (integerp (nth j (nth ,ix hpg))) (rationalp (nth j (nth ,ix hpg)))
                     (<= -9223372036854775808 (nth j (nth ,ix hpg))) (< (nth j (nth ,ix hpg)) 9223372036854775808)))
       :rule-classes ((:rewrite) (:type-prescription :corollary (implies (and (hpgp hpg) (< (nfix j) (len (nth ,ix hpg)))) (integerp (nth j (nth ,ix hpg))))))
       :hints (("Goal" :in-theory (enable hpgp))))))
(hpg-elem otag) (hpg-elem oref) (hpg-elem atag) (hpg-elem aref) (hpg-elem mtag) (hpg-elem mref)

(defthm hpg-push-slot-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp j) (< j (len (nth *h-otagi* hpg))) (< j (len (nth *h-orefi* hpg))))
           (and (hpgp (hpg-push (nth j (nth *h-otagi* hpg)) (nth j (nth *h-orefi* hpg)) hpg))
                (hpg-ok (hpg-push (nth j (nth *h-otagi* hpg)) (nth j (nth *h-orefi* hpg)) hpg))))
  :hints (("Goal" :in-theory (disable hpgp hpg-ok hpg-push-ok)
           :use ((:instance hpg-push-ok (tag (nth j (nth *h-otagi* hpg))) (ref (nth j (nth *h-orefi* hpg))))))))

(defthm hpg-push-word-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp j) (< j (len (nth *h-atagi* hpg))) (< j (len (nth *h-arefi* hpg))))
           (and (hpgp (hpg-push (nth j (nth *h-atagi* hpg)) (nth j (nth *h-arefi* hpg)) hpg))
                (hpg-ok (hpg-push (nth j (nth *h-atagi* hpg)) (nth j (nth *h-arefi* hpg)) hpg))))
  :hints (("Goal" :in-theory (disable hpgp hpg-ok hpg-push-ok)
           :use ((:instance hpg-push-ok (tag (nth j (nth *h-atagi* hpg))) (ref (nth j (nth *h-arefi* hpg))))))))

(defthm hpgp-arrs-d
  (implies (hpgp hpg)
           (and (h-otagp (nth 1 hpg)) (h-orefp (nth 2 hpg)) (h-atagp (nth 7 hpg)) (h-arefp (nth 8 hpg))
                (h-mtagp (nth 10 hpg)) (h-mrefp (nth 11 hpg))))
  :hints (("Goal" :in-theory (e/d (hpgp) (nth h-otagp h-orefp h-atagp h-arefp h-mtagp h-mrefp)))))

(defthm hpg-scan-obj-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp i)) (and (hpgp (hpg-scan-obj i k hpg)) (hpg-ok (hpg-scan-obj i k hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp nth update-nth h-otagp h-orefp))))

(defthm hpg-scan-run-ok
  (implies (and (hpgp hpg) (hpg-ok hpg)) (and (hpgp (hpg-scan-run j e hpg)) (hpg-ok (hpg-scan-run j e hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp nth update-nth h-atagp h-arefp))))

(defthm hpg-scan-vec-ok
  (implies (and (hpgp hpg) (hpg-ok hpg)) (and (hpgp (hpg-scan-vec i hpg)) (hpg-ok (hpg-scan-vec i hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp hpg-scan-run nth update-nth))))

(defthm hpg-pop-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp v) (<= v (nth 12 hpg)))
           (and (hpgp (update-nth 12 v hpg)) (hpg-ok (update-nth 12 v hpg))))
  :hints (("Goal" :in-theory (enable hpgp hpg-ok hpg-lens))))

(defthm hpg-ok-stack
  (implies (and (hpgp hpg) (hpg-ok hpg))
           (and (natp (nth 12 hpg)) (<= (nth 12 hpg) (len (nth 10 hpg)))
                (<= (len (nth 10 hpg)) (len (nth 11 hpg))) (<= (len (nth 10 hpg)) *hb40*)
                (integerp (nth 0 hpg)) (<= -9223372036854775808 (nth 0 hpg)) (< (nth 0 hpg) 9223372036854775808)
                (true-listp (nth 10 hpg)) (true-listp (nth 11 hpg))
                (< (nth 12 hpg) 9223372036854775808)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hpgp hpg-ok hpg-lens))))

(defthm hpg-scan-obj-lens
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp i) (xd-lens hpg) (nt-lens hpg))
           (and (xd-lens (hpg-scan-obj i k hpg)) (nt-lens (hpg-scan-obj i k hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp nth update-nth h-otagp h-orefp nt-lens))))

(defthm hpg-scan-run-lens
  (implies (and (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg))
           (and (xd-lens (hpg-scan-run j e hpg)) (nt-lens (hpg-scan-run j e hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp nth update-nth h-atagp h-arefp nt-lens))))

(defthm hpg-scan-vec-lens
  (implies (and (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg))
           (and (xd-lens (hpg-scan-vec i hpg)) (nt-lens (hpg-scan-vec i hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp hpg-scan-run nth update-nth nt-lens))))

(in-theory (disable hpg-scan-obj hpg-scan-vec hpg-scan-run hpg-ok))

; (the heap entry, hs-rep / hs-hpg: gen-st-ntail)

; ---- the procedure acl2-fortran prints (check-gen compares it)

(defconst *dr-proc*
  (mv-let (e ps) (g-st-module *heapg-st-raw* '(hpg-obj-at) '(hpg-drain hpg-run-from-batch hpg-run-take hpg-next-tail hpg-seq-op)
                              *heapg-st*)
    (and (not e) (find-proc "hpg_drain" ps))))

(defconst *dr-ls* (nth 4 *dr-proc*))
(defconst *dr-body* (nth 5 *dr-proc*))
(defconst *dr-b* (cadr (car *dr-body*)))

(defthm dr-proc-shape
  (and (equal *dr-proc*
              (list :subroutine "hpg_drain" (nth 2 *dr-proc*) (cons (list "hs" :inout "heap_state") (g-dummies '(fuel)))
                    *dr-ls* *dr-body*))
       (equal *dr-body* (list (list :do *dr-b*))))
  :rule-classes nil)

; ---- the oracle: the callee's ACL2 value on the stobj the entry holds

(defun dr-heap-at (heap key c hpg) (equal (lkp key heap) (cons key (hs-rep c hpg))))

(defun-nx s-call-val-d (name args fr heap)
  (mv-let (err key intent) (obj-of (kadr (kar args)) fr)
    (let* ((e (cdr (lkp key heap))) (hpg (hs-hpg e)))
      (mv-let (e1 i) (sv (kadr args) fr heap)
        (mv-let (e2 k) (sv (kaddr args) fr heap)
          ; the CALL as drain writes it (the object a variable), the entry canonical, the lengths xd-lens and nt-lens say
          (cond ((or err (not (equal (kar args) (list :var (kadr (kar args))))) (not (true-listp args))
                     (not (eq intent :inout)) e1
                     (not (dr-heap-at heap key e hpg)) (not (hpgp hpg)) (not (hpg-ok hpg)) (not (xd-lens hpg)) (not (nt-lens hpg)))
                 (mv :orc fr heap))
                ((and (equal name "hpg_scan_obj") (equal (len args) 3) (not e2)
                      (natp i) (< i *hb40*) (natp k) (<= k 5))
                 (mv nil fr (put key (hs-rep e (hpg-scan-obj i k hpg)) heap)))
                ((and (equal name "hpg_scan_vec") (equal (len args) 2) (natp i) (int64p i))
                 (mv nil fr (put key (hs-rep e (hpg-scan-vec i hpg)) heap)))
                (t (mv :orc fr heap))))))))

(mutual-recursion
 (defun sxc-d (x frame heap)
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
                  (c (sxc-list-d (kaddr x) frame heap))
                  (t (sxc-list-d (kadddr x) frame heap)))))
     (:select (mv-let (err k) (sv (kadr x) frame heap)
                (cond (err (mv (errst err) frame heap))
                      ((not (integerp k)) (mv (errst :type) frame heap))
                      (t (let ((arm (lkp k (kaddr x))))
                           (sxc-list-d (if arm (kadr arm) (kadddr x)) frame heap))))))
     ((:cycle :exit :return) (mv (kar x) frame heap))
     (:call (mv-let (err fr2 h2) (s-call-val-d (kadr x) (kaddr x) frame heap)
              (if err (mv (errst err) frame heap) (mv :normal fr2 h2))))
     (otherwise (mv (errst :syntax) frame heap))))
 (defun sxc-list-d (ss frame heap)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) (mv :normal frame heap)
     (mv-let (sta fr2 h2) (sxc-d (car ss) frame heap)
       (if (eq sta :normal) (sxc-list-d (cdr ss) fr2 h2) (mv sta fr2 h2))))))

(in-theory (disable sxc-d sxc-list-d))

; ---- the named hypothesis: the callees' procedures answer the oracle (p-sorc on it)

(defun-sk p-sorc-d (procs b)
  (forall (x fr heap fuel)
    (implies (and (eq (kar x) :call) (not (mv-nth 0 (s-call-val-d (kadr x) (kaddr x) fr heap)))
                  (integerp fuel) (< (+ b (acl2-count x)) fuel))
             (equal (f-ex x fr heap procs fuel)
                    (mv :normal (mv-nth 1 (s-call-val-d (kadr x) (kaddr x) fr heap))
                        (mv-nth 2 (s-call-val-d (kadr x) (kaddr x) fr heap)))))))

(in-theory (disable p-sorc-d))

(defthm sxc-d-ok-is-f-ex-list
  (implies (and (p-sorc-d procs b) (natp b) (not (errstp (mv-nth 0 (sxc-list-d ss fr heap))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxc-list-d ss fr heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable s-call-val-d p-sorc-d f-ex-list f-ex sxc-d sxc-list-d)
           :use ((:functional-instance sxc-ok-is-f-ex-list
                  (s-call-val s-call-val-d) (sxc sxc-d) (sxc-list sxc-list-d)
                  (p-sorc p-sorc-d) (p-sorc-witness p-sorc-d-witness))))
          (dr-hint id clause '(f-ex-list) '(p-sorc-d-witness) '(p-sorc-d)
           '(:in-theory (union-theories '(p-sorc-d kadr kaddr kadddr) (theory 'minimal-theory)))
           '(:in-theory (union-theories '(kadr kaddr kadddr) (theory 'minimal-theory)) :use ((:instance p-sorc-d-necc)))
           '(:in-theory (disable s-call-val-d p-sorc-d f-ex f-ex-list sxc-d sxc-list-d)
             :expand ((:free (x frame heap) (sxc-d x frame heap)) (:free (ss frame heap) (sxc-list-d ss frame heap)))))))

; ---- one step of the drain, on the ACL2 side

(defun-nx dr-step (hpg)
  (let* ((sp (- (h-msp hpg) 1))
         (tag (h-mtagi sp hpg))
         (ref (h-mrefi sp hpg))
         (hpg (update-h-msp sp hpg)))
    (cond ((and (equal tag 8) (< 0 ref) (< ref *hb40*)) (hpg-scan-obj ref 0 hpg))
          ((and (equal tag 9) (< 0 ref)) (hpg-scan-vec ref hpg))
          (t hpg))))

(defmacro dr-stop () '(or (zp n) (zp (nth 12 hpg)) (not (equal (nth 0 hpg) 0))))

(defthm hpg-drain-step
  (implies (not (dr-stop)) (equal (hpg-drain n hpg) (hpg-drain (1- n) (dr-step hpg))))
  :hints (("Goal" :in-theory (e/d (dr-step h-msp h-err) (hpg-scan-obj hpg-scan-vec)) :expand ((hpg-drain n hpg)))))

(defthm hpg-drain-stop
  (implies (dr-stop) (equal (hpg-drain n hpg) hpg))
  :hints (("Goal" :in-theory (enable h-msp h-err) :expand ((hpg-drain n hpg)))))

(defthm dr-step-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (not (zp (nth 12 hpg))))
           (and (hpgp (dr-step hpg)) (hpg-ok (dr-step hpg))))
  :hints (("Goal" :in-theory (e/d (dr-step h-msp update-h-msp h-mtagi h-mrefi) (hpgp hpg-ok nth update-nth hpg-ok-stack hpg-pop-ok hpg-scan-obj-ok hpg-scan-vec-ok hpg-mref-elem))
           :use (hpg-ok-stack (:instance hpg-pop-ok (v (1- (nth 12 hpg))))
                 (:instance hpg-mref-elem (j (1- (nth 12 hpg))))
                 (:instance hpg-scan-obj-ok (i (nth (1- (nth 12 hpg)) (nth 11 hpg))) (k 0) (hpg (update-nth 12 (1- (nth 12 hpg)) hpg)))
                 (:instance hpg-scan-vec-ok (i (nth (1- (nth 12 hpg)) (nth 11 hpg))) (hpg (update-nth 12 (1- (nth 12 hpg)) hpg)))))))

(defthm dr-step-lens
  (implies (and (hpgp hpg) (hpg-ok hpg) (not (zp (nth 12 hpg))) (xd-lens hpg) (nt-lens hpg))
           (and (xd-lens (dr-step hpg)) (nt-lens (dr-step hpg))))
  :hints (("Goal" :in-theory (e/d (dr-step h-msp update-h-msp h-mtagi h-mrefi)
                                  (hpgp hpg-ok nth update-nth hpg-ok-stack hpg-pop-ok hpg-scan-obj-lens hpg-scan-vec-lens nt-lens xd-lens))
           :use (hpg-ok-stack (:instance hpg-pop-ok (v (1- (nth 12 hpg))))
                 (:instance hpg-scan-obj-lens (i (nth (1- (nth 12 hpg)) (nth 11 hpg))) (k 0) (hpg (update-nth 12 (1- (nth 12 hpg)) hpg)))
                 (:instance hpg-scan-vec-lens (i (nth (1- (nth 12 hpg)) (nth 11 hpg))) (hpg (update-nth 12 (1- (nth 12 hpg)) hpg)))))))

(in-theory (disable dr-step hpg-drain))

; the stack's top entry, in the forms the symbolic run meets
(nt-arr-lemma h-mtag-int64-d h-mtagp)
(nt-arr-lemma h-mref-int64-d h-mrefp)

(defthm dr-top-int64
  (implies (and (hpgp hpg) (hpg-ok hpg) (< 0 (nth 12 hpg)))
           (and (int64p (nth (+ -1 (nth 12 hpg)) (nth 10 hpg))) (int64p (nth (+ -1 (nth 12 hpg)) (nth 11 hpg)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(natp) (theory 'minimal-theory))
           :use (hpg-ok-stack hpgp-arrs-d
                 (:instance h-mtag-int64-d (l (nth 10 hpg)) (j (+ -1 (nth 12 hpg))))
                 (:instance h-mref-int64-d (l (nth 11 hpg)) (j (+ -1 (nth 12 hpg))))))))

(defmacro dr-top-lemma (name ix)
  `(defthm ,name
     (implies (and (hpgp hpg) (hpg-ok hpg) (< 0 (nth 12 hpg)))
              (and (integerp (nth (+ -1 (nth 12 hpg)) (nth ,ix hpg)))
                   (<= (nth (+ -1 (nth 12 hpg)) (nth ,ix hpg)) 9223372036854775807)
                   (<= -9223372036854775808 (nth (+ -1 (nth 12 hpg)) (nth ,ix hpg)))))
     :rule-classes (:rewrite (:type-prescription :corollary (implies (and (hpgp hpg) (hpg-ok hpg) (< 0 (nth 12 hpg))) (integerp (nth (+ -1 (nth 12 hpg)) (nth ,ix hpg))))))
     :hints (("Goal" :in-theory (e/d (int64p) (hpgp hpg-ok nth h-mtag-int64-d h-mref-int64-d hpg-mtag-elem hpg-mref-elem hpgp-arrs-d)) :use dr-top-int64))))
(dr-top-lemma dr-top-tag 10)
(dr-top-lemma dr-top-ref 11)

; ---- one iteration of the DO's body, symbolically

(defun dr-frp (fr ls)
  (if (atom ls) t
    (and (consp (cdr (lkp (car (car ls)) fr))) (equal (car (cdr (lkp (car (car ls)) fr))) (cadr (car ls)))
         (dr-frp fr (cdr ls)))))

(defun dr-hs-at (fr key) (equal (lkp "hs" fr) (list* "hs" :obj :inout key)))
(defun dr-fuel-at (fr n) (equal (lkp "fuel_" fr) (list* "fuel_" :int64 n)))

(defthm dr-hs-at-lkp (implies (dr-hs-at fr key) (equal (lkp "hs" fr) (list* "hs" :obj :inout key))))
(defthm dr-fuel-at-lkp (implies (dr-fuel-at fr n) (equal (lkp "fuel_" fr) (list* "fuel_" :int64 n))))
(defthm dr-heap-at-lkp (implies (dr-heap-at heap key c hpg) (equal (lkp key heap) (cons key (hs-rep c hpg)))))
(defthm dr-hs-at-put (implies (not (equal k "hs")) (equal (dr-hs-at (put k v fr) key) (dr-hs-at fr key))))
(defthm dr-fuel-at-put
  (equal (dr-fuel-at (put k v fr) n) (if (equal k "fuel_") (equal v (cons :int64 n)) (dr-fuel-at fr n))))
(defthm dr-heap-at-put (equal (dr-heap-at (put key v heap) key c hpg) (equal v (hs-rep c hpg))))
(in-theory (disable dr-hs-at dr-fuel-at dr-heap-at))

(defmacro dr-hyps ()
  '(and (dr-frp fr *dr-ls*) (dr-hs-at fr key)
        (dr-fuel-at fr n) (int64p n)
        (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (dr-heap-at heap key c hpg)))

(defthm dr-iter-stop
  (implies (and (dr-hyps) (dr-stop))
           (and (equal (mv-nth 0 (sxc-list-d *dr-b* fr heap)) :exit)
                (equal (mv-nth 2 (sxc-list-d *dr-b* fr heap)) heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (int64p comp-of read-elem) (hpgp hpg-ok hs-rep nth update-nth put))
           :expand ((:free (x frame heap) (sxc-d x frame heap)) (:free (ss frame heap) (sxc-list-d ss frame heap))
                    (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))))))

(defthm dr-iter-step
  (implies (and (dr-hyps) (not (dr-stop)))
           (let ((r (sxc-list-d *dr-b* fr heap)))
             (and (equal (mv-nth 0 r) :cycle)
                  (equal (mv-nth 2 r) (put key (hs-rep c (dr-step hpg)) heap))
                  (dr-frp (mv-nth 1 r) *dr-ls*)
                  (dr-hs-at (mv-nth 1 r) key)
                  (dr-fuel-at (mv-nth 1 r) (1- n)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (nfix int64p comp-of read-elem s-call-val-d dr-step h-msp update-h-msp h-mtagi h-mrefi)
                           (hpgp hpg-ok hs-rep nth update-nth put hpg-scan-obj hpg-scan-vec hpg-mtag-elem hpg-mref-elem))
           :expand ((:free (x frame heap) (sxc-d x frame heap)) (:free (ss frame heap) (sxc-list-d ss frame heap))
                    (:free (x frame heap) (sx x frame heap)) (:free (e fr heap) (sv e fr heap))))))

; ---- the DO, by induction on the drain's fuel

(defthm f-ex-do-cycle
  (implies (and (posp k) (equal (mv-nth 0 (f-ex-list bb fr heap procs (1- k))) :cycle))
           (equal (f-ex (list :do bb) fr heap procs k)
                  (f-ex (list :do bb) (mv-nth 1 (f-ex-list bb fr heap procs (1- k))) (mv-nth 2 (f-ex-list bb fr heap procs (1- k)))
                        procs (1- k))))
  :hints (("Goal" :in-theory (disable f-ex f-ex-list) :expand ((f-ex (list :do bb) fr heap procs k)))))

(defthm f-ex-do-exit2
  (implies (and (posp k) (equal (mv-nth 0 (f-ex-list bb fr heap procs (1- k))) :exit))
           (equal (f-ex (list :do bb) fr heap procs k)
                  (mv :normal (mv-nth 1 (f-ex-list bb fr heap procs (1- k))) (mv-nth 2 (f-ex-list bb fr heap procs (1- k))))))
  :hints (("Goal" :in-theory (disable f-ex f-ex-list) :expand ((f-ex (list :do bb) fr heap procs k)))))

(defmacro dr-k (b) `(+ 2 ,b (acl2-count *dr-b*)))

(defun-nx dr-ind (n hpg fr heap k key c)
  (declare (xargs :measure (nfix n)))
  (if (or (dr-stop) (zp k)) (list fr heap)
    (dr-ind (1- n) (dr-step hpg) (mv-nth 1 (sxc-list-d *dr-b* fr heap)) (put key (hs-rep c (dr-step hpg)) heap)
            (1- k) key c)))

(defthm dr-loop
  (implies (and (dr-hyps) (p-sorc-d procs b) (natp b) (integerp k) (< (* (+ 1 (nfix n)) (dr-k b)) k))
           (and (equal (mv-nth 0 (f-ex (list :do *dr-b*) fr heap procs k)) :normal)
                (equal (mv-nth 2 (f-ex (list :do *dr-b*) fr heap procs k)) (put key (hs-rep c (hpg-drain n hpg)) heap))))
  :hints (("Goal" :induct (dr-ind n hpg fr heap k key c) :do-not-induct t
           :in-theory (disable f-ex f-ex-list sxc-list-d hpgp hpg-ok hs-rep dr-frp p-sorc-d put))))

; ---- f-invoke of a subroutine of the drain's shape, on its body's run

(defthm f-invoke-sub-d
  (implies (and (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (int64-listp ks) (equal (len ks) (len vs)) (integerp fuel) (< (+ 6 (len ks)) fuel)
                (equal (mv-nth 0 (f-ex-list body (undef-locals ls (fb vs ks (put o (list* :obj :inout key) nil)))
                                            heap procs (1- fuel)))
                       :normal))
           (equal (f-invoke (list :subroutine nm rec (cons (list o :inout c) (g-dummies vs)) ls body)
                            (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                  (mv nil caller (mv-nth 2 (f-ex-list body (undef-locals ls (fb vs ks (put o (list* :obj :inout key) nil)))
                                                      heap procs (1- fuel))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-ex-list undef-locals fb g-dummies g-lits f-bind)
           :expand ((:free (p) (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel))))))

(defmacro dr-frame ()
  '(undef-locals *dr-ls* (fb '(fuel) (list n) (put "hs" (list* :obj :inout key) nil))))

(defthm dr-frame-hyps
  (and (dr-frp (dr-frame) *dr-ls*) (dr-hs-at (dr-frame) key)
       (dr-fuel-at (dr-frame) n))
  :hints (("Goal" :in-theory (enable fb dr-hs-at dr-fuel-at))))

(defthm dr-body-run
  (implies (and (p-sorc-d procs b) (natp b) (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (int64p n)
                (dr-heap-at heap key comps hpg)
                (integerp k) (< (+ 2 (* (+ 1 (nfix n)) (dr-k b))) k))
           (and (equal (mv-nth 0 (f-ex-list *dr-body* (dr-frame) heap procs k)) :normal)
                (equal (mv-nth 2 (f-ex-list *dr-body* (dr-frame) heap procs k))
                       (put key (hs-rep comps (hpg-drain n hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-ex f-ex-list dr-loop dr-frp undef-locals fb hpgp hpg-ok hs-rep int64p p-sorc-d put)
           :expand ((f-ex-list *dr-body* (dr-frame) heap procs k)
                    (:free (fr h) (f-ex-list nil fr h procs (+ -1 k))))
           :use ((:instance dr-loop (fr (dr-frame)) (c comps) (k (1- k)))))))

(defthm dr-k-nat (implies (natp b) (natp (* (+ 1 (nfix n)) (dr-k b)))) :rule-classes nil)

; ---- the theorem: the callees' correctness (p-sorc-d) the only hypothesis about the
; procedures; hs's heap entry holds the stobj as hs-rep lays it out

(defthm hpg-drain-fortran-correct
  (implies (and (p-sorc-d procs b) (natp b)
                (hpgp hpg) (hpg-ok hpg) (xd-lens hpg) (nt-lens hpg) (int64p n)
                (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (dr-heap-at heap key comps hpg)
                (integerp fuel) (< (+ 9 (* (+ 1 (nfix n)) (dr-k b))) fuel))
           (equal (f-invoke *dr-proc* (cons (list :var ob) (g-lits (list n))) caller heap procs fuel)
                  (mv nil caller (put key (hs-rep comps (hpg-drain n hpg)) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (quote (natp int64-listp len car-cons cdr-cons (int64-listp) (len) (g-dummies) (nth) (cons) (equal))) (theory (quote minimal-theory)))
           :use (dr-proc-shape dr-k-nat
                 (:instance dr-body-run (k (1- fuel)))
                 (:instance f-invoke-sub-d (ks (list n)) (vs '(fuel)) (o "hs") (c "heap_state") (nm "hpg_drain")
                            (rec (nth 2 *dr-proc*)) (ls *dr-ls*) (body *dr-body*))))))
