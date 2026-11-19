; gen-st-ntail: hpg-next-tail-fortran-correct (GEN.md "What remains" 4b).
; hpg-next-tail is a value function given the stobj; it reads the stobj only
; through its callees hpg-ot, hpg-or, hpg-obj-at, hpg-okd, hpg-oi, whose
; Fortran reads the `hp_*` externs (4c), so they cannot be sfd-ok entries.
; Their correctness is the named hypothesis `p-sflits-n`: the oracle
; s-fn-val-n answers each callee's ACL2 value on hpg0 (the externs' state;
; the heap entry of the object passed is not read), and p-sflits-n says the
; procedures answer it (gen-sflits' p-sflits on that oracle). svf/sxf are
; copied with the oracle's parameters (hpg0, nms: the names it answers), and
; sxf-lits-ok-is-f-ex-list instantiated; the body's run is symbolic.
; (hpg-next-tail is not recursive: no tail loop is needed.)

(in-package "ACL2")

(include-book "gen-st-spush")
(include-book "gen-st-heap")
(include-book "gen-sfinst")

; ---- clotran's definitions (heapsq.lisp), compared by check-gen

(defmacro sb64p (x) `(and (integerp ,x) (<= -9223372036854775808 ,x) (< ,x 9223372036854775808)))

(defun hpg-ot (j hpg)
  (declare (xargs :stobjs hpg :guard (sb64p j) :verify-guards nil))
  (if (and (<= 0 j) (< j (h-otag-length hpg))) (h-otagi j hpg) -1))

(defun hpg-or (j hpg)
  (declare (xargs :stobjs hpg :guard (sb64p j) :verify-guards nil))
  (if (and (<= 0 j) (< j (h-oref-length hpg))) (h-orefi j hpg) -1))

(defun hpg-okd (o hpg)
  (declare (xargs :stobjs hpg :guard (sb64p o) :verify-guards nil))
  (if (and (<= 0 o) (< o (h-okind-length hpg))) (h-okindi o hpg) -1))

(defun hpg-oi (o hpg)
  (declare (xargs :stobjs hpg :guard (sb64p o) :verify-guards nil))
  (if (and (<= 0 o) (< o (h-oi1-length hpg))) (h-oi1i o hpg) -1))

(defun hpg-obj-at (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref)) :verify-guards nil))
  (and (equal tag 8) (< 0 ref) (< ref *hb40*)
       (< (+ 4 (* 5 ref)) (h-otag-length hpg)) (< (+ 4 (* 5 ref)) (h-oref-length hpg))))

(defun hpg-next-tail (o hpg)
  (declare (xargs :stobjs hpg :guard (and (natp o) (< o *hb40*)) :verify-guards nil))
  (let* ((w (+ 2 (* 5 o)))
         (tg (hpg-ot w hpg))
         (tr (hpg-or w hpg)))
    (cond ((equal tg 0) 1)
          ((not (hpg-obj-at tg tr hpg)) 0)
          ((equal (hpg-okd tr hpg) 1) (if (< 0 (hpg-oi tr hpg)) w 1))
          ((equal (hpg-okd tr hpg) 6)
           (case (hpg-oi tr hpg)
             (1 w)
             (2 1)
             (3 (+ 1 (* 5 tr)))
             (otherwise 0)))
          (t 0))))

; ---- the oracle: the callees' ACL2 values on hpg0, for the names in nms

(defun nt-ks (ks n) (and (int64-listp ks) (equal (len ks) n)))

(defun-nx s-fn-val-n (name s ks hpg0 nms)
  (declare (ignorable s))
  (cond ((not (member-equal name nms)) (mv :orc nil))
        ((and (equal name "hpg_ot") (nt-ks ks 1)) (mv nil (hpg-ot (car ks) hpg0)))
        ((and (equal name "hpg_or") (nt-ks ks 1)) (mv nil (hpg-or (car ks) hpg0)))
        ((and (equal name "hpg_okd") (nt-ks ks 1)) (mv nil (hpg-okd (car ks) hpg0)))
        ((and (equal name "hpg_oi") (nt-ks ks 1)) (mv nil (hpg-oi (car ks) hpg0)))
        ((and (equal name "hpg_obj_at") (nt-ks ks 2)) (mv nil (hpg-obj-at (car ks) (cadr ks) hpg0)))
        ((and (equal name "hpg_next_tail") (nt-ks ks 1) (natp (car ks)) (< (car ks) *hb40*))
         (mv nil (hpg-next-tail (car ks) hpg0)))
        (t (mv :orc nil))))

; ---- svf/svlf/sxf/sxf-list on it (gen-sfinst's copies, renamed)

(mutual-recursion
 (defun svf-n (e fr heap hpg0 nms)
  (declare (xargs :measure (acl2-count e)))
  (case (kar e)
    (:int (if (int-lit-p (kadr e)) (mv nil (kadr e)) (mv :syntax nil)))
    (:true (mv nil t))
    (:false (mv nil nil))
    (:huge (mv nil *int64-max*))
    (:var (let ((b (cdr (lkp (kadr e) fr))))
            (cond ((not (and (consp b) (member-eq (car b) '(:int64 :logical)))) (mv :type nil))
                  ((eq (cdr b) :undef) (mv :undefined nil))
                  (t (mv nil (cdr b))))))
    (:comp (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
             (cond (err (mv err nil)) ((int64p v) (mv nil v)) (t (mv :type nil)))))
    (:size (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
             (cond (err (mv err nil)) ((farrayp v) (mv nil (len (cdr v)))) (t (mv :type nil)))))
    (:elem (mv-let (err i) (svf-n (kadddr e) fr heap hpg0 nms)
             (if err (mv err nil)
               (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
                 (if err (mv err nil) (read-elem v i))))))
    (:neg (mv-let (err a) (svf-n (kadr e) fr heap hpg0 nms) (if err (mv err nil) (arith :sub 0 a))))
    (:not (mv-let (err a) (svf-n (kadr e) fr heap hpg0 nms)
            (cond (err (mv err nil)) ((booleanp a) (mv nil (not a))) (t (mv :type nil)))))
    ((:add :sub :mul :eq :lt :le :ge :max)
     (mv-let (err a) (svf-n (kadr e) fr heap hpg0 nms)
       (if err (mv err nil)
         (mv-let (err b) (svf-n (kaddr e) fr heap hpg0 nms)
           (if err (mv err nil) (binop (kar e) a b))))))
    (:fcall (let ((a (kaddr e)))
              (mv-let (err key intent) (obj-of (kadr (kar a)) fr)
                (declare (ignore intent))
                (cond ((not (eq (kar (kar a)) :var)) (mv :syntax nil))
                      (err (mv err nil))
                      (t (mv-let (err ks) (svlf-n (kdr a) fr heap hpg0 nms)
                           (if err (mv err nil)
                             (mv-let (err v) (s-fn-val-n (kadr e) (cdr (lkp key heap)) ks hpg0 nms) (mv err v)))))))))
    (otherwise (mv :syntax nil))))
 (defun svlf-n (cs fr heap hpg0 nms)
  (declare (xargs :measure (acl2-count cs)))
  (if (atom cs) (mv nil nil)
    (mv-let (err v) (svf-n (car cs) fr heap hpg0 nms)
      (if err (mv err nil)
        (mv-let (err vs) (svlf-n (cdr cs) fr heap hpg0 nms)
          (if err (mv err nil) (mv nil (cons v vs)))))))))

(mutual-recursion
 (defun sxf-n (x frame heap hpg0 nms)
   (declare (xargs :measure (acl2-count x)))
   (case (kar x)
     (:assign
      (mv-let (err v) (svf-n (kaddr x) frame heap hpg0 nms)
        (if err (mv (errst err) frame heap)
          (let ((d (kadr x)))
            (case (kar d)
              (:var (let ((b (cdr (lkp (kadr d) frame))))
                      (if (and (consp b) (scalar-ok (car b) v))
                          (mv :normal (put (kadr d) (cons (car b) v) frame) heap)
                        (mv (errst :type) frame heap))))
              ((:comp :elem)
               (mv-let (err key intent) (obj-of (kadr d) frame)
                 (cond (err (mv (errst err) frame heap))
                       ((not (eq intent :inout)) (mv (errst :intent) frame heap))
                       ((not (int64p v)) (mv (errst :type) frame heap))
                       (t (let* ((comps (cdr (lkp key heap))) (p (lkp (kaddr d) comps)))
                            (cond ((not (consp p)) (mv (errst :type) frame heap))
                                  ((eq (kar d) :comp)
                                   (if (int64p (cdr p))
                                       (mv :normal frame (put key (put (kaddr d) v comps) heap))
                                     (mv (errst :type) frame heap)))
                                  (t (mv-let (err i) (svf-n (kadddr d) frame heap hpg0 nms)
                                       (cond (err (mv (errst err) frame heap))
                                             ((not (and (farrayp (cdr p)) (integerp i))) (mv (errst :type) frame heap))
                                             ((not (and (<= 0 i) (< i (len (cddr p))))) (mv (errst :bounds) frame heap))
                                             (t (mv :normal frame
                                                    (put key (put (kaddr d) (cons :array (update-nth i v (cddr p))) comps)
                                                         heap))))))))))))
              (otherwise (mv (errst :syntax) frame heap)))))))
     (:if (mv-let (err c) (svf-n (kadr x) frame heap hpg0 nms)
            (cond (err (mv (errst err) frame heap))
                  ((not (booleanp c)) (mv (errst :type) frame heap))
                  (c (sxf-list-n (kaddr x) frame heap hpg0 nms))
                  (t (sxf-list-n (kadddr x) frame heap hpg0 nms)))))
     (:select (mv-let (err k) (svf-n (kadr x) frame heap hpg0 nms)
                (cond (err (mv (errst err) frame heap))
                      ((not (integerp k)) (mv (errst :type) frame heap))
                      (t (let ((arm (lkp k (kaddr x))))
                           (sxf-list-n (if arm (kadr arm) (kadddr x)) frame heap hpg0 nms))))))
     ((:cycle :exit :return) (mv (kar x) frame heap))
     (otherwise (mv (errst :syntax) frame heap))))
 (defun sxf-list-n (ss frame heap hpg0 nms)
   (declare (xargs :measure (acl2-count ss)))
   (if (atom ss) (mv :normal frame heap)
     (mv-let (st fr2 h2) (sxf-n (car ss) frame heap hpg0 nms)
       (if (eq st :normal) (sxf-list-n (cdr ss) fr2 h2 hpg0 nms) (mv st fr2 h2))))))

(in-theory (disable svf-n svlf-n sxf-n sxf-list-n))

; ---- the named hypothesis: the callees' procedures answer the oracle

(defun-sk p-sflits-n (procs b hpg0 nms)
  (forall (name s ks ob caller heap fuel)
    (let ((p (find-proc name procs)))
      (implies (and (not (mv-nth 0 (s-fn-val-n name s ks hpg0 nms))) (not (mv-nth 0 (obj-of ob caller)))
                    (equal (cdr (lkp (mv-nth 1 (obj-of ob caller)) heap)) s)
                    (integerp fuel) (< b fuel))
               (and (eq (kar p) :function) (int64-listp ks) (< (+ 4 (len ks)) b)
                    (sfl-dums (nth 4 (true-list-fix p)) ks)
                    (equal (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                           (mv nil (mv-nth 1 (s-fn-val-n name s ks hpg0 nms)) heap)))))))

(in-theory (disable p-sflits-n))

;; sxf-lits-ok-is-f-ex-list on the copies (gen-sfinst's sxf-h-ok-generic)
(defthm sxf-n-ok-is-f-ex-list
  (implies (and (p-sflits-n procs b hpg0 nms) (natp b)
                (not (errstp (mv-nth 0 (sxf-list-n ss fr heap hpg0 nms))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxf-list-n ss fr heap hpg0 nms)))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:functional-instance sxf-lits-ok-is-f-ex-list
                  (s-fn-val (lambda (name s ks) (s-fn-val-n name s ks hpg0 nms)))
                  (svf (lambda (e fr heap) (svf-n e fr heap hpg0 nms)))
                  (svlf (lambda (cs fr heap) (svlf-n cs fr heap hpg0 nms)))
                  (sxf (lambda (x frame heap) (sxf-n x frame heap hpg0 nms)))
                  (sxf-list (lambda (ss frame heap) (sxf-list-n ss frame heap hpg0 nms)))
                  (p-sflits (lambda (procs b) (p-sflits-n procs b hpg0 nms)))
                  (p-sflits-witness (lambda (procs b) (p-sflits-n-witness procs b hpg0 nms))))))
          (sfi-hint id clause '(f-ex-list) '(p-sflits-n-witness) '(p-sflits-n)
           '(:in-theory (union-theories '(p-sflits-n) (theory 'minimal-theory)))
           '(:in-theory (theory 'minimal-theory) :use ((:instance p-sflits-n-necc)))
           '(:in-theory (disable s-fn-val-n svf-n svlf-n sxf-n sxf-list-n p-sflits-n)
             :expand ((svf-n e fr heap hpg0 nms) (svlf-n cs fr heap hpg0 nms) (sxf-n x frame heap hpg0 nms)
                      (sxf-list-n ss frame heap hpg0 nms))))))

; ---- f-invoke of a FUNCTION given the stobj, on its body's run (gen-stretfn's f-invoke-sret on sxf-list-n)

(defthm fbv-g-dummies (equal (fbv (g-dummies vs) ks fr) (fb vs ks fr))
  :hints (("Goal" :induct (fb vs ks fr) :in-theory (e/d (kar kadr fb fbv g-dummies) (g-formal)))))

(defthm f-invoke-sret-n
  (implies (and (p-sflits-n procs b hpg0 nms) (natp b)
                (equal (car (sxf-list-n body (rfr rt) heap hpg0 nms)) :return)
                (equal (mv-nth 2 (sxf-list-n body (rfr rt) heap hpg0 nms)) heap)
                (sret-ok (mv-nth 1 (sxf-list-n body (rfr rt) heap hpg0 nms)) rt v)
                (equal (cdr (lkp ob caller)) (list* :obj intent key))
                (int64-listp ks) (equal (len ks) (len vs))
                (integerp fuel) (< (+ 7 b (len ks) (acl2-count body)) fuel))
           (equal (f-invoke (list :function nm t rec (cons (list o :in c) (g-dummies vs)) rt (g-locals locs) body)
                            (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                  (mv nil v heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (sret-ok) (sxf-list-n f-ex-list undef-locals fb g-dummies g-lits g-locals f-bind
                                      sxf-n-ok-is-f-ex-list f-ex-list-open))
           :expand ((:free (p) (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel)))
           :use ((:instance sxf-n-ok-is-f-ex-list (ss body) (fr (rfr rt)) (k (1- fuel)))))))

; ---- the reads are int64 on an hpg

(defmacro nt-arr-lemma (name recog)
  `(defthm ,name
     (implies (and (,recog l) (natp j) (< j (len l))) (int64p (nth j l)))
     :hints (("Goal" :in-theory (enable nth)))))

(nt-arr-lemma h-otag-int64 h-otagp)
(nt-arr-lemma h-oref-int64 h-orefp)
(nt-arr-lemma h-okind-int64 h-okindp)
(nt-arr-lemma h-oi1-int64 h-oi1p)

(defthm hpgp-arrs
  (implies (hpgp hpg)
           (and (h-otagp (nth *h-otagi* hpg)) (h-orefp (nth *h-orefi* hpg))
                (h-okindp (nth *h-okindi* hpg)) (h-oi1p (nth *h-oi1i* hpg))))
  :hints (("Goal" :in-theory (e/d (hpgp) (h-otagp h-orefp h-okindp h-oi1p)))))

(defthm hpg-reads-int64
  (implies (and (hpgp hpg) (integerp j))
           (and (int64p (hpg-ot j hpg)) (int64p (hpg-or j hpg)) (int64p (hpg-okd j hpg)) (int64p (hpg-oi j hpg))))
  :hints (("Goal" :in-theory (disable nth h-otagp h-orefp h-okindp h-oi1p int64p)
           :use ((:instance h-otag-int64 (l (nth *h-otagi* hpg))) (:instance h-oref-int64 (l (nth *h-orefi* hpg)))
                 (:instance h-okind-int64 (l (nth *h-okindi* hpg))) (:instance h-oi1-int64 (l (nth *h-oi1i* hpg)))))
          (and stable-under-simplificationp '(:in-theory (enable int64p)))))

(defthm hpg-obj-at-bool (booleanp (hpg-obj-at tag ref hpg)) :rule-classes :type-prescription)

(defthm hpg-obj-at-ref
  (implies (hpg-obj-at tag ref hpg) (and (< 0 ref) (< ref 1099511627776)))
  :rule-classes :forward-chaining)

; the same, int64p opened: integerp as a type, the bounds linear
(defmacro nt-read-lemmas (f)
  `(progn
     (defthm ,(packn (list f '-int-tp))
       (implies (and (hpgp hpg) (integerp j)) (integerp (,f j hpg)))
       :rule-classes :type-prescription
       :hints (("Goal" :in-theory (union-theories '(int64p) (theory 'minimal-theory)) :use hpg-reads-int64)))
     (defthm ,(packn (list f '-bounds))
       (implies (and (hpgp hpg) (integerp j))
                (and (<= -9223372036854775808 (,f j hpg)) (<= (,f j hpg) 9223372036854775807)))
       :rule-classes :linear
       :hints (("Goal" :in-theory (union-theories '(int64p) (theory 'minimal-theory)) :use hpg-reads-int64)))))

(nt-read-lemmas hpg-ot)
(nt-read-lemmas hpg-or)
(nt-read-lemmas hpg-okd)
(nt-read-lemmas hpg-oi)

(in-theory (disable hpg-ot hpg-or hpg-okd hpg-oi hpg-obj-at))

; ---- the procedure acl2-fortran prints (check-gen compares it)

(defconst *nt-proc*
  (mv-let (e ps) (g-st-module *heapg-st-raw* '(hpg-obj-at) '(hpg-drain hpg-run-from-batch hpg-run-take hpg-next-tail hpg-seq-op)
                              *heapg-st*)
    (and (not e) (find-proc "hpg_next_tail" ps))))

(defconst *nt-callees* '("hpg_ot" "hpg_or" "hpg_obj_at" "hpg_okd" "hpg_oi"))

(defun nt-unloc (ls) (if (atom ls) nil (cons (cons (car (car ls)) (cadr (car ls))) (nt-unloc (cdr ls)))))
(defconst *nt-locs* (reverse (nt-unloc (nth 6 *nt-proc*))))
(defconst *nt-body* (nth 7 *nt-proc*))

(defthm nt-proc-shape
  (equal *nt-proc*
         (list :function "hpg_next_tail" t (nth 3 *nt-proc*) (cons (list "hs" :in "heap_state") (g-dummies '(o)))
               :int64 (g-locals *nt-locs*) *nt-body*))
  :rule-classes nil)

; ---- the body's run, symbolically

(defmacro nt-frame ()
  '(undef-locals (cons (list "r" :int64) (g-locals *nt-locs*)) (fb '(o) (list o) (put "hs" (list* :obj :in key) nil))))

(defthm nt-run
  (implies (and (hpgp hpg0) (natp o) (< o *hb40*))
           (let ((r (sxf-list-n *nt-body* (nt-frame) heap hpg0 *nt-callees*)))
             (and (equal (car r) :return) (equal (mv-nth 2 r) heap)
                  (sret-ok (mv-nth 1 r) :int64 (hpg-next-tail o hpg0)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (sret-ok s-fn-val-n fb) (hpgp))
           :expand ((:free (x fr h) (sxf-n x fr h hpg0 *nt-callees*))
                    (:free (ss fr h) (sxf-list-n ss fr h hpg0 *nt-callees*))
                    (:free (e fr h) (svf-n e fr h hpg0 *nt-callees*))
                    (:free (cs fr h) (svlf-n cs fr h hpg0 *nt-callees*))))))

; ---- the theorem: the callees' correctness (p-sflits-n on *nt-callees*) the only hypothesis
; about the procedures; hpg the externs' state, the heap entry of ob's object not read

(defthm hpg-next-tail-fortran-correct
  (implies (and (p-sflits-n procs b hpg *nt-callees*) (natp b)
                (hpgp hpg) (natp o) (< o *hb40*)
                (equal (cdr (lkp ob caller)) (list* :obj intent key))
                (integerp fuel) (< (+ 8 b (acl2-count *nt-body*)) fuel))
           (equal (f-invoke *nt-proc* (cons (list :var ob) (g-lits (list o))) caller heap procs fuel)
                  (mv nil (hpg-next-tail o hpg) heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (int64p) (f-invoke sxf-list-n hpg-next-tail hpgp g-dummies g-locals g-lits undef-locals fb
                                     f-invoke-sret-n nt-run p-sflits-n))
           :use (nt-proc-shape
                 (:instance nt-run (hpg0 hpg))
                 (:instance f-invoke-sret-n (hpg0 hpg) (nms *nt-callees*) (body *nt-body*) (rt :int64)
                            (v (hpg-next-tail o hpg)) (ks (list o)) (vs '(o)) (o "hs") (c "heap_state")
                            (nm "hpg_next_tail") (rec (nth 3 *nt-proc*)) (locs *nt-locs*))))))
