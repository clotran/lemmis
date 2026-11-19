; gen-st-ext: p-sflits-n discharged (GEN.md "What remains" 4c, step 1).
; hpg-next-tail's callees hpg_ot, hpg_or, hpg_okd, hpg_oi, hpg_obj_at read
; GC.f90's `hp_*` externs, fsem's :extern procedures on the "%ext" component
; of hs's heap entry (fsyn, fsem ext-op). One lemma per extern op
; (f-ev-xcall-*, f-ex-xcall-*: an :xcall of the entry answers the field's element, size,
; value, or the heap with it written); then each callee's procedure answers
; its ACL2 value on hs-hpg of the entry (nt-*-ok), so p-sflits-n holds of
; any procs holding these procedures and externs (`nt-finds`), and
; hpg-next-tail / hpg-seq-op are correct with no hypothesis on the
; procedures past nt-finds (`-fortran-correct-x`).
;
; The callees' procedures are g-st-module's (gen-st's extern roles,
; gen-st-heap's *heapg-xmod*; check-gen compares the text with
; src/f/gen/heap_gen.inc), asserted here to have the shape the proofs expand.
;
; A fact about the state, not the procedures: hp_n_oslot answers both
; h-otag-length and h-oref-length, hp_n_obj both h-okind-length and
; h-oi1-length (one GC.f90 pool each), so the stobj must have those
; lengths equal (`nt-lens`, in the oracle's domain, nt-ent-ok).

(in-package "ACL2")

(include-book "gen-st-ntail")
(include-book "gen-cf")

; ---- the externs and the callees' procedures

(defconst *nt-externs*
  `((:extern "hp_otag" :elem ,*h-otagi*) (:extern "hp_oref" :elem ,*h-orefi*) (:extern "hp_n_oslot" :size ,*h-otagi*)
    (:extern "hp_okind" :elem ,*h-okindi*) (:extern "hp_oi1" :elem ,*h-oi1i*) (:extern "hp_n_obj" :size ,*h-okindi*)))

(defun nt-rd-proc (nm a ext size)
  (declare (xargs :guard t))
  `(:function ,nm t nil (("hs" :in "heap_state") (,a :value :int64)) :int64 (("t_1" :logical))
    ((:if (:not (:lt (:var ,a) (:int 0)))
          ((:assign (:var "t_1") (:lt (:var ,a) (:xcall ,size "hs" nil))))
          ((:assign (:var "t_1") (:false))))
     (:if (:var "t_1")
          ((:assign (:var "r") (:xcall ,ext "hs" ((:var ,a)))) (:return))
          ((:assign (:var "r") (:int -1)) (:return))))))

; g-st-module's procedures (gen-st-heap's *heapg-xmod*), each of the shape the proofs below expand
(defconst *ot-proc* (find-proc "hpg_ot" *heapg-xmod*))
(defconst *or-proc* (find-proc "hpg_or" *heapg-xmod*))
(defconst *okd-proc* (find-proc "hpg_okd" *heapg-xmod*))
(defconst *oi-proc* (find-proc "hpg_oi" *heapg-xmod*))
(defconst *oat-proc* (find-proc "hpg_obj_at" *heapg-xmod*))

(assert-event (and (equal *ot-proc* (nt-rd-proc "hpg_ot" "j_" "hp_otag" "hp_n_oslot"))
                   (equal *or-proc* (nt-rd-proc "hpg_or" "j_" "hp_oref" "hp_n_oslot"))
                   (equal *okd-proc* (nt-rd-proc "hpg_okd" "o_" "hp_okind" "hp_n_obj"))
                   (equal *oi-proc* (nt-rd-proc "hpg_oi" "o_" "hp_oi1" "hp_n_obj"))))

(assert-event
 (equal *oat-proc*
  '(:function "hpg_obj_at" t nil (("hs" :in "heap_state") ("tag_" :value :int64) ("ref_" :value :int64)) :logical nil
    ((:if (:eq (:var "tag_") (:int 8))
          ((:if (:lt (:int 0) (:var "ref_"))
                ((:if (:lt (:var "ref_") (:int 1099511627776))
                      ((:if (:lt (:add (:int 4) (:mul (:int 5) (:var "ref_"))) (:xcall "hp_n_oslot" "hs" nil))
                            ((:assign (:var "r") (:lt (:add (:int 4) (:mul (:int 5) (:var "ref_"))) (:xcall "hp_n_oslot" "hs" nil)))
                             (:return))
                            ((:assign (:var "r") (:false)) (:return))))
                      ((:assign (:var "r") (:false)) (:return))))
                ((:assign (:var "r") (:false)) (:return))))
          ((:assign (:var "r") (:false)) (:return)))))))

(assert-event (fmodule-p (list :module "m" (append *nt-externs* (list *ot-proc* *or-proc* *okd-proc* *oi-proc* *oat-proc*)))))

(defmacro nt-finds ()
  '(and (equal (find-proc "hp_otag" procs) (nth 0 *nt-externs*)) (equal (find-proc "hp_oref" procs) (nth 1 *nt-externs*))
        (equal (find-proc "hp_n_oslot" procs) (nth 2 *nt-externs*)) (equal (find-proc "hp_okind" procs) (nth 3 *nt-externs*))
        (equal (find-proc "hp_oi1" procs) (nth 4 *nt-externs*)) (equal (find-proc "hp_n_obj" procs) (nth 5 *nt-externs*))
        (equal (find-proc "hpg_ot" procs) *ot-proc*) (equal (find-proc "hpg_or" procs) *or-proc*)
        (equal (find-proc "hpg_okd" procs) *okd-proc*) (equal (find-proc "hpg_oi" procs) *oi-proc*)
        (equal (find-proc "hpg_obj_at" procs) *oat-proc*)))

; ---- one lemma per extern op: an :xcall of the procedure found, on variables

(defmacro xp () 'p)
(defmacro xf () '(cadddr p))
(defthm nth-0-3 (and (equal (nth 0 x) (car x)) (equal (nth 1 x) (cadr x)) (equal (nth 2 x) (caddr x)) (equal (nth 3 x) (cadddr x)))
  :hints (("Goal" :in-theory (enable nth))))
(in-theory (disable nth-0-3))
(defmacro ext-key () '(mv-nth 1 (obj-of o fr)))
(defmacro ext-at () '(cdr (lkp "%ext" (cdr (lkp (ext-key) heap)))))
(defmacro ext-hyps (op)
  `(and (equal (find-proc nm procs) p) (integerp fuel) (< 3 fuel) (true-listp (xp)) (equal (car (xp)) :extern) (equal (caddr (xp)) ,op) (natp (xf))
        (not (mv-nth 0 (obj-of o fr))) (true-listp (ext-at))))
(defmacro xvar-ok (x) `(and (equal (cadr (lkp ,x fr)) :int64) (int64p (cddr (lkp ,x fr)))))
(defun ext-var-expands (vars)
  (declare (xargs :mode :program))
  (if (atom vars) nil
    (cons `(:free (k) (f-ev (list :var ,(car vars)) fr heap procs k)) (ext-var-expands (cdr vars)))))
(defmacro ext-thm (name concl x args &rest vars)
  `(defthm ,name ,concl
     :hints (("Goal" :in-theory (enable obj-of nth-0-3)
              :expand ((,x (list :xcall nm o ,args) fr heap procs fuel)
                       (:free (ds as ce k) (f-bind ds as fr ce nil heap procs k))
                       ,@(ext-var-expands vars))))))

(ext-thm f-ev-xcall-size
  (implies (and (ext-hyps :size) (true-listp (nth (xf) (ext-at))))
           (equal (f-ev (list :xcall nm o nil) fr heap procs fuel) (mv nil (len (nth (xf) (ext-at))))))
  f-ev nil)

(ext-thm f-ev-xcall-scalar
  (implies (and (ext-hyps :scalar) (int64p (nth (xf) (ext-at))))
           (equal (f-ev (list :xcall nm o nil) fr heap procs fuel) (mv nil (nth (xf) (ext-at)))))
  f-ev nil)

(ext-thm f-ev-xcall-elem
  (implies (and (ext-hyps :elem) (xvar-ok x) (true-listp (nth (xf) (ext-at)))
                (<= 0 (cddr (lkp x fr))) (< (cddr (lkp x fr)) (len (nth (xf) (ext-at))))
                (int64p (nth (cddr (lkp x fr)) (nth (xf) (ext-at)))))
           (equal (f-ev (list :xcall nm o (list (list :var x))) fr heap procs fuel)
                  (mv nil (nth (cddr (lkp x fr)) (nth (xf) (ext-at))))))
  f-ev (list (list :var x)) x)

(ext-thm f-ex-xcall-set-scalar
  (implies (and (ext-hyps :set-scalar) (xvar-ok y))
           (equal (f-ex (list :xcall nm o (list (list :var y))) fr heap procs fuel)
                  (mv :normal fr (put (ext-key) (put "%ext" (update-nth (xf) (cddr (lkp y fr)) (ext-at))
                                                     (cdr (lkp (ext-key) heap)))
                                      heap))))
  f-ex (list (list :var y)) y)

(ext-thm f-ex-xcall-set-elem
  (implies (and (ext-hyps :set-elem) (xvar-ok x) (xvar-ok y) (true-listp (nth (xf) (ext-at)))
                (<= 0 (cddr (lkp x fr))) (< (cddr (lkp x fr)) (len (nth (xf) (ext-at)))))
           (equal (f-ex (list :xcall nm o (list (list :var x) (list :var y))) fr heap procs fuel)
                  (mv :normal fr
                      (put (ext-key) (put "%ext" (update-nth (xf) (update-nth (cddr (lkp x fr)) (cddr (lkp y fr))
                                                                              (nth (xf) (ext-at)))
                                                             (ext-at))
                                          (cdr (lkp (ext-key) heap)))
                           heap))))
  f-ex (list (list :var x) (list :var y)) x y)

(in-theory (disable f-ev-xcall-size f-ev-xcall-scalar f-ev-xcall-elem f-ex-xcall-set-scalar f-ex-xcall-set-elem))

; ---- the entry: hs-hpg's fields the externs read are "%ext"'s own

(defmacro nt-ext (s) `(cdr (lkp "%ext" ,s)))

(defmacro nt-hpg-nth (name k)
  `(defthm ,name (equal (nth ,k (hs-hpg e)) (nth ,k (nt-ext e))) :hints (("Goal" :in-theory (enable hs-hpg)))))
(nt-hpg-nth nth-hs-hpg-otag *h-otagi*)
(nt-hpg-nth nth-hs-hpg-oref *h-orefi*)
(nt-hpg-nth nth-hs-hpg-okind *h-okindi*)
(nt-hpg-nth nth-hs-hpg-oi1 *h-oi1i*)

(defmacro nt-tl (name recog)
  `(defthm ,name (implies (,recog x) (true-listp x)) :rule-classes :forward-chaining))
(nt-tl h-otagp-tl h-otagp)
(nt-tl h-orefp-tl h-orefp)
(nt-tl h-okindp-tl h-okindp)
(nt-tl h-oi1p-tl h-oi1p)

(defthm nt-ent-arrs
  (implies (nt-ent-ok s)
           (and (true-listp (nt-ext s))
                (true-listp (nth *h-otagi* (nt-ext s))) (true-listp (nth *h-orefi* (nt-ext s)))
                (true-listp (nth *h-okindi* (nt-ext s))) (true-listp (nth *h-oi1i* (nt-ext s)))
                (h-otagp (nth *h-otagi* (nt-ext s))) (h-orefp (nth *h-orefi* (nt-ext s)))
                (h-okindp (nth *h-okindi* (nt-ext s))) (h-oi1p (nth *h-oi1i* (nt-ext s)))
                (equal (len (nth *h-orefi* (nt-ext s))) (len (nth *h-otagi* (nt-ext s))))
                (equal (len (nth *h-oi1i* (nt-ext s))) (len (nth *h-okindi* (nt-ext s))))))
  :hints (("Goal" :in-theory (e/d (nt-ent-ok nt-lens) (hpgp-arrs h-otagp h-orefp h-okindp h-oi1p hpgp))
           :use ((:instance hpgp-arrs (hpg (hs-hpg s)))))))

(in-theory (disable h-otagp h-orefp h-okindp h-oi1p))

; ---- each callee's procedure answers its ACL2 value on the entry's stobj

(defconst *nt-b* 60)

(defmacro nt-callee-hyps ()
  '(and (nt-finds) (nt-ent-ok (cdr (lkp key heap))) (equal (cdr (lkp ob caller)) (list* :obj intent key))
        (integerp fuel) (< *nt-b* fuel)))

; f-ev opened on the expressions the callees' bodies hold, whatever the frame and fuel
(defun nt-ev-expands (es)
  (declare (xargs :mode :program))
  (if (atom es) nil
    (cons `(:free (fr k) (f-ev ',(car es) fr heap procs k)) (nt-ev-expands (cdr es)))))

(defun nt-rd-exprs (a ext size)
  (declare (ignorable ext))
  (declare (xargs :mode :program))
  `((:not (:lt (:var ,a) (:int 0))) (:lt (:var ,a) (:int 0)) (:var ,a) (:int 0) (:false) (:var "t_1") (:int -1)
    (:lt (:var ,a) (:xcall ,size "hs" nil)) (:xcall ,size "hs" nil) (:xcall ,ext "hs" ((:var ,a)))))

(defmacro nt-rd-lemma (thm proc fn a ext size f)
  `(defthm ,thm
     (implies (and (nt-callee-hyps) (int64p j))
              (equal (f-invoke ,proc (list (list :var ob) (g-lit j)) caller heap procs fuel)
                     (mv nil (,fn j (hs-hpg (cdr (lkp key heap)))) heap)))
     :hints (("Goal" :do-not-induct t
              :in-theory (e/d (,fn h-otag-length h-oref-length h-okind-length h-oi1-length h-otagi h-orefi h-okindi h-oi1i obj-of int64p ext-op ext-read-p ext-dums nth-hs-hpg-otag nth-hs-hpg-oref
                               nth-hs-hpg-okind nth-hs-hpg-oi1)
                              (f-invoke f-ev f-bind f-ex f-ex-list hs-hpg nt-ent-ok g-lit))
              :use ((:instance nt-ent-arrs (s (cdr (lkp key heap))))
                    (:instance ,(packn (list f '-int64)) (l (nth ,(packn (list '* f 'i*)) (nt-ext (cdr (lkp key heap)))))))
              :expand ((f-invoke ,proc (list (list :var ob) (g-lit j)) caller heap procs fuel)
                       (:free (ds as cl ce outs k) (f-bind ds as cl ce outs heap procs k))
                       ,@(nt-ev-expands (nt-rd-exprs a ext size)))))))

(nt-rd-lemma nt-ot-ok *ot-proc* hpg-ot "j_" "hp_otag" "hp_n_oslot" h-otag)
(nt-rd-lemma nt-or-ok *or-proc* hpg-or "j_" "hp_oref" "hp_n_oslot" h-oref)
(nt-rd-lemma nt-okd-ok *okd-proc* hpg-okd "o_" "hp_okind" "hp_n_obj" h-okind)
(nt-rd-lemma nt-oi-ok *oi-proc* hpg-oi "o_" "hp_oi1" "hp_n_obj" h-oi1)

(defmacro nt-oat-lemma ()
 `(defthm nt-oat-ok
  (implies (and (nt-callee-hyps) (int64p tag) (int64p ref))
           (equal (f-invoke *oat-proc* (list (list :var ob) (g-lit tag) (g-lit ref)) caller heap procs fuel)
                  (mv nil (hpg-obj-at tag ref (hs-hpg (cdr (lkp key heap)))) heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (hpg-obj-at h-otag-length h-oref-length obj-of int64p ext-op ext-read-p ext-dums nth-hs-hpg-otag nth-hs-hpg-oref)
                           (f-invoke f-ev f-bind f-ex f-ex-list hs-hpg nt-ent-ok g-lit))
           :use ((:instance nt-ent-arrs (s (cdr (lkp key heap)))))
           :expand ((f-invoke *oat-proc* (list (list :var ob) (g-lit tag) (g-lit ref)) caller heap procs fuel)
                    (:free (ds as cl ce outs k) (f-bind ds as cl ce outs heap procs k))
                    ,@(nt-ev-expands
                       '((:eq (:var "tag_") (:int 8)) (:var "tag_") (:int 8) (:lt (:int 0) (:var "ref_")) (:int 0) (:var "ref_")
                         (:lt (:var "ref_") (:int 1099511627776)) (:int 1099511627776)
                         (:lt (:add (:int 4) (:mul (:int 5) (:var "ref_"))) (:xcall "hp_n_oslot" "hs" nil))
                         (:add (:int 4) (:mul (:int 5) (:var "ref_"))) (:int 4) (:mul (:int 5) (:var "ref_")) (:int 5)
                         (:xcall "hp_n_oslot" "hs" nil) (:false))))))))

(nt-oat-lemma)

; ---- p-sflits-n: every name it answers, its procedure answers it

(defthm g-lits-len2
  (implies (and (int64-listp ks) (equal (len ks) 2)) (equal (g-lits ks) (list (g-lit (car ks)) (g-lit (cadr ks)))))
  :hints (("Goal" :expand ((g-lits ks) (g-lits (cdr ks)) (g-lits (cddr ks)) (int64-listp ks) (int64-listp (cdr ks))))))

(defmacro nt-ent-concl ()
  '(let ((p (find-proc name procs)))
     (and (eq (kar p) :function) (int64-listp ks) (< (+ 4 (len ks)) *nt-b*)
          (sfl-dums (nth 4 (true-list-fix p)) ks)
          (equal (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                 (mv nil (mv-nth 1 (s-fn-val-n name s ks *nt-callees*)) heap)))))

(defthm nt-ent-all
  (implies (and (nt-finds) (not (mv-nth 0 (s-fn-val-n name s ks *nt-callees*))) (not (mv-nth 0 (obj-of ob caller)))
                (equal (cdr (lkp (mv-nth 1 (obj-of ob caller)) heap)) s) (integerp fuel) (< *nt-b* fuel))
           (nt-ent-concl))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (s-fn-val-n nt-ks sfl-dums val-dums int64-listp)
                           (f-invoke obj-of hpg-ot hpg-or hpg-okd hpg-oi hpg-obj-at hpg-next-tail nt-ot-ok nt-or-ok nt-okd-ok
                            nt-oi-ok nt-oat-ok hs-hpg))
           :use ((:instance obj-of-binding)
                 (:instance nt-ot-ok (j (car ks)) (intent (mv-nth 2 (obj-of ob caller))) (key (mv-nth 1 (obj-of ob caller))))
                 (:instance nt-or-ok (j (car ks)) (intent (mv-nth 2 (obj-of ob caller))) (key (mv-nth 1 (obj-of ob caller))))
                 (:instance nt-okd-ok (j (car ks)) (intent (mv-nth 2 (obj-of ob caller))) (key (mv-nth 1 (obj-of ob caller))))
                 (:instance nt-oi-ok (j (car ks)) (intent (mv-nth 2 (obj-of ob caller))) (key (mv-nth 1 (obj-of ob caller))))
                 (:instance nt-oat-ok (tag (car ks)) (ref (cadr ks)) (intent (mv-nth 2 (obj-of ob caller)))
                            (key (mv-nth 1 (obj-of ob caller))))))))

(defmacro ntw (k) `(mv-nth ,k (p-sflits-n-witness procs *nt-b* *nt-callees*)))

(defthm p-sflits-n-holds
  (implies (nt-finds) (p-sflits-n procs *nt-b* *nt-callees*))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(p-sflits-n) (theory 'minimal-theory))
           :use ((:instance nt-ent-all (name (ntw 0)) (s (ntw 1)) (ks (ntw 2)) (ob (ntw 3))
                            (caller (ntw 4)) (heap (ntw 5)) (fuel (ntw 6)))))))

; ---- the theorems: no hypothesis on the procedures past nt-finds; hs's entry holds the stobj as
; hs-rep lays it out, its externs' lengths as nt-lens says

(defthm lkp-ext-hs-rep (equal (lkp "%ext" (hs-rep c hpg)) (cons "%ext" (hs-ext hpg)))
  :hints (("Goal" :in-theory (e/d (hs-rep) (put hs-ext hs-del)))))

(defthm nt-ent-ok-rep
  (implies (and (hpgp hpg) (nt-lens hpg)) (nt-ent-ok (hs-rep c hpg)))
  :hints (("Goal" :in-theory (e/d (nt-ent-ok hs-ext) (hpgp hs-rep nt-lens)))))

(defthm hpg-next-tail-fortran-correct-x
  (implies (and (nt-finds) (hpgp hpg) (nt-lens hpg) (natp o) (< o *hb40*)
                (equal (cdr (lkp ob caller)) (list* :obj intent key)) (equal (cdr (lkp key heap)) (hs-rep c hpg))
                (integerp fuel) (< (+ 8 *nt-b* (acl2-count *nt-body*)) fuel))
           (equal (f-invoke *nt-proc* (cons (list :var ob) (g-lits (list o))) caller heap procs fuel)
                  (mv nil (hpg-next-tail o hpg) heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (hs-hpg-rep) (f-invoke hpg-next-tail hpgp nt-lens nt-ent-ok hs-rep hpg-next-tail-fortran-correct
                                         p-sflits-n-holds))
           :use (p-sflits-n-holds (:instance hpg-next-tail-fortran-correct (b *nt-b*))))))

(defthm hpg-seq-op-fortran-correct-x
  (implies (and (nt-finds) (equal (find-proc "hpg_next_tail" procs) *nt-proc*)
                (hpgp hpg) (nt-lens hpg) (int64p op) (int64p tag) (int64p ref)
                (equal (cdr (lkp ob caller)) (list* :obj intent key)) (equal (cdr (lkp key heap)) (hs-rep c hpg))
                (integerp fuel) (< (+ 18 *nt-b* (acl2-count *nt-body*) (acl2-count *sq-body*)) fuel))
           (equal (f-invoke *sq-proc* (cons (list :var ob) (g-lits (list op tag ref))) caller heap procs fuel)
                  (mv nil (hpg-seq-op op tag ref hpg) heap)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (hs-hpg-rep) (f-invoke hpg-seq-op hpgp nt-lens nt-ent-ok hs-rep hpg-seq-op-fortran-correct
                                         p-sflits-n-holds int64p))
           :use (p-sflits-n-holds (:instance hpg-seq-op-fortran-correct (b *nt-b*))))))
