; gen-sflits: p-sforc from a hypothesis on literal arguments (GEN.md
; "What remains" 4b, step 3). p-sforc asks f-ev of `f(ob, cs)` to answer
; svf's value for any argument codes cs; `p-sflits` asks it only of the
; procedure invoked on literals: wherever the oracle s-fn-val answers on f,
; S (ob's heap entry) and ks, f's procedure is a FUNCTION whose dummies are
; the object (intent in) then ks's value dummies, and f-invoke of it on
; `((:var ob) . (g-lits ks))` answers the oracle's value, the heap unchanged.
; That is what g-sret-fn-sem gives of a generated function (gen-sfdisch).
; `p-sflits-p-sforc`: p-sflits gives p-sforc, by induction on the call
; code's size (p-sforc-b, p-sforc below a bound m: the argument codes are
; smaller, so f-ev of them is svf's by svf-ok-is-f-ev-b, and f-invoke depends
; on its arguments only through f-bind). Then `sxf-lits-ok-is-f-ex-list`,
; sxf-ok-is-f-ex-list under p-sflits.

(in-package "ACL2")

(include-book "gen-sfx")
(include-book "gen-stfn")

; ---- p-sforc below a bound on the code's size

(defun-sk p-sforc-b (procs b m)
  (forall (x fr heap fuel)
    (implies (and (eq (kar x) :fcall) (< (acl2-count x) m) (not (mv-nth 0 (svf x fr heap)))
                  (integerp fuel) (< (+ b (acl2-count x)) fuel))
             (equal (f-ev x fr heap procs fuel) (svf x fr heap)))))

(in-theory (disable p-sforc-b))

(defthm svf-fcall-f-ev-b
  (implies (and (p-sforc-b procs b m) (eq (kar e) :fcall) (< (acl2-count e) m) (not (mv-nth 0 (svf e fr heap)))
                (integerp k) (< (+ b (acl2-count e)) k))
           (equal (f-ev e fr heap procs k) (svf e fr heap)))
  :hints (("Goal" :in-theory (disable p-sforc-b-necc f-ev svf) :use (:instance p-sforc-b-necc (x e) (fuel k)))))

(defthm svf-ok-is-f-ev-b
  (implies (and (p-sforc-b procs b m) (natp b) (< (acl2-count e) m) (not (mv-nth 0 (svf e fr heap)))
                (integerp k) (< (+ b (acl2-count e)) k))
           (equal (f-ev e fr heap procs k) (svf e fr heap)))
  :hints (("Goal" :induct (sv-ind e k) :do-not-induct t
           :in-theory (disable p-sforc-b-necc binop arith read-elem comp-of obj-of f-ev svf f-invoke find-proc
                               svf-is-sv sv-is-fv-f cs-expr cf-expr fv int-lit-p svf-ok-is-f-ev svf-fcall-f-ev))
          (and stable-under-simplificationp
               '(:cases ((member-eq (kar e) '(:int :true :false :huge :var :comp :size)) (member-eq (kar e) '(:neg :not))
                         (member-eq (kar e) '(:add :sub :mul :eq :lt :le :ge :max)) (eq (kar e) :elem) (eq (kar e) :fcall))
                 :use (svf-fcall-f-ev-b)))))

; ---- f-bind of value dummies: on codes answering ks (by svf), and on ks's literals

(defun val-dums (ds) (if (atom ds) t (and (eq (kadr (car ds)) :value) (val-dums (cdr ds)))))

(defun fbv (ds ks fr) (if (atom ds) fr (fbv (cdr ds) (cdr ks) (put (kar (car ds)) (cons :int64 (car ks)) fr))))

(defun fbv-ind (ds cs ks fr fuel)
  (if (atom ds) (list cs ks fr fuel)
    (fbv-ind (cdr ds) (cdr cs) (cdr ks) (put (kar (car ds)) (cons :int64 (car ks)) fr) (1- fuel))))

(defthm svlf-cons-parts
  (implies (and (consp cs) (not (car (svlf cs fr heap))))
           (and (not (car (svf (car cs) fr heap))) (not (car (svlf (cdr cs) fr heap)))
                (equal (mv-nth 1 (svlf cs fr heap)) (cons (mv-nth 1 (svf (car cs) fr heap)) (mv-nth 1 (svlf (cdr cs) fr heap))))))
  :hints (("Goal" :in-theory (disable svf) :expand ((svlf cs fr heap)))))

(defthm f-bind-val-step
  (implies (and (posp fuel) (consp ds) (consp cs) (eq (kadr (car ds)) :value)
                (equal (f-ev (car cs) caller heap procs (1- fuel)) (svf (car cs) caller heap))
                (not (mv-nth 0 (svf (car cs) caller heap))) (int64p (mv-nth 1 (svf (car cs) caller heap))))
           (equal (f-bind ds cs caller callee outs heap procs fuel)
                  (f-bind (cdr ds) (cdr cs) caller (put (kar (car ds)) (cons :int64 (mv-nth 1 (svf (car cs) caller heap))) callee)
                          outs heap procs (1- fuel))))
  :hints (("Goal" :in-theory (disable f-ev svf put int64p) :expand ((f-bind ds cs caller callee outs heap procs fuel)))))

(defun fbc-ind (ds cs fr heap callee fuel)
  (if (atom ds) (list cs fr heap callee fuel)
    (mv-let (e v) (svf (car cs) fr heap)
      (declare (ignore e))
      (fbc-ind (cdr ds) (cdr cs) fr heap (put (kar (car ds)) (cons :int64 v) callee) (1- fuel)))))

(defthm f-bind-val-codes
  (implies (and (p-sforc-b procs b m) (natp b) (< (acl2-count cs) m)
                (not (mv-nth 0 (svlf cs caller heap))) (int64-listp (mv-nth 1 (svlf cs caller heap)))
                (val-dums ds) (equal (len ds) (len cs))
                (integerp fuel) (< (+ b 1 (acl2-count cs)) fuel))
           (equal (f-bind ds cs caller callee outs heap procs fuel)
                  (mv nil (fbv ds (mv-nth 1 (svlf cs caller heap)) callee) outs)))
  :hints (("Goal" :induct (fbc-ind ds cs caller heap callee fuel)
           :in-theory (disable f-ev svf svlf put svf-ok-is-f-ev-b svf-fcall-f-ev-b svf-ok-is-f-ev svf-fcall-f-ev
                               svf-leaf-f-ev f-ev-svf-un f-ev-svf-bin f-ev-svf-elem svf-is-sv sv-is-fv-f int64p f-bind))
          ("Subgoal *1/2"
           :use ((:instance svf-ok-is-f-ev-b (e (car cs)) (fr caller) (k (1- fuel)))))
          ("Subgoal *1/1" :expand ((f-bind ds cs caller callee outs heap procs fuel) (svlf cs caller heap)))))

(defthm f-bind-val-lits
  (implies (and (int64-listp ks) (val-dums ds) (equal (len ds) (len ks)) (integerp fuel) (< (+ 4 (len ds)) fuel))
           (equal (f-bind ds (g-lits ks) caller callee outs heap procs fuel) (mv nil (fbv ds ks callee) outs)))
  :hints (("Goal" :induct (fbv-ind ds ks ks callee fuel) :in-theory (disable g-lit f-ev put)
           :expand ((f-bind ds (g-lits ks) caller callee outs heap procs fuel)))))

; the object dummy (intent in) first
(defthm f-bind-in-first
  (implies (and (posp fuel) (eq (kadr d) :in))
           (equal (f-bind (cons d ds) (cons a as) caller callee outs heap procs fuel)
                  (mv-let (err key intent) (if (eq (kar a) :var) (obj-of (kadr a) caller) (mv :type nil nil))
                    (declare (ignore intent))
                    (if err (mv err nil nil)
                      (f-bind ds as caller (put (kar d) (list* :obj :in key) callee) outs heap procs (1- fuel))))))
  :hints (("Goal" :in-theory (disable f-bind obj-of) :expand ((f-bind (cons d ds) (cons a as) caller callee outs heap procs fuel)))))

; f-invoke of a function depends on its arguments only through f-bind
(defthm f-invoke-same-bind-fn
  (implies (and (equal (kar p) :function) (posp fuel)
                (equal (f-bind (nth 4 (true-list-fix p)) a1 caller nil nil heap procs (1- fuel))
                       (f-bind (nth 4 (true-list-fix p)) a2 caller nil nil heap procs (1- fuel))))
           (equal (f-invoke p a1 caller heap procs fuel) (f-invoke p a2 caller heap procs fuel)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable f-bind f-ex-list undef-locals copy-out errstp)
           :expand ((f-invoke p a1 caller heap procs fuel) (f-invoke p a2 caller heap procs fuel)))))

; ---- the hypothesis on literals

(defun sfl-dums (ds ks)
  (and (consp ds) (eq (kadr (car ds)) :in) (val-dums (cdr ds)) (equal (len (cdr ds)) (len ks))))

(defun-sk p-sflits (procs b)
  (forall (name s ks ob caller heap fuel)
    (let ((p (find-proc name procs)))
      (implies (and (not (mv-nth 0 (s-fn-val name s ks))) (not (mv-nth 0 (obj-of ob caller)))
                    (equal (cdr (lkp (mv-nth 1 (obj-of ob caller)) heap)) s)
                    (integerp fuel) (< b fuel))
               (and (eq (kar p) :function) (int64-listp ks) (< (+ 4 (len ks)) b)
                    (sfl-dums (nth 4 (true-list-fix p)) ks)
                    (equal (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                           (mv nil (mv-nth 1 (s-fn-val name s ks)) heap)))))))

(in-theory (disable p-sflits sfl-dums))

; svf on an :fcall answering, its parts
(defthm svf-fcall-parts
  (let* ((a (kaddr x)) (ob (kadr (kar a))) (key (mv-nth 1 (obj-of ob fr))) (ks (mv-nth 1 (svlf (kdr a) fr heap))))
    (implies (and (eq (kar x) :fcall) (not (mv-nth 0 (svf x fr heap))))
             (and (equal (kar (kar a)) :var) (not (mv-nth 0 (obj-of ob fr)))
                  (not (mv-nth 0 (svlf (kdr a) fr heap)))
                  (not (mv-nth 0 (s-fn-val (kadr x) (cdr (lkp key heap)) ks)))
                  (equal (svf x fr heap) (list nil (mv-nth 1 (s-fn-val (kadr x) (cdr (lkp key heap)) ks)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable obj-of svlf) :expand ((svf x fr heap)))))

(defthm fcall-count-parts
  (implies (equal (kar (kar (kaddr x))) :var)
           (< (+ 4 (acl2-count (kdr (kaddr x)))) (acl2-count x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable kar kdr kadr kaddr))))

(defthm svlf-len
  (implies (not (mv-nth 0 (svlf cs fr heap))) (equal (len (mv-nth 1 (svlf cs fr heap))) (len cs)))
  :hints (("Goal" :induct (len cs) :in-theory (disable svf) :expand ((svlf cs fr heap)))))

; the argument codes against their values' literals, after the object (intent in)
(defthm f-bind-codes-lits
  (implies (and (p-sforc-b procs b m) (natp b) (< (acl2-count cs) m)
                (eq (kadr d) :in) (val-dums ds) (equal (len ds) (len cs))
                (eq (kar a) :var) (not (mv-nth 0 (obj-of (kadr a) caller)))
                (not (mv-nth 0 (svlf cs caller heap))) (int64-listp (mv-nth 1 (svlf cs caller heap)))
                (integerp fuel) (< (+ b 2 (acl2-count cs)) fuel) (< (+ 5 (len cs)) fuel))
           (equal (f-bind (cons d ds) (cons a cs) caller nil nil heap procs fuel)
                  (f-bind (cons d ds) (cons (list :var (kadr a)) (g-lits (mv-nth 1 (svlf cs caller heap))))
                          caller nil nil heap procs fuel)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-bind obj-of svlf f-ev svf put g-lits int64-listp f-bind-val-codes f-bind-val-lits svlf-len)
           :use ((:instance svlf-len (fr caller))
                 (:instance f-bind-val-codes (callee (put (kar d) (list* :obj :in (mv-nth 1 (obj-of (kadr a) caller))) nil))
                            (outs nil) (fuel (1- fuel)))
                 (:instance f-bind-val-lits (ks (mv-nth 1 (svlf cs caller heap)))
                            (callee (put (kar d) (list* :obj :in (mv-nth 1 (obj-of (kadr a) caller))) nil))
                            (outs nil) (fuel (1- fuel)))))))

(defthm f-ev-fcall-open
  (implies (and (posp fuel) (eq (kar x) :fcall) (eq (kar (find-proc (kadr x) procs)) :function))
           (equal (f-ev x fr heap procs fuel)
                  (list (mv-nth 0 (f-invoke (find-proc (kadr x) procs) (kaddr x) fr heap procs (1- fuel)))
                        (mv-nth 1 (f-invoke (find-proc (kadr x) procs) (kaddr x) fr heap procs (1- fuel))))))
  :hints (("Goal" :expand ((f-ev x fr heap procs fuel)) :in-theory (disable f-invoke find-proc))))

(defthm cons-kar-kdr (implies (consp y) (equal (cons (kar y) (kdr y)) y)) :hints (("Goal" :in-theory (enable kar kdr))))

(defthm consp-kaddr-var (implies (equal (kar (kar y)) :var) (consp y)) :rule-classes nil
  :hints (("Goal" :in-theory (enable kar))))

(defthm sfl-dums-parts
  (implies (sfl-dums ds ks)
           (and (consp ds) (eq (kadr (car ds)) :in) (val-dums (cdr ds)) (equal (len (cdr ds)) (len ks))
                (equal (cons (car ds) (cdr ds)) ds)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable sfl-dums))))

(defthm mvl-0 (equal (mv-nth 0 (cons a b)) a))
(defthm mvl-1 (equal (mv-nth 1 (cons a (cons b c))) b))

(defmacro pfx ()'(find-proc (kadr x) procs))
(defmacro pob () '(kadr (kar (kaddr x))))
(defmacro pks () '(mv-nth 1 (svlf (kdr (kaddr x)) fr heap)))
(defmacro pds () '(nth 4 (true-list-fix (find-proc (kadr x) procs))))

; f-ev of the :fcall, its codes below m: the invocation on literals
(defthm p-sforc-b-one
  (implies (and (p-sflits procs b) (natp b) (p-sforc-b procs b m)
                (eq (kar x) :fcall) (< (acl2-count (kdr (kaddr x))) m) (not (mv-nth 0 (svf x fr heap)))
                (integerp fuel) (< (+ b (acl2-count x)) fuel))
           (equal (f-ev x fr heap procs fuel) (svf x fr heap)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(mvl-0 mvl-1 posp natp (:type-prescription acl2-count)) (theory 'minimal-theory))
           :use (svf-fcall-parts fcall-count-parts
                 (:instance f-ev-fcall-open)
                 (:instance svlf-len (cs (kdr (kaddr x))))
                 (:instance consp-kaddr-var (y (kaddr x)))
                 (:instance cons-kar-kdr (y (kaddr x)))
                 (:instance sfl-dums-parts (ds (pds)) (ks (pks)))
                 (:instance p-sflits-necc (name (kadr x)) (ob (pob)) (caller fr) (fuel (1- fuel))
                            (s (cdr (lkp (mv-nth 1 (obj-of (pob) fr)) heap))) (ks (pks)))
                 (:instance f-invoke-same-bind-fn (p (pfx)) (caller fr) (fuel (1- fuel))
                            (a1 (kaddr x)) (a2 (cons (list :var (pob)) (g-lits (pks)))))
                 (:instance f-bind-codes-lits (d (car (pds))) (ds (cdr (pds))) (a (kar (kaddr x))) (cs (kdr (kaddr x)))
                            (caller fr) (fuel (1- (1- fuel))))))))

(defthm p-sforc-b-step
  (implies (and (p-sflits procs b) (natp b) (posp m) (p-sforc-b procs b (+ -1 m))) (p-sforc-b procs b m))
  :hints (("Goal" :do-not-induct t :in-theory (disable svf f-ev)
           :expand ((p-sforc-b procs b m))
           :use ((:instance p-sforc-b-one (m (+ -1 m)) (x (mv-nth 0 (p-sforc-b-witness procs b m)))
                            (fr (mv-nth 1 (p-sforc-b-witness procs b m)))
                            (heap (mv-nth 2 (p-sforc-b-witness procs b m)))
                            (fuel (mv-nth 3 (p-sforc-b-witness procs b m))))
                 (:instance svf-fcall-parts (x (mv-nth 0 (p-sforc-b-witness procs b m)))
                            (fr (mv-nth 1 (p-sforc-b-witness procs b m)))
                            (heap (mv-nth 2 (p-sforc-b-witness procs b m))))
                 (:instance fcall-count-parts (x (mv-nth 0 (p-sforc-b-witness procs b m))))))))

(defthm p-sforc-b-zero (p-sforc-b procs b 0) :hints (("Goal" :in-theory (enable p-sforc-b))))

(defun nat-ind-b (m) (if (zp m) m (nat-ind-b (1- m))))

(defthm p-sforc-b-all
  (implies (and (p-sflits procs b) (natp b) (natp m)) (p-sforc-b procs b m))
  :hints (("Goal" :induct (nat-ind-b m))))

(defthm p-sflits-p-sforc
  (implies (and (p-sflits procs b) (natp b)) (p-sforc procs b))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (p-sforc) (svf f-ev p-sforc-b-all))
           :use ((:instance p-sforc-b-all (m (+ 1 (acl2-count (mv-nth 0 (p-sforc-witness procs b))))))
                 (:instance p-sforc-b-necc (m (+ 1 (acl2-count (mv-nth 0 (p-sforc-witness procs b)))))
                            (x (mv-nth 0 (p-sforc-witness procs b))) (fr (mv-nth 1 (p-sforc-witness procs b)))
                            (heap (mv-nth 2 (p-sforc-witness procs b))) (fuel (mv-nth 3 (p-sforc-witness procs b))))))))

(defthm sxf-lits-ok-is-f-ex-list
  (implies (and (p-sflits procs b) (natp b) (not (errstp (mv-nth 0 (sxf-list ss fr heap))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxf-list ss fr heap)))
  :hints (("Goal" :in-theory (disable sxf-ok-is-f-ex-list sxf-list f-ex-list) :use sxf-ok-is-f-ex-list)))
