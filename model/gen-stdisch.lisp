; gen-stdisch: the oracles of gen-stcall/gen-stcallst made concrete, and
; their hypotheses discharged (GEN.md 4 (4a) (iii)). tab lists the source
; subroutines, each r = (fn formals (sv) t x) with one stobj answering
; itself and an st-plain body; `tab-ok` says each translates (g-st-fn), its
; procedure is the one procs names, and the static side conditions of
; g-st-fn-call hold -- all decidable on a given tab, so an instance
; discharges it by evaluation.
;   ac-orc (f ks s)        the source's call: a-st of f's body on ks, S
;   sc-orc (name args ..)  the Fortran call: the codes' values by sv, the
;                          object's S from the heap, ac-orc, the heap put
; Each answers an error when a dynamic side condition fails (ks not int64,
; S without st-ok/st-wf, the object not INOUT), so "the oracle answers"
; carries them. Proved: `p-sorc-h-holds` (sc-orc is what f-ex of the CALL
; answers, by g-st-fn-call), `c-sorc-h-holds` (sc-orc on g-callst's CALL is
; ac-orc), `a-call-ok-h-holds` (ac-orc keeps st-ok and st-wf, by gst-sem):
; p-sorc, c-sorc and a-call-ok with the oracles replaced.

(in-package "ACL2")

(include-book "gen-stcsorc")

(defun st-src (f tab) (cond ((atom tab) nil) ((equal (kar (car tab)) f) (car tab)) (t (st-src f (cdr tab)))))
(defun st-src-name (name tab)
  (cond ((atom tab) nil) ((equal (g-sym (kar (car tab)) nil) name) (car tab)) (t (st-src-name name (cdr tab)))))
(defun tab-names (tab) (if (atom tab) nil (cons (g-sym (kar (car tab)) nil) (tab-names (cdr tab)))))

(defun svals (cs fr heap)
  (if (atom cs) (mv nil nil)
    (mv-let (e v) (sv (car cs) fr heap)
      (if e (mv e nil) (mv-let (e vs) (svals (cdr cs) fr heap) (if e (mv e nil) (mv nil (cons v vs))))))))

(defun ac-orc (f ks s tab st defs n o)
  (let* ((r (st-src f tab)) (vs (g-st-vals (kadr r) st)))
    (if (and (consp r) (int64-listp ks) (equal (len ks) (len vs)) (st-ok st o s) (st-wf st s))
        (mv-let (e s1) (a-st (nth 4 r) (pairlis$ vs ks) s st defs n) (mv e s1 nil))
      (mv :orc s nil))))

(defun sc-orc (name args fr heap tab st defs n o)
  (let* ((r (st-src-name name tab)) (ob (kadr (kar args))) (key (okey ob fr)) (s (cdr (lkp key heap))))
    (mv-let (e ks) (svals (kdr args) fr heap)
      (if (and (consp r) (not e) (equal (kar args) (list :var ob)) (equal (st-src (kar r) tab) r) (obj-at ob s fr heap))
          (mv-let (e s1 rs) (ac-orc (kar r) ks s tab st defs n o)
            (declare (ignore rs))
            (if e (mv e fr heap) (mv nil fr (put key s1 heap))))
        (mv :orc fr heap)))))

(defmacro ent-let (&rest body)
  `(let* ((fn (kar r)) (formals (kadr r)) (sv (car (kaddr r))) (x (nth 4 r)) (vs (g-st-vals formals st)) (outs (list sv)))
     (declare (ignorable fn formals sv x vs outs))
     ,@body))

(defun st-ent-ok (r gdefs sigs st defs procs o b)
  (ent-let
   (mv-let (e p) (g-st-fn (list fn formals (list sv) t x) gdefs sigs st)
     (mv-let (e2 ss c2 l2) (g-stmt x (g-em vs) 0 nil sigs (sfn) st outs nil nil)
       (declare (ignore e2 c2 l2))
       (and (not e) sv (eq (g-role sv st) :stobj) (tself-ok fn st)
            (eq (g-role fn st) :sub) (equal (g-obj fn st) formals)
            (equal (g-st-dummies formals outs st) (list (list o :inout (g-comp sv st))))
            (st-plain :term x nil st) (no-calls :term x sigs nil)
            (not (g-role 'if st)) (not (g-role 'implies st)) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
            (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (member-equal o (g-formals vs)))
            (equal (find-proc (g-sym fn nil) procs) p)
            (integerp b) (< (+ 9 (acl2-count (gbody ss))) b))))))

(defun tab-ok1 (tab gdefs sigs st defs procs o b)
  (if (atom tab) t (and (st-ent-ok (car tab) gdefs sigs st defs procs o b) (tab-ok1 (cdr tab) gdefs sigs st defs procs o b))))

(defun tab-ok (tab gdefs sigs st defs procs o b)
  (and (tab-ok1 tab gdefs sigs st defs procs o b) (no-duplicatesp-equal (tab-names tab))))

(in-theory (disable st-ent-ok ac-orc sc-orc))

; ---- lookups

(defthm st-src-ok
  (implies (and (tab-ok1 tab gdefs sigs st defs procs o b) (consp (st-src f tab)))
           (and (st-ent-ok (st-src f tab) gdefs sigs st defs procs o b) (equal (kar (st-src f tab)) f))))

(defthm st-src-name-ok
  (implies (and (tab-ok1 tab gdefs sigs st defs procs o b) (consp (st-src-name name tab)))
           (and (st-ent-ok (st-src-name name tab) gdefs sigs st defs procs o b)
                (equal (g-sym (kar (st-src-name name tab)) nil) name))))

(defthm st-src-member
  (implies (consp (st-src f tab)) (member-equal (g-sym f nil) (tab-names tab)))
  :hints (("Goal" :in-theory (disable g-sym))))

(defthm st-src-not-member
  (implies (not (member-equal (g-sym f nil) (tab-names tab))) (not (consp (st-src f tab))))
  :hints (("Goal" :in-theory (disable g-sym))))

(defthm st-src-name-st-src
  (implies (and (no-duplicatesp-equal (tab-names tab)) (consp (st-src f tab)))
           (equal (st-src-name (g-sym f nil) tab) (st-src f tab)))
  :hints (("Goal" :in-theory (disable g-sym))))

(defthm obj-at-val
  (implies (obj-at o s fr heap) (equal (cdr (lkp (okey o fr) heap)) s))
  :hints (("Goal" :in-theory (enable obj-at okey))))

(defthm kar-st-src (implies (consp (st-src f tab)) (equal (kar (st-src f tab)) f)))

(defthm car-lkp-key (implies (consp (lkp k al)) (equal (car (lkp k al)) k)))

(defthm svals-svs-is
  (implies (not (mv-nth 0 (svals cs fr heap))) (svs-is cs (mv-nth 1 (svals cs fr heap)) fr heap))
  :hints (("Goal" :in-theory (disable sv))))

(defthm svs-is-svals
  (implies (and (svs-is cs ks fr heap) (true-listp ks)) (equal (svals cs fr heap) (mv nil ks)))
  :hints (("Goal" :in-theory (disable sv))))

(defthm int64-listp-true (implies (int64-listp ks) (true-listp ks)) :rule-classes :forward-chaining)

; ---- p-sorc

(defun-sk p-sorc-h (procs b tab st defs n o)
  (forall (x fr heap fuel)
    (implies (and (eq (kar x) :call) (not (mv-nth 0 (sc-orc (kadr x) (kaddr x) fr heap tab st defs n o)))
                  (integerp fuel) (< (+ b (acl2-count x)) fuel))
             (equal (f-ex x fr heap procs fuel)
                    (mv :normal (mv-nth 1 (sc-orc (kadr x) (kaddr x) fr heap tab st defs n o))
                        (mv-nth 2 (sc-orc (kadr x) (kaddr x) fr heap tab st defs n o)))))))

; what sc-orc's answering gives, named
(defthm sc-orc-parts
  (let* ((r (st-src-name name tab)) (ob (kadr (kar args))) (key (okey ob fr)) (s (cdr (lkp key heap)))
         (ks (mv-nth 1 (svals (kdr args) fr heap))))
    (implies (not (mv-nth 0 (sc-orc name args fr heap tab st defs n o)))
             (and (consp r) (not (mv-nth 0 (svals (kdr args) fr heap)))
                  (equal args (cons (list :var ob) (kdr args)))
                  (equal (st-src (kar r) tab) r) (obj-at ob s fr heap)
                  (int64-listp ks) (equal (len ks) (len (g-st-vals (kadr r) st))) (st-ok st o s) (st-wf st s)
                  (not (mv-nth 0 (a-st (nth 4 r) (pairlis$ (g-st-vals (kadr r) st) ks) s st defs n)))
                  (equal (sc-orc name args fr heap tab st defs n o)
                         (list nil fr (put key (mv-nth 1 (a-st (nth 4 r) (pairlis$ (g-st-vals (kadr r) st) ks) s st defs n))
                                           heap))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (sc-orc ac-orc) (svals a-st st-ok st-wf obj-at okey st-src st-src-name lkp put)))))

(defthm obj-at-binding
  (implies (obj-at ob s fr heap)
           (and (equal (cdr (lkp ob fr)) (list* :obj :inout (okey ob fr)))
                (equal (lkp (okey ob fr) heap) (cons (okey ob fr) s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable obj-at okey))))

(defthm acl2-count-call-codes
  (implies (equal (kaddr x) (cons a cs)) (< (acl2-count cs) (acl2-count x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable kaddr kdr kar))))

;  st-ent-ok's facts, as g-st-fn-call states them
(defthm st-ent-ok-facts
  (implies (st-ent-ok r gdefs sigs st defs procs o b)
           (ent-let
            (and (not (mv-nth 0 (gfn))) sv (eq (g-role sv st) :stobj) (tself-ok fn st)
                 (eq (g-role fn st) :sub) (equal (g-obj fn st) formals)
                 (equal (g-st-dummies formals outs st) (list (list o :inout (g-comp sv st))))
                 (st-plain :term x nil st) (no-calls :term x sigs nil)
                 (not (g-role 'if st)) (not (g-role 'implies st)) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                 (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (member-equal o (g-formals vs)))
                 (equal (find-proc (g-sym fn nil) procs) (mv-nth 1 (gfn)))
                 (integerp b) (< (+ 9 (acl2-count (gbody (gsf 1)))) b))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(st-ent-ok) (theory 'minimal-theory)))))

; one entry: g-st-fn-call at r's fields
(defthm ent-call
  (let ((vs (g-st-vals (kadr r) st)))
    (implies (and (st-ent-ok r gdefs sigs st defs procs o b) (equal (g-sym (kar r) nil) fname)
                  (equal (kar xc) :call) (equal (kadr xc) fname) (equal (kaddr xc) (cons (list :var ob) cs))
                  (equal (cdr (lkp ob caller)) (list* :obj :inout key)) (svs-is cs ks caller heap)
                  (int64-listp ks) (equal (len ks) (len vs)) (equal (lkp key heap) (cons key s))
                  (st-ok st o s) (st-wf st s) (not (car (a-st (nth 4 r) (pairlis$ vs ks) s st defs n)))
                  (integerp fuel) (< (+ b (acl2-count cs)) fuel))
             (equal (f-ex xc caller heap procs fuel)
                    (mv :normal caller (put key (mv-nth 1 (a-st (nth 4 r) (pairlis$ vs ks) s st defs n)) heap)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)
           :use (st-ent-ok-facts
                 (:instance g-st-fn-call (fn (kar r)) (formals (kadr r)) (sv (car (kaddr r))) (x (nth 4 r))
                            (c (g-comp (car (kaddr r)) st)))))))

; the CALL's f-ex is sc-orc's answer
(defthm p-sorc-ent
  (let ((r (st-src-name (kadr x) tab)))
    (implies (and (st-ent-ok r gdefs sigs st defs procs o b) (equal (g-sym (kar r) nil) (kadr x))
                  (eq (kar x) :call) (not (mv-nth 0 (sc-orc (kadr x) (kaddr x) fr heap tab st defs n o)))
                  (integerp fuel) (< (+ b (acl2-count x)) fuel))
             (equal (f-ex x fr heap procs fuel)
                    (mv :normal (mv-nth 1 (sc-orc (kadr x) (kaddr x) fr heap tab st defs n o))
                        (mv-nth 2 (sc-orc (kadr x) (kaddr x) fr heap tab st defs n o))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (set-difference-theories
                       (union-theories '(eq mv-nth-0-car mv-nth-cons-k car-cons cdr-cons (:e posp) (:e binary-+) (:e unary--))
                                       (theory 'minimal-theory))
                       '((:definition mv-nth)))
           :use ((:instance sc-orc-parts (name (kadr x)) (args (kaddr x)))
                 (:instance obj-at-binding (ob (kadr (kar (kaddr x)))) (s (cdr (lkp (okey (kadr (kar (kaddr x))) fr) heap))))
                 (:instance acl2-count-call-codes (a (list :var (kadr (kar (kaddr x))))) (cs (kdr (kaddr x))))
                 (:instance svals-svs-is (cs (kdr (kaddr x))))
                 (:instance ent-call (r (st-src-name (kadr x) tab)) (fname (kadr x)) (xc x) (caller fr)
                            (ob (kadr (kar (kaddr x)))) (cs (kdr (kaddr x)))
                            (ks (mv-nth 1 (svals (kdr (kaddr x)) fr heap)))
                            (key (okey (kadr (kar (kaddr x))) fr)) (s (cdr (lkp (okey (kadr (kar (kaddr x))) fr) heap))))))))

(defthm p-sorc-h-holds
  (implies (tab-ok tab gdefs sigs st defs procs o b) (p-sorc-h procs b tab st defs n o))
  :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories '(p-sorc-h tab-ok) (theory 'minimal-theory)) '((:definition mv-nth)))
           :use ((:instance sc-orc-parts (name (kadr (mv-nth 0 (p-sorc-h-witness procs b tab st defs n o))))
                            (args (kaddr (mv-nth 0 (p-sorc-h-witness procs b tab st defs n o))))
                            (fr (mv-nth 1 (p-sorc-h-witness procs b tab st defs n o)))
                            (heap (mv-nth 2 (p-sorc-h-witness procs b tab st defs n o))))
                 (:instance st-src-name-ok (name (kadr (mv-nth 0 (p-sorc-h-witness procs b tab st defs n o)))))
                 (:instance p-sorc-ent (x (mv-nth 0 (p-sorc-h-witness procs b tab st defs n o)))
                            (fr (mv-nth 1 (p-sorc-h-witness procs b tab st defs n o)))
                            (heap (mv-nth 2 (p-sorc-h-witness procs b tab st defs n o)))
                            (fuel (mv-nth 3 (p-sorc-h-witness procs b tab st defs n o))))))))

; ---- c-sorc

(defun-sk c-sorc-h (o st tab defs n o0)
  (forall (f xs cs fr heap ks s)
    (implies (and (eq (g-role f st) :sub) (equal (len xs) (len (g-obj f st))) (obj-at o s fr heap) (svs-is cs ks fr heap) (int64s ks)
                  (not (mv-nth 0 (ac-orc f ks s tab st defs n o0))))
             (equal (sc-orc (g-sym f nil) (append (g-scs (g-obj f st) xs st) cs) fr heap tab st defs n o0)
                    (list nil fr (put (okey o fr) (mv-nth 1 (ac-orc f ks s tab st defs n o0)) heap))))))

; one stobj formal: g-scall-args passes its object alone
(defthm g-scs-one
  (implies (and (equal (g-st-dummies formals outs st) (list (list o io c))) (equal (len xs) (len formals)))
           (equal (g-scs formals xs st) (list (list :var o))))
  :hints (("Goal" :induct (g-scs formals xs st) :in-theory (disable g-role g-obj g-comp))))

(defthm g-st-dummies-none
  (implies (and (equal (g-st-dummies formals outs st) nil) (equal (len xs) (len formals)))
           (equal (g-scs formals xs st) nil))
  :hints (("Goal" :induct (g-scs formals xs st) :in-theory (disable g-role g-obj g-comp))))

(defthm ac-orc-parts
  (let ((r (st-src f tab)))
    (implies (not (mv-nth 0 (ac-orc f ks s tab st defs n o)))
             (and (consp r) (int64-listp ks) (st-ok st o s) (st-wf st s)
                  (equal (len ks) (len (g-st-vals (kadr r) st)))
                  (not (mv-nth 0 (a-st (nth 4 r) (pairlis$ (g-st-vals (kadr r) st) ks) s st defs n)))
                  (equal (mv-nth 1 (ac-orc f ks s tab st defs n o))
                         (mv-nth 1 (a-st (nth 4 r) (pairlis$ (g-st-vals (kadr r) st) ks) s st defs n))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (ac-orc) (a-st st-ok st-wf st-src)))))

(defthm sc-orc-call
  (implies (and (no-duplicatesp-equal (tab-names tab)) (consp (st-src f tab))
                (obj-at o s fr heap) (svs-is cs ks fr heap) (int64-listp ks)
                (not (mv-nth 0 (ac-orc f ks s tab st defs n o0))))
           (equal (sc-orc (g-sym f nil) (cons (list :var o) cs) fr heap tab st defs n o0)
                  (list nil fr (put (okey o fr) (mv-nth 1 (ac-orc f ks s tab st defs n o0)) heap))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (sc-orc) (ac-orc svals st-src st-src-name tab-names put g-sym obj-at okey svs-is lkp)))))

; the entry's facts c-sorc needs, about f itself
(defthm ent-src-facts
  (implies (and (tab-ok1 tab gdefs sigs st defs procs o b) (consp (st-src f tab)))
           (equal (g-st-dummies (g-obj f st) (list (car (kaddr (st-src f tab)))) st)
                  (list (list o :inout (g-comp (car (kaddr (st-src f tab))) st)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (set-difference-theories (union-theories '(kar-st-src) (theory 'minimal-theory)) '((:definition mv-nth)))
           :use (st-src-ok (:instance st-ent-ok-facts (r (st-src f tab)))))))

(defthm append-one (equal (append (list a) b) (cons a b)))

(defthm c-sorc-h-holds
  (implies (tab-ok tab gdefs sigs st defs procs o b) (c-sorc-h o st tab defs n o))
  :hints (("Goal" :do-not-induct t
           :in-theory (set-difference-theories (union-theories '(c-sorc-h tab-ok append-one int64-listp-true) (theory 'minimal-theory)) '((:definition mv-nth)))
           :use ((:instance ac-orc-parts (f (mv-nth 0 (c-sorc-h-witness o st tab defs n o)))
                            (ks (mv-nth 5 (c-sorc-h-witness o st tab defs n o))) (s (mv-nth 6 (c-sorc-h-witness o st tab defs n o))))
                 (:instance ent-src-facts (f (mv-nth 0 (c-sorc-h-witness o st tab defs n o))))
                 (:instance sc-orc-call (o0 o) (f (mv-nth 0 (c-sorc-h-witness o st tab defs n o)))
                            (cs (mv-nth 2 (c-sorc-h-witness o st tab defs n o)))
                            (fr (mv-nth 3 (c-sorc-h-witness o st tab defs n o))) (heap (mv-nth 4 (c-sorc-h-witness o st tab defs n o)))
                            (ks (mv-nth 5 (c-sorc-h-witness o st tab defs n o))) (s (mv-nth 6 (c-sorc-h-witness o st tab defs n o))))
                 (:instance g-scs-one (formals (g-obj (mv-nth 0 (c-sorc-h-witness o st tab defs n o)) st))
                            (xs (mv-nth 1 (c-sorc-h-witness o st tab defs n o)))
                            (outs (list (car (kaddr (st-src (mv-nth 0 (c-sorc-h-witness o st tab defs n o)) tab)))))
                            (io :inout) (c (g-comp (car (kaddr (st-src (mv-nth 0 (c-sorc-h-witness o st tab defs n o)) tab))) st)))))))

; ---- a-call-ok: a-st on a translated body keeps st-ok and st-wf (gst-sem)

(defthm stfn-wf
  (implies (and (stfn-hyps) (not (gsf 0)) (no-duplicatesp-equal (g-formals vs)) (em-nostobj (g-em vs) st)
                (member-equal o (st-objs st)))
           (and (st-ok st o (mv-nth 1 (a-st x (pairlis$ vs ks) s st defs n)))
                (st-wf st (mv-nth 1 (a-st x (pairlis$ vs ks) s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance gst-sem-holds (em (g-em vs)) (cnt 0) (locs nil) (fnames (sfn)) (env (pairlis$ vs ks))
                            (fr (undef-locals (g-locals (gsf 3)) (fb vs ks (put o (list* :obj :inout key) nil)))))
                 (:instance gst-sem-use (em (g-em vs)) (cnt 0) (locs nil) (fnames (sfn)) (env (pairlis$ vs ks))
                            (fr (undef-locals (g-locals (gsf 3)) (fb vs ks (put o (list* :obj :inout key) nil)))))
                 (:instance sfr-em-ok (locs (gsf 3)) (objs (st-objs st)))
                 (:instance sfr-decl (locs (gsf 3)) (fnames (sfn)))
                 (:instance sfr-obj-at (locs (gsf 3)) (objs (st-objs st)))
                 (:instance subsetp-append-r (a (st-objs st)) (b (g-formals vs)))))))

; g-st-fn-sem's hypotheses (but the caller and fuel): S' keeps st-ok and st-wf
(defthm g-st-fn-wf
  (let ((vs (g-st-vals formals st)) (outs (list sv)))
    (implies (and (not (mv-nth 0 (gfn))) sv (eq (g-role sv st) :stobj) (tself-ok fn st)
                  (equal (g-st-dummies formals outs st) (list (list o :inout c)))
                  (stfn-hyps0))
             (and (st-ok st o (mv-nth 1 (a-st x (pairlis$ vs ks) s st defs n)))
                  (st-wf st (mv-nth 1 (a-st x (pairlis$ vs ks) s st defs n))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-st-fn g-stmt g-reaches g-called g-fcalls g-ccalls g-has g-st-dummies g-dummies g-locals g-em
                               g-formals g-st-vals g-role g-lits f-bind f-ex-list sx-list a-st undef-locals fb stfn-run
                               st-plain no-calls lf-ok st-ok st-wf g-st-fn-err stl-holds f-ex-list-open stfn-body sx-list-is-f-ex-list)
           :use (g-st-fn-err (:instance stfn-wf (vs (g-st-vals formals st)) (outs (list sv)))
                 (:instance stl-holds (em (g-em (g-st-vals formals st))) (cnt 0) (locs nil)
                            (fnames (append (g-formals (g-st-vals formals st)) (st-objs st))) (outs (list sv)))
                 (:instance st-ok-necc (x sv))
                 (:instance g-obj-st-objs (x sv))))))

(defun-sk a-call-ok-h (st o tab defs n o0)
  (forall (f ks s)
    (implies (and (not (mv-nth 0 (ac-orc f ks s tab st defs n o0))) (st-ok st o s) (st-wf st s))
             (and (st-ok st o (mv-nth 1 (ac-orc f ks s tab st defs n o0)))
                  (st-wf st (mv-nth 1 (ac-orc f ks s tab st defs n o0)))))))

(defthm lkp-one (equal (lkp k (list (cons k s))) (cons k s)))

; one entry: ac-orc keeps st-ok and st-wf
(defthm a-call-ok-ent
  (implies (and (st-ent-ok (st-src f tab) gdefs sigs st defs procs o b) (not (mv-nth 0 (ac-orc f ks s tab st defs n o))))
           (and (st-ok st o (mv-nth 1 (ac-orc f ks s tab st defs n o))) (st-wf st (mv-nth 1 (ac-orc f ks s tab st defs n o)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (set-difference-theories (union-theories '(mv-nth-0-car lkp-one) (theory 'minimal-theory))
                                               '((:definition mv-nth)))
           :use ((:instance st-ent-ok-facts (r (st-src f tab))) ac-orc-parts
                 (:instance g-st-fn-wf
                            (fn (kar (st-src f tab))) (formals (kadr (st-src f tab))) (sv (car (kaddr (st-src f tab))))
                            (x (nth 4 (st-src f tab))) (c (g-comp (car (kaddr (st-src f tab))) st))
                            (key 0) (heap (list (cons 0 s))))))))

(defthm a-call-ok-h-holds
  (implies (tab-ok tab gdefs sigs st defs procs o b) (a-call-ok-h st o tab defs n o))
  :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories '(a-call-ok-h tab-ok) (theory 'minimal-theory)) '((:definition mv-nth)))
           :use ((:instance ac-orc-parts (f (mv-nth 0 (a-call-ok-h-witness st o tab defs n o)))
                            (ks (mv-nth 1 (a-call-ok-h-witness st o tab defs n o))) (s (mv-nth 2 (a-call-ok-h-witness st o tab defs n o))))
                 (:instance st-src-ok (f (mv-nth 0 (a-call-ok-h-witness st o tab defs n o))))
                 (:instance a-call-ok-ent (f (mv-nth 0 (a-call-ok-h-witness st o tab defs n o)))
                            (ks (mv-nth 1 (a-call-ok-h-witness st o tab defs n o))) (s (mv-nth 2 (a-call-ok-h-witness st o tab defs n o))))))))
