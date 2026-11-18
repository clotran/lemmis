; gen-stinst: the stobj-call oracles' functional instance (GEN.md 4 (4a)).
; sxc/sxc-list and a-stcall copied with gen-stdisch's concrete oracles
; (sc-orc for s-call-val, ac-orc for a-call-val), and gen-stcall's
; sxc-ok-is-f-ex-list and gen-stcallst's gst-callst instantiated with them:
; p-sorc, c-sorc and a-call-ok become p-sorc-h, c-sorc-h and a-call-ok-h,
; which tab-ok gives (gen-stdisch), so both theorems hold with no oracle
; hypothesis, for any table of source subroutines satisfying the decidable
; tab-ok.

(in-package "ACL2")

(include-book "gen-stdisch")

(mutual-recursion
 (defun sxc-h (x frame heap tab st defs n o)
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
                  (c (sxc-list-h (kaddr x) frame heap tab st defs n o))
                  (t (sxc-list-h (kadddr x) frame heap tab st defs n o)))))
     (:select (mv-let (err k) (sv (kadr x) frame heap)
                (cond (err (mv (errst err) frame heap))
                      ((not (integerp k)) (mv (errst :type) frame heap))
                      (t (let ((arm (lkp k (kaddr x))))
                           (sxc-list-h (if arm (kadr arm) (kadddr x)) frame heap tab st defs n o))))))
     ((:cycle :exit :return) (mv (kar x) frame heap))
     (:call (mv-let (err fr2 h2) (sc-orc (kadr x) (kaddr x) frame heap tab st defs n o)
              (if err (mv (errst err) frame heap) (mv :normal fr2 h2))))
     (otherwise (mv (errst :syntax) frame heap))))
 (defun sxc-list-h (ss frame heap tab st defs n o)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) (mv :normal frame heap)
     (mv-let (sta fr2 h2) (sxc-h (car ss) frame heap tab st defs n o)
       (if (eq sta :normal) (sxc-list-h (cdr ss) fr2 h2 tab st defs n o) (mv sta fr2 h2))))))

; (the oracle's parameters apart from the caller's st, defs, n: the functional instance needs it)
(defun a-stcall-h (x env s st defs n tab st0 defs0 n0 o0)
  (mv-let (e ks) (a-sx-list (g-cvals (g-obj (car x) st) (cdr x) st) env s st defs n)
    (if e (mv e s nil) (ac-orc (car x) ks s tab st0 defs0 n0 o0))))

(in-theory (disable sxc-h sxc-list-h a-stcall-h))

;; the functional instance's hints, on its top-level subgoals: the instance
;; itself (naming a function of `main`) closes propositionally; a constraint naming a witness
;; (a defun-sk's definition) gets hdef, one naming a defun-sk but no witness
;; (its necc) gets hnecc, the others (sxc's, a-stcall's definitions) hother
(defun stinst-occ (syms x) (declare (xargs :mode :program))
  (if (atom x) (member-eq x syms) (or (stinst-occ syms (car x)) (stinst-occ syms (cdr x)))))

(defun stinst-hint (id clause main wits sks hdef hnecc hother)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :pool-lst) nil) (equal (access clause-id id :primes) 0)
       (equal (len (access clause-id id :case-lst)) 1)
       (cond ((stinst-occ main clause) '(:in-theory (theory 'minimal-theory)))
             ((stinst-occ wits clause) hdef)
             ((stinst-occ sks clause) hnecc)
             (t hother))))

;; the functional instance, with fresh names for the oracles' parameters
(defthm sxc-h-ok-generic
  (implies (and (p-sorc-h procs b tab0 st0 defs0 n0 o0) (natp b)
                (not (errstp (mv-nth 0 (sxc-list-h ss fr heap tab0 st0 defs0 n0 o0))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxc-list-h ss fr heap tab0 st0 defs0 n0 o0)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable sc-orc p-sorc-h tab-ok f-ex-list f-ex sxc-h sxc-list-h)
           :use (
                 (:functional-instance sxc-ok-is-f-ex-list
                  (s-call-val (lambda (name args fr heap) (sc-orc name args fr heap tab0 st0 defs0 n0 o0)))
                  (sxc (lambda (x frame heap) (sxc-h x frame heap tab0 st0 defs0 n0 o0)))
                  (sxc-list (lambda (ss frame heap) (sxc-list-h ss frame heap tab0 st0 defs0 n0 o0)))
                  (p-sorc (lambda (procs b) (p-sorc-h procs b tab0 st0 defs0 n0 o0)))
                  (p-sorc-witness (lambda (procs b) (p-sorc-h-witness procs b tab0 st0 defs0 n0 o0))))))
          (stinst-hint id clause '(f-ex-list) '(p-sorc-h-witness) '(p-sorc-h)
           '(:in-theory (union-theories '(p-sorc-h kadr kaddr kadddr) (theory 'minimal-theory)))
           '(:in-theory (union-theories '(kadr kaddr kadddr) (theory 'minimal-theory))
             :use ((:instance p-sorc-h-necc (tab tab0) (st st0) (defs defs0) (n n0) (o o0))))
           '(:in-theory (disable sc-orc p-sorc-h f-ex f-ex-list sxc-h sxc-list-h)
             :expand ((:free (x frame heap) (sxc-h x frame heap tab0 st0 defs0 n0 o0))
                      (:free (ss frame heap) (sxc-list-h ss frame heap tab0 st0 defs0 n0 o0)))))))

; wherever sxc-list-h answers no error, f-ex-list is sxc-list-h, for a table with tab-ok
(defthm sxc-h-ok-is-f-ex-list
  (implies (and (tab-ok tab gdefs sigs st defs procs o b) (natp b)
                (not (errstp (mv-nth 0 (sxc-list-h ss fr heap tab st defs n o))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxc-list-h ss fr heap tab st defs n o)))
  :hints (("Goal" :in-theory (disable p-sorc-h-holds tab-ok p-sorc-h)
           :use (p-sorc-h-holds (:instance sxc-h-ok-generic (tab0 tab) (st0 st) (defs0 defs) (n0 n) (o0 o))))))

; ---- gst-callst with the concrete oracles

; c-sorc-h and a-call-ok-h with the oracles' st apart from the caller's (the
; functional instance's lambdas need it), and given by them when they agree
(defun-sk c-sorc-h2 (o st tab st0 defs n o0)
  (forall (f xs cs fr heap ks s)
    (implies (and (eq (g-role f st) :sub) (equal (len xs) (len (g-obj f st))) (obj-at o s fr heap) (svs-is cs ks fr heap) (int64s ks)
                  (not (mv-nth 0 (ac-orc f ks s tab st0 defs n o0))))
             (equal (sc-orc (g-sym f nil) (append (g-scs (g-obj f st) xs st) cs) fr heap tab st0 defs n o0)
                    (list nil fr (put (okey o fr) (mv-nth 1 (ac-orc f ks s tab st0 defs n o0)) heap))))))

(defun-sk a-call-ok-h2 (st o tab st0 defs n o0)
  (forall (f ks s)
    (implies (and (not (mv-nth 0 (ac-orc f ks s tab st0 defs n o0))) (st-ok st o s) (st-wf st s))
             (and (st-ok st o (mv-nth 1 (ac-orc f ks s tab st0 defs n o0))) (st-wf st (mv-nth 1 (ac-orc f ks s tab st0 defs n o0)))))))

(in-theory (disable c-sorc-h2 a-call-ok-h2))

(defthm c-sorc-h2-from-h
  (implies (c-sorc-h o st tab defs n o0) (c-sorc-h2 o st tab st defs n o0))
  :hints (("Goal" :in-theory (e/d (c-sorc-h2) (c-sorc-h sc-orc ac-orc))
           :use (:instance c-sorc-h-necc
                 (f (mv-nth 0 (c-sorc-h2-witness o st tab st defs n o0))) (xs (mv-nth 1 (c-sorc-h2-witness o st tab st defs n o0)))
                 (cs (mv-nth 2 (c-sorc-h2-witness o st tab st defs n o0))) (fr (mv-nth 3 (c-sorc-h2-witness o st tab st defs n o0)))
                 (heap (mv-nth 4 (c-sorc-h2-witness o st tab st defs n o0))) (ks (mv-nth 5 (c-sorc-h2-witness o st tab st defs n o0)))
                 (s (mv-nth 6 (c-sorc-h2-witness o st tab st defs n o0)))))))

(defthm a-call-ok-h2-from-h
  (implies (a-call-ok-h st o tab defs n o0) (a-call-ok-h2 st o tab st defs n o0))
  :hints (("Goal" :in-theory (e/d (a-call-ok-h2) (a-call-ok-h ac-orc))
           :use (:instance a-call-ok-h-necc
                 (f (mv-nth 0 (a-call-ok-h2-witness st o tab st defs n o0))) (ks (mv-nth 1 (a-call-ok-h2-witness st o tab st defs n o0)))
                 (s (mv-nth 2 (a-call-ok-h2-witness st o tab st defs n o0)))))))

(defthm gst-callst-generic
  (implies (and (eq (g-role (car x) st) :sub) (not (g-upd (g-obj (car x) st) (cdr x) st))
                (not (car (g-callst x em cnt locs sigs fnames st nil)))
                (not (car (a-stcall-h x env s st defs n tab0 st0 defs0 n0 o0)))
                (c-sorc-h2 o st tab0 st0 defs0 n0 o0) (a-call-ok-h2 st o tab0 st0 defs0 n0 o0)
                (no-calls :list (cvs) sigs nil) (em-ok em env fr)
                (decl-ok (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st))
           (and (equal (car (sxc-list-h (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap tab0 st0 defs0 n0 o0)) :normal)
                (equal (mv-nth 2 (sxc-list-h (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap tab0 st0 defs0 n0 o0))
                       (put (okey o fr) (mv-nth 1 (a-stcall-h x env s st defs n tab0 st0 defs0 n0 o0)) heap))
                (st-ok st o (mv-nth 1 (a-stcall-h x env s st defs n tab0 st0 defs0 n0 o0)))
                (st-wf st (mv-nth 1 (a-stcall-h x env s st defs n tab0 st0 defs0 n0 o0)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable sc-orc ac-orc c-sorc-h2 a-call-ok-h2 sxc-h sxc-list-h a-stcall-h g-callst g-role st-ok st-wf)
           :use ((:functional-instance gst-callst
                  (s-call-val (lambda (name args fr heap) (sc-orc name args fr heap tab0 st0 defs0 n0 o0)))
                  (sxc (lambda (x frame heap) (sxc-h x frame heap tab0 st0 defs0 n0 o0)))
                  (sxc-list (lambda (ss frame heap) (sxc-list-h ss frame heap tab0 st0 defs0 n0 o0)))
                  (a-call-val (lambda (f ks s) (ac-orc f ks s tab0 st0 defs0 n0 o0)))
                  (a-stcall (lambda (x env s st defs n) (a-stcall-h x env s st defs n tab0 st0 defs0 n0 o0)))
                  (c-sorc (lambda (o st) (c-sorc-h2 o st tab0 st0 defs0 n0 o0)))
                  (c-sorc-witness (lambda (o st) (c-sorc-h2-witness o st tab0 st0 defs0 n0 o0)))
                  (a-call-ok (lambda (st o) (a-call-ok-h2 st o tab0 st0 defs0 n0 o0)))
                  (a-call-ok-witness (lambda (st o) (a-call-ok-h2-witness st o tab0 st0 defs0 n0 o0))))))
          (stinst-hint id clause '(g-callst) '(c-sorc-h2-witness a-call-ok-h2-witness) '(c-sorc-h2 a-call-ok-h2)
           '(:in-theory (union-theories '(c-sorc-h2 a-call-ok-h2 kadr kaddr kadddr g-obj (:type-prescription st-ok) (:type-prescription st-wf)) (theory 'minimal-theory)))
           '(:in-theory (union-theories '(kadr kaddr kadddr g-obj) (theory 'minimal-theory))
             :use ((:instance c-sorc-h2-necc (tab tab0) (defs defs0) (n n0))
                   (:instance a-call-ok-h2-necc (tab tab0) (defs defs0) (n n0))))
           '(:in-theory (disable sc-orc ac-orc sxc-h sxc-list-h a-stcall-h)
             :expand ((:free (x frame heap) (sxc-h x frame heap tab0 st0 defs0 n0 o0))
                      (:free (ss frame heap) (sxc-list-h ss frame heap tab0 st0 defs0 n0 o0))
                      (:free (x env s st defs n) (a-stcall-h x env s st defs n tab0 st0 defs0 n0 o0)))))))

; gst-callst with no oracle hypothesis: for a table with tab-ok
(defthm gst-callst-h
  (implies (and (tab-ok tab gdefs tsigs st defs procs o b)
                (eq (g-role (car x) st) :sub) (not (g-upd (g-obj (car x) st) (cdr x) st))
                (not (car (g-callst x em cnt locs sigs fnames st nil)))
                (not (car (a-stcall-h x env s st defs n tab st defs n o)))
                (no-calls :list (cvs) sigs nil) (em-ok em env fr)
                (decl-ok (mv-nth 3 (g-callst x em cnt locs sigs fnames st nil)) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (st-wf st s) (obj-at o s fr heap) (sn-hyps) (em-nostobj em st))
           (and (equal (car (sxc-list-h (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap tab st defs n o)) :normal)
                (equal (mv-nth 2 (sxc-list-h (mv-nth 1 (g-callst x em cnt locs sigs fnames st nil)) fr heap tab st defs n o))
                       (put (okey o fr) (mv-nth 1 (a-stcall-h x env s st defs n tab st defs n o)) heap))
                (st-ok st o (mv-nth 1 (a-stcall-h x env s st defs n tab st defs n o)))
                (st-wf st (mv-nth 1 (a-stcall-h x env s st defs n tab st defs n o)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable tab-ok c-sorc-h a-call-ok-h c-sorc-h2 a-call-ok-h2 c-sorc-h-holds a-call-ok-h-holds
                               sxc-list-h a-stcall-h g-callst)
           :use ((:instance c-sorc-h-holds (sigs tsigs)) (:instance a-call-ok-h-holds (sigs tsigs))
                 (:instance c-sorc-h2-from-h (o0 o)) (:instance a-call-ok-h2-from-h (o0 o))
                 (:instance gst-callst-generic (tab0 tab) (st0 st) (defs0 defs) (n0 n) (o0 o))))))
