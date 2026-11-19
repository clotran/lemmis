; gen-sfinst: the functional instance for value functions given the stobj
; (GEN.md "What remains" 4b, step 3). svf/svlf/sxf/sxf-list and gs-sem-f
; copied with gen-sfdisch's concrete oracle s-fn-val-h (its defs, st and o
; apart: the functional instance's lambdas need them), and gen-sflits'
; sxf-lits-ok-is-f-ex-list and gen-sfthm's gs-sem-holds-f instantiated with
; them: p-sflits and sf-orc become p-sflits-h and sf-orc-h, which sfd-ok
; gives (gen-sfdisch), so both hold with no oracle hypothesis, for any defs
; satisfying the decidable sfd-ok.

(in-package "ACL2")

(include-book "gen-sfdisch")

(mutual-recursion
 (defun svf-h (e fr heap defs0 st0 o0)
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
    (:elem (mv-let (err i) (svf-h (kadddr e) fr heap defs0 st0 o0)
             (if err (mv err nil)
               (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
                 (if err (mv err nil) (read-elem v i))))))
    (:neg (mv-let (err a) (svf-h (kadr e) fr heap defs0 st0 o0) (if err (mv err nil) (arith :sub 0 a))))
    (:not (mv-let (err a) (svf-h (kadr e) fr heap defs0 st0 o0)
            (cond (err (mv err nil)) ((booleanp a) (mv nil (not a))) (t (mv :type nil)))))
    ((:add :sub :mul :eq :lt :le :ge :max)
     (mv-let (err a) (svf-h (kadr e) fr heap defs0 st0 o0)
       (if err (mv err nil)
         (mv-let (err b) (svf-h (kaddr e) fr heap defs0 st0 o0)
           (if err (mv err nil) (binop (kar e) a b))))))
    (:fcall (let ((a (kaddr e)))
              (mv-let (err key intent) (obj-of (kadr (kar a)) fr)
                (declare (ignore intent))
                (cond ((not (eq (kar (kar a)) :var)) (mv :syntax nil))
                      (err (mv err nil))
                      (t (mv-let (err ks) (svlf-h (kdr a) fr heap defs0 st0 o0)
                           (if err (mv err nil)
                             (mv-let (err v) (s-fn-val-h (kadr e) (cdr (lkp key heap)) ks defs0 st0 o0) (mv err v)))))))))
    (otherwise (mv :syntax nil))))
 (defun svlf-h (cs fr heap defs0 st0 o0)
  (declare (xargs :measure (acl2-count cs)))
  (if (atom cs) (mv nil nil)
    (mv-let (err v) (svf-h (car cs) fr heap defs0 st0 o0)
      (if err (mv err nil)
        (mv-let (err vs) (svlf-h (cdr cs) fr heap defs0 st0 o0)
          (if err (mv err nil) (mv nil (cons v vs)))))))))

(mutual-recursion
 (defun sxf-h (x frame heap defs0 st0 o0)
   (declare (xargs :measure (acl2-count x)))
   (case (kar x)
     (:assign
      (mv-let (err v) (svf-h (kaddr x) frame heap defs0 st0 o0)
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
                                  (t (mv-let (err i) (svf-h (kadddr d) frame heap defs0 st0 o0)
                                       (cond (err (mv (errst err) frame heap))
                                             ((not (and (farrayp (cdr p)) (integerp i))) (mv (errst :type) frame heap))
                                             ((not (and (<= 0 i) (< i (len (cddr p))))) (mv (errst :bounds) frame heap))
                                             (t (mv :normal frame
                                                    (put key (put (kaddr d) (cons :array (update-nth i v (cddr p))) comps)
                                                         heap))))))))))))
              (otherwise (mv (errst :syntax) frame heap)))))))
     (:if (mv-let (err c) (svf-h (kadr x) frame heap defs0 st0 o0)
            (cond (err (mv (errst err) frame heap))
                  ((not (booleanp c)) (mv (errst :type) frame heap))
                  (c (sxf-list-h (kaddr x) frame heap defs0 st0 o0))
                  (t (sxf-list-h (kadddr x) frame heap defs0 st0 o0)))))
     (:select (mv-let (err k) (svf-h (kadr x) frame heap defs0 st0 o0)
                (cond (err (mv (errst err) frame heap))
                      ((not (integerp k)) (mv (errst :type) frame heap))
                      (t (let ((arm (lkp k (kaddr x))))
                           (sxf-list-h (if arm (kadr arm) (kadddr x)) frame heap defs0 st0 o0))))))
     ((:cycle :exit :return) (mv (kar x) frame heap))
     (otherwise (mv (errst :syntax) frame heap))))
 (defun sxf-list-h (ss frame heap defs0 st0 o0)
   (declare (xargs :measure (acl2-count ss)))
   (if (atom ss) (mv :normal frame heap)
     (mv-let (st fr2 h2) (sxf-h (car ss) frame heap defs0 st0 o0)
       (if (eq st :normal) (sxf-list-h (cdr ss) fr2 h2 defs0 st0 o0) (mv st fr2 h2))))))

(defun gs-sem-f-h (x em cnt locs sigs fnames st env s defs n fr heap o defs0 st0 o0)
  (mv-let (e ss c ty cnt2 locs2) (g-sexpr x em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-sxf x env s st defs n)
      (implies (and (not e) (not ae) (sfc-ok :term x sigs st) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (sf-orc-h sigs defs st o defs0 st0 o0) (not (consp (lkp 'mv-nth defs)))
                    (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (obj-is o s fr heap))
               (mv-let (stt fr2 h2) (sxf-list-h ss fr heap defs0 st0 o0)
                 (mv-let (fe fvv) (svf-h c fr2 heap defs0 st0 o0)
                   (and (equal stt :normal) (equal h2 heap) (not fe) (equal fvv v) (scalar-ok ty v))))))))

(in-theory (disable svf-h svlf-h sxf-h sxf-list-h gs-sem-f-h))

;; the functional instance's hints, on its top-level subgoals (gen-stinst's
;; stinst-hint): the instance itself (naming a function of `main`) closes
;; propositionally; a constraint naming a witness gets hdef, one naming a
;; defun-sk but no witness hnecc, the others (the copies' definitions) hother
(defun sfi-occ (syms x) (declare (xargs :mode :program))
  (if (atom x) (member-eq x syms) (or (sfi-occ syms (car x)) (sfi-occ syms (cdr x)))))

(defun sfi-hint (id clause main wits sks hdef hnecc hother)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :pool-lst) nil) (equal (access clause-id id :primes) 0)
       (equal (len (access clause-id id :case-lst)) 1)
       (cond ((sfi-occ main clause) '(:in-theory (theory 'minimal-theory)))
             ((sfi-occ '(gs-sem-f-h) clause) hother)
             ((sfi-occ wits clause) hdef)
             ((sfi-occ sks clause) hnecc)
             (t hother))))

(defmacro sfi-other ()
  ''(:in-theory (disable s-fn-val-h svf-h svlf-h sxf-h sxf-list-h gs-sem-f-h g-sexpr a-sxf sf-orc-h p-sflits-h)
     :expand ((svf-h e fr heap defs0 st0 o0) (svlf-h cs fr heap defs0 st0 o0) (sxf-h x frame heap defs0 st0 o0)
              (sxf-list-h ss frame heap defs0 st0 o0)
              (gs-sem-f-h x em cnt locs sigs fnames st env s defs n fr heap o defs0 st0 o0))))

;; sxf-lits-ok-is-f-ex-list, with fresh names for the oracle's parameters
(defthm sxf-h-ok-generic
  (implies (and (p-sflits-h procs b defs0 st0 o0) (natp b)
                (not (errstp (mv-nth 0 (sxf-list-h ss fr heap defs0 st0 o0))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxf-list-h ss fr heap defs0 st0 o0)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:functional-instance sxf-lits-ok-is-f-ex-list
                  (s-fn-val (lambda (name s ks) (s-fn-val-h name s ks defs0 st0 o0)))
                  (svf (lambda (e fr heap) (svf-h e fr heap defs0 st0 o0)))
                  (svlf (lambda (cs fr heap) (svlf-h cs fr heap defs0 st0 o0)))
                  (sxf (lambda (x frame heap) (sxf-h x frame heap defs0 st0 o0)))
                  (sxf-list (lambda (ss frame heap) (sxf-list-h ss frame heap defs0 st0 o0)))
                  (p-sflits (lambda (procs b) (p-sflits-h procs b defs0 st0 o0)))
                  (p-sflits-witness (lambda (procs b) (p-sflits-h-witness procs b defs0 st0 o0))))))
          (sfi-hint id clause '(f-ex-list) '(p-sflits-h-witness) '(p-sflits-h)
           '(:in-theory (union-theories '(p-sflits-h) (theory 'minimal-theory)))
           '(:in-theory (theory 'minimal-theory) :use ((:instance p-sflits-h-necc)))
           (sfi-other))))

; wherever sxf-list-h answers no error, f-ex-list is sxf-list-h, for defs with sfd-ok
(defthm sxf-h-ok-is-f-ex-list
  (implies (and (sfd-ok defs gdefs sigs st procs o b) (natp b)
                (not (errstp (mv-nth 0 (sxf-list-h ss fr heap defs st o))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxf-list-h ss fr heap defs st o)))
  :hints (("Goal" :in-theory (disable p-sflits-h-holds sfd-ok p-sflits-h)
           :use (p-sflits-h-holds (:instance sxf-h-ok-generic (defs0 defs) (st0 st) (o0 o))))))

;; gs-sem-holds-f, the same way
(defthm gs-sem-h-generic
  (implies (and (sn-hyps) (em-nostobj em st))
           (gs-sem-f-h x em cnt locs sigs fnames st env s defs n fr heap o defs0 st0 o0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:functional-instance gs-sem-holds-f
                  (s-fn-val (lambda (name s ks) (s-fn-val-h name s ks defs0 st0 o0)))
                  (svf (lambda (e fr heap) (svf-h e fr heap defs0 st0 o0)))
                  (svlf (lambda (cs fr heap) (svlf-h cs fr heap defs0 st0 o0)))
                  (sxf (lambda (x frame heap) (sxf-h x frame heap defs0 st0 o0)))
                  (sxf-list (lambda (ss frame heap) (sxf-list-h ss frame heap defs0 st0 o0)))
                  (sf-orc (lambda (sigs defs st o) (sf-orc-h sigs defs st o defs0 st0 o0)))
                  (sf-orc-witness (lambda (sigs defs st o) (sf-orc-h-witness sigs defs st o defs0 st0 o0)))
                  (gs-sem-f (lambda (x em cnt locs sigs fnames st env s defs n fr heap o)
                              (gs-sem-f-h x em cnt locs sigs fnames st env s defs n fr heap o defs0 st0 o0))))))
          (sfi-hint id clause '(subsetp-equal) '(sf-orc-h-witness) '(sf-orc-h)
           '(:in-theory (union-theories '(sf-orc-h (:type-prescription scalar-ok) (:type-prescription st-ok) (:type-prescription int64-listp)) (theory 'minimal-theory)) :use ((:instance sf-orc-h-necc)))
           '(:in-theory (theory 'minimal-theory) :use ((:instance sf-orc-h-necc)))
           (sfi-other))))

; gs-sem on svf-h against a-sxf, the oracle's hypothesis discharged by sfd-ok:
; g-sexpr's statements run normally, the heap unchanged, and its code's value
; is a-sxf's, of g-sexpr's type
(defthm gs-sem-holds-h
  (implies (and (sn-hyps) (em-nostobj em st) (sfd-ok defs gdefs sigs st procs o b))
           (mv-let (e ss c ty cnt2 locs2) (g-sexpr x em cnt locs sigs fnames st)
             (declare (ignore cnt2))
             (mv-let (ae v) (a-sxf x env s st defs n)
               (implies (and (not e) (not ae) (sfc-ok :term x sigs st) (em-ok em env fr) (decl-ok locs2 fr)
                             (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                             (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                             (st-ok st o s) (obj-is o s fr heap))
                        (mv-let (stt fr2 h2) (sxf-list-h ss fr heap defs st o)
                          (mv-let (fe fvv) (svf-h c fr2 heap defs st o)
                            (and (equal stt :normal) (equal h2 heap) (not fe) (equal fvv v) (scalar-ok ty v))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable sfd-ok sf-orc-h-holds g-sexpr a-sxf svf-h sxf-list-h sfc-ok em-ok decl-ok st-ok obj-is)
           :use (sf-orc-h-holds (:instance gs-sem-h-generic (defs0 defs) (st0 st) (o0 o)))
           :expand ((gs-sem-f-h x em cnt locs sigs fnames st env s defs n fr heap o defs st o)))))
