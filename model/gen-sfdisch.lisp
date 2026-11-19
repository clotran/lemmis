; gen-sfdisch: the oracle s-fn-val made concrete, and sf-orc and p-sflits
; discharged (GEN.md "What remains" 4b, step 3). The table is defs itself:
; each entry `(fn formals x)` a value function reading the stobj, x
; call-free, translated by g-st-fn as `(fn formals (nil) t x)`, its
; procedure procs', its sig's formals its own -- `sfd-ok`, decidable on a
; given defs (so an instance discharges it by evaluation).
;   s-fn-val-h (name s ks)  a-sx of the entry named name on the value
;                           formals bound to ks, at a fuel where a-sx answers
;                           no error (defchoose sfn-fuel), when ks are int64,
;                           as many as the value formals, and S has st-ok
; Proved: `sf-orc-h-holds` (sf-orc with the concrete oracle: a-sxf of a
; call-free body is a-sx; a-sx ignores the stobj formal's binding, nil in
; sf-orc's env; a-sx-mono makes the fuels agree; the type by rfn-run) and
; `p-sflits-h-holds` (p-sflits with it, by g-sret-fn-sem).

(in-package "ACL2")

(include-book "gen-sflits")
(include-book "gen-sfthm")
(include-book "gen-stretfn")

; ---- a-sx reads the env only at names that are not stobjs

(defun-sk env-ns (e1 e2 st)
  (forall y (implies (not (eq (g-role y st) :stobj)) (equal (lkp y e1) (lkp y e2)))))

(in-theory (disable env-ns))

(defthm g-st-free-if-parts
  (implies (and (consp x) (not (equal (car x) 'quote)) (not (consp (car x))) (g-st-free x st)
                (not (eq (g-role nil st) :stobj)))
           (and (g-st-free (kadr x) st) (g-st-free (kaddr x) st) (g-st-free (kadddr x) st) (g-st-free-list (cdr x) st)))
  :hints (("Goal" :expand ((g-st-free x st) (g-st-free-list (cdr x) st) (g-st-free-list (cddr x) st)
                           (g-st-free-list (cdddr x) st) (g-st-free nil st))
           :in-theory (enable kar kdr kadr kaddr kadddr))))

(defthm g-st-free-lam-parts
  (implies (and (consp x) (consp (car x)) (g-st-free x st)) (g-st-free-list (cdr x) st))
  :hints (("Goal" :expand ((g-st-free x st)))))

(defthm g-st-free-list-parts
  (implies (and (consp x) (g-st-free-list x st)) (and (g-st-free (car x) st) (g-st-free-list (cdr x) st)))
  :hints (("Goal" :expand ((g-st-free-list x st)))))

; the claims, named, so the inductions below only chain step lemmas
(defun-nx aev-ok (flag x e1 e2 defs n st)
  (if (eq flag :one)
      (implies (g-st-free x st) (equal (a-ev x e1 defs n) (a-ev x e2 defs n)))
    (implies (g-st-free-list x st) (equal (a-ev-list x e1 defs n) (a-ev-list x e2 defs n)))))

(defthm g-st-free-nil (implies (not (eq (g-role nil st) :stobj)) (g-st-free nil st)))

(defthm a-sx-zp-f (implies (zp n) (equal (a-sx x env s st defs n) (mv :fuel nil))) :hints (("Goal" :expand ((a-sx x env s st defs n)))))

(defthm a-sx-list-zp-f (implies (zp n) (equal (a-sx-list x env s st defs n) (mv :fuel nil)))
  :hints (("Goal" :expand ((a-sx-list x env s st defs n)))))

(defmacro aev-thy ()
  '(e/d (aev-ok) (g-st-free g-st-free-list a-prim g-role a-ev a-ev-list lkp)))

(defthm aev-zp (implies (zp n) (aev-ok flag x e1 e2 defs n st))
  :hints (("Goal" :in-theory (aev-thy))))

(defthm aev-atom
  (implies (and (env-ns e1 e2 st) (not (zp n)) (atom x)) (aev-ok :one x e1 e2 defs n st))
  :hints (("Goal" :in-theory (aev-thy) :expand ((a-ev x e1 defs n) (a-ev x e2 defs n) (g-st-free x st))
           :use ((:instance env-ns-necc (y x))))))

(defthm aev-cons
  (implies (and (not (eq (g-role nil st) :stobj)) (not (zp n)) (consp x)
                (aev-ok :one (kadr x) e1 e2 defs (1- n) st) (aev-ok :one (kaddr x) e1 e2 defs (1- n) st)
                (aev-ok :one (kadddr x) e1 e2 defs (1- n) st) (aev-ok :list (cdr x) e1 e2 defs (1- n) st))
           (aev-ok :one x e1 e2 defs n st))
  :hints (("Goal" :in-theory (aev-thy) :expand ((:free (n) (a-ev x e1 defs n)) (:free (n) (a-ev x e2 defs n)))
           :cases ((eq (car x) 'quote) (eq (car x) 'if) (consp (car x))))))

(defthm aevl-atom (implies (and (not (zp n)) (atom x)) (aev-ok :list x e1 e2 defs n st))
  :hints (("Goal" :in-theory (aev-thy) :expand ((a-ev-list x e1 defs n) (a-ev-list x e2 defs n)))))

(defthm aevl-cons
  (implies (and (not (zp n)) (consp x) (aev-ok :one (car x) e1 e2 defs (1- n) st) (aev-ok :list (cdr x) e1 e2 defs (1- n) st))
           (aev-ok :list x e1 e2 defs n st))
  :hints (("Goal" :in-theory (aev-thy) :expand ((a-ev-list x e1 defs n) (a-ev-list x e2 defs n)))))

(defthm aev-ok-list
  (implies (and (not (equal flag :one)) (not (equal flag :list))) (equal (aev-ok flag x e1 e2 defs n st) (aev-ok :list x e1 e2 defs n st))))

(in-theory (disable aev-ok))

(defun aev3-ind (flag x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (if (eq flag :one)
        (if (atom x) nil
          (list (aev3-ind :one (kadr x) (1- n)) (aev3-ind :one (kaddr x) (1- n)) (aev3-ind :one (kadddr x) (1- n))
                (aev3-ind :list (cdr x) (1- n))))
      (if (atom x) nil (list (aev3-ind :one (car x) (1- n)) (aev3-ind :list (cdr x) (1- n)))))))

(defthm aev-ok-thm
  (implies (and (env-ns e1 e2 st) (not (eq (g-role nil st) :stobj))) (aev-ok flag x e1 e2 defs n st))
  :rule-classes nil
  :hints (("Goal" :induct (aev3-ind flag x n)
           :in-theory (union-theories '((:induction aev3-ind) aev-zp aev-atom aev-cons aevl-atom aevl-cons aev-ok-list)
                                      (theory 'minimal-theory)))
          (and stable-under-simplificationp '(:cases ((eq flag :one) (eq flag :list))))))

(defthm a-ev-env-ns
  (implies (and (env-ns e1 e2 st) (not (eq (g-role nil st) :stobj)) (g-st-free x st))
           (equal (a-ev x e1 defs n) (a-ev x e2 defs n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable aev-ok) :use (:instance aev-ok-thm (flag :one)))))

(defun asx2-ind (flag x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (if (eq flag :sx)
        (if (atom x) nil
          (list (asx2-ind :list (cdr x) (1- n)) (asx2-ind :sx (kadr x) (1- n)) (asx2-ind :sx (kaddr x) (1- n))
                (asx2-ind :sx (kadddr x) (1- n))))
      (if (atom x) nil (list (asx2-ind :sx (car x) (1- n)) (asx2-ind :list (cdr x) (1- n)))))))

(defun-nx asx-ok (flag x e1 e2 s st defs n)
  (if (eq flag :sx)
      (equal (a-sx x e1 s st defs n) (a-sx x e2 s st defs n))
    (equal (a-sx-list x e1 s st defs n) (a-sx-list x e2 s st defs n))))

(defmacro asx-thy ()
  '(e/d (asx-ok) (g-st-free g-st-free-list a-prim g-role a-ev a-sx a-sx-list read-elem lkp)))

(defthm asx-zp (implies (zp n) (asx-ok flag x e1 e2 s st defs n))
  :hints (("Goal" :in-theory (asx-thy) :expand ((a-sx x e1 s st defs n) (a-sx x e2 s st defs n)
                                                (a-sx-list x e1 s st defs n) (a-sx-list x e2 s st defs n)))))

(defthm asx-free
  (implies (and (env-ns e1 e2 st) (not (eq (g-role nil st) :stobj)) (not (zp n)) (g-st-free x st))
           (asx-ok :sx x e1 e2 s st defs n))
  :hints (("Goal" :in-theory (asx-thy) :expand ((a-sx x e1 s st defs n) (a-sx x e2 s st defs n))
           :use ((:instance a-ev-env-ns (defs defs) (n n))))))

(defthm asx-cons
  (implies (and (not (zp n)) (not (g-st-free x st))
                (implies (consp x)
                         (and (asx-ok :sx (kadr x) e1 e2 s st defs (1- n)) (asx-ok :sx (kaddr x) e1 e2 s st defs (1- n))
                              (asx-ok :sx (kadddr x) e1 e2 s st defs (1- n)) (asx-ok :list (cdr x) e1 e2 s st defs (1- n)))))
           (asx-ok :sx x e1 e2 s st defs n))
  :hints (("Goal" :in-theory (asx-thy) :expand ((:free (n) (a-sx x e1 s st defs n)) (:free (n) (a-sx x e2 s st defs n))))))

(defthm asxl-step
  (implies (and (not (zp n))
                (implies (consp x) (and (asx-ok :sx (car x) e1 e2 s st defs (1- n)) (asx-ok :list (cdr x) e1 e2 s st defs (1- n)))))
           (asx-ok :list x e1 e2 s st defs n))
  :hints (("Goal" :in-theory (asx-thy) :expand ((a-sx-list x e1 s st defs n) (a-sx-list x e2 s st defs n)))))


(in-theory (disable asx-ok))

(defthm a-sx-env-ns-flag
  (implies (and (env-ns e1 e2 st) (not (eq (g-role nil st) :stobj)))
           (if (eq flag :sx) (asx-ok :sx x e1 e2 s st defs n) (asx-ok :list x e1 e2 s st defs n)))
  :rule-classes nil
  :hints (("Goal" :induct (asx2-ind flag x n)
           :in-theory (union-theories '((:induction asx2-ind) asx-zp asx-free asx-cons asxl-step)
                                      (theory 'minimal-theory)))
          (and stable-under-simplificationp '(:cases ((g-st-free x st))))))

; sf-orc's env (nil at the stobj formal) and g-sret-fn-sem's (the value formals)
(defun sfv-ind (formals ks st)
  (cond ((atom formals) ks)
        ((eq (g-role (car formals) st) :stobj) (sfv-ind (cdr formals) ks st))
        (t (sfv-ind (cdr formals) (cdr ks) st))))

(defthm lkp-sf-vals
  (implies (not (eq (g-role y st) :stobj))
           (equal (lkp y (pairlis$ formals (sf-vals formals ks st))) (lkp y (pairlis$ (g-st-vals formals st) ks))))
  :hints (("Goal" :induct (sfv-ind formals ks st) :in-theory (disable g-role))))

(defthm env-ns-sf-vals
  (env-ns (pairlis$ formals (sf-vals formals ks st)) (pairlis$ (g-st-vals formals st) ks) st)
  :hints (("Goal" :in-theory (enable env-ns) :do-not-induct t)))

(defthm a-sx-sf-vals
  (implies (not (eq (g-role nil st) :stobj))
           (equal (a-sx x (pairlis$ formals (sf-vals formals ks st)) s st defs n)
                  (a-sx x (pairlis$ (g-st-vals formals st) ks) s st defs n)))
  :hints (("Goal" :in-theory (enable asx-ok) :use (:instance a-sx-env-ns-flag (flag :sx) (e1 (pairlis$ formals (sf-vals formals ks st)))
                                  (e2 (pairlis$ (g-st-vals formals st) ks))))))

; ---- a-sxf is a-sx on a body calling no function of defs

(defthm no-calls-term-parts
  (implies (and (no-calls :term x defs nil) (consp x) (not (eq (car x) 'quote)))
           (and (no-calls :list (cdr x) defs nil)
                (no-calls :term (kadr x) defs nil) (no-calls :term (kaddr x) defs nil) (no-calls :term (kadddr x) defs nil)
                (implies (consp (car x)) (no-calls :term (kaddr (car x)) defs nil))
                (implies (not (consp (car x))) (not (consp (lkp (car x) defs))))))
  :hints (("Goal" :in-theory (enable kar kdr kadr kaddr kadddr)
           :expand ((no-calls :term x defs nil) (no-calls :list (cdr x) defs nil) (no-calls :list (cddr x) defs nil)
                    (no-calls :list (cdddr x) defs nil) (no-calls :term nil defs nil)))))

(defun-nx sxd-ok (flag x env s st defs n)
  (if (eq flag :sx)
      (implies (no-calls :term x defs nil) (equal (a-sxf x env s st defs n) (a-sx x env s st defs n)))
    (implies (no-calls :list x defs nil) (equal (a-sxf-list x env s st defs n) (a-sx-list x env s st defs n)))))

(defthm a-sxf-list-zp-f (implies (zp n) (equal (a-sxf-list x env s st defs n) (mv :fuel nil)))
  :hints (("Goal" :expand ((a-sxf-list x env s st defs n)))))

(defmacro sxd-thy ()
  '(e/d (sxd-ok) (a-sx a-sx-list a-ev a-prim read-elem g-st-free no-calls a-sxf a-sxf-list lkp g-role)))

(defthm sxd-zp (implies (zp n) (sxd-ok flag x env s st defs n)) :hints (("Goal" :in-theory (sxd-thy))))

(defthm sxd-sx
  (implies (and (not (zp n))
                (implies (consp x)
                         (and (sxd-ok :list (cdr x) env s st defs (1- n))
                              (sxd-ok :sx (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x)))
                                                                    (mv-nth 1 (a-sx-list (cdr x) env s st defs (1- n))))
                                      s st defs (1- n))
                              (sxd-ok :sx (kadr x) env s st defs (1- n)) (sxd-ok :sx (kaddr x) env s st defs (1- n))
                              (sxd-ok :sx (kadddr x) env s st defs (1- n)))))
           (sxd-ok :sx x env s st defs n))
  :hints (("Goal" :in-theory (sxd-thy)
           :expand ((a-sx x env s st defs n) (a-sxf x env s st defs n)) :cases ((g-st-free x st)))))

(defthm sxd-list
  (implies (and (not (zp n))
                (implies (consp x) (and (sxd-ok :sx (car x) env s st defs (1- n)) (sxd-ok :list (cdr x) env s st defs (1- n)))))
           (sxd-ok :list x env s st defs n))
  :hints (("Goal" :in-theory (sxd-thy)
           :expand ((:free (n) (a-sx-list x env s st defs n)) (:free (n) (a-sxf-list x env s st defs n))))))

(in-theory (disable sxd-ok))

(defthm a-sxf-nodefs-flag
  (if (eq flag :sx) (sxd-ok :sx x env s st defs n) (sxd-ok :list x env s st defs n))
  :rule-classes nil
  :hints (("Goal" :induct (asxf-ind flag x env s st defs n)
           :in-theory (union-theories '((:induction asxf-ind) sxd-zp sxd-sx sxd-list) (theory 'minimal-theory)))))

(defthm a-sxf-nodefs
  (implies (no-calls :term x defs nil) (equal (a-sxf x env s st defs n) (a-sx x env s st defs n)))
  :hints (("Goal" :in-theory (e/d (sxd-ok) (a-sx a-sxf no-calls)) :use (:instance a-sxf-nodefs-flag (flag :sx)))))

; ---- the table and the oracle

(defun sfd-src (name defs)
  (cond ((atom defs) nil)
        ((and (consp (car defs)) (equal (g-sym (caar defs) nil) name)) (car defs))
        (t (sfd-src name (cdr defs)))))

(defun sfd-names (defs)
  (cond ((atom defs) nil)
        ((consp (car defs)) (cons (g-sym (caar defs) nil) (sfd-names (cdr defs))))
        (t (sfd-names (cdr defs)))))

(defchoose sfn-fuel (m) (x env s st defs) (and (natp m) (not (mv-nth 0 (a-sx x env s st defs m)))))

(defun s-fn-val-h (name s ks defs st o)
  (let* ((d (sfd-src name defs)) (x (kaddr d)) (vs (g-st-vals (kadr d) st)) (env (pairlis$ vs ks)))
    (if (and (consp d) (int64-listp ks) (equal (len ks) (len vs)) (st-ok st o s))
        (mv-let (e v) (a-sx x env s st defs (sfn-fuel x env s st defs)) (mv e v))
      (mv :orc nil))))

(defmacro sfe-let (&rest body)
  `(let* ((fn (kar d)) (formals (kadr d)) (x (kaddr d)) (vs (g-st-vals formals st)) (sig (cdr (lkp fn sigs)))
          (dums (g-st-dummies formals (list nil) st)))
     (declare (ignorable fn formals x vs sig dums))
     ,@body))

(defun sfe-ok (d gdefs sigs st defs procs o b)
  (sfe-let
   (mv-let (e p) (g-st-fn (list fn formals (list nil) t x) gdefs sigs st)
    (mv-let (e2 body c2 l2) (g-sret x (g-em vs) 0 nil fn sigs (append (g-formals vs) (st-objs st)) st)
     (declare (ignore e2 c2 l2))
     (and (consp d) (not e) (consp (lkp fn sigs)) (equal (kar sig) formals) (true-listp formals)
          (equal dums (list (list o :in (kaddr (car dums)))))
          (no-calls :term x sigs nil) (no-calls :term x defs nil)
          (not (g-role 'if st)) (not (g-role 'implies st)) (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (not (eq (g-role nil st) :stobj))
          (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
          (not (member-equal o (g-formals vs))) (not (equal o "r"))
          (equal (find-proc (g-sym fn nil) procs) p)
          (integerp b)
          (< (+ 7 (len vs) (acl2-count body)) b))))))

(defun sfd-ok1 (ds gdefs sigs st defs procs o b)
  (if (atom ds) t
    (and (or (not (consp (car ds))) (sfe-ok (car ds) gdefs sigs st defs procs o b))
         (sfd-ok1 (cdr ds) gdefs sigs st defs procs o b))))

(defun sfd-ok (defs gdefs sigs st procs o b)
  (and (sfd-ok1 defs gdefs sigs st defs procs o b) (no-duplicatesp-equal (sfd-names defs))))

(in-theory (disable sfe-ok s-fn-val-h))

; ---- lookups

(defthm true-list-fix-true (implies (true-listp x) (equal (true-list-fix x) x)))

(defthm car-lkp-key-f (implies (consp (lkp k al)) (equal (car (lkp k al)) k)))

(defthm cdr-lkp-one (equal (cdr (lkp k (list (cons k s)))) s))

(defthm sfd-src-ok
  (implies (and (sfd-ok1 ds gdefs sigs st defs procs o b) (consp (sfd-src name ds)))
           (and (sfe-ok (sfd-src name ds) gdefs sigs st defs procs o b)
                (equal (g-sym (car (sfd-src name ds)) nil) name))))

(defthm lkp-sfd-names
  (implies (consp (lkp f ds)) (member-equal (g-sym f nil) (sfd-names ds)))
  :hints (("Goal" :in-theory (disable g-sym))))

(defthm sfd-src-lkp
  (implies (and (no-duplicatesp-equal (sfd-names ds)) (consp (lkp f ds)))
           (equal (sfd-src (g-sym f nil) ds) (lkp f ds)))
  :hints (("Goal" :in-theory (disable g-sym))))

; what the oracle's answering gives
(defthm s-fn-val-h-parts
  (let* ((d (sfd-src name defs)) (x (kaddr d)) (vs (g-st-vals (kadr d) st)) (env (pairlis$ vs ks))
         (m (sfn-fuel x env s st defs)))
    (implies (not (mv-nth 0 (s-fn-val-h name s ks defs st o)))
             (and (consp d) (int64-listp ks) (equal (len ks) (len vs)) (st-ok st o s)
                  (not (mv-nth 0 (a-sx x env s st defs m)))
                  (equal (mv-nth 1 (s-fn-val-h name s ks defs st o)) (mv-nth 1 (a-sx x env s st defs m))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (s-fn-val-h) (a-sx st-ok sfd-src)))))

; the fuel chosen answers no error, and a-sx's value at any other fuel without one
(defthm sfn-fuel-agrees
  (implies (not (mv-nth 0 (a-sx x env s st defs n)))
           (and (not (mv-nth 0 (a-sx x env s st defs (sfn-fuel x env s st defs))))
                (equal (a-sx x env s st defs (sfn-fuel x env s st defs)) (a-sx x env s st defs n))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable a-sx)
           :cases ((natp n))
           :use ((:instance sfn-fuel (m n))
                 (:instance a-sx-mono (m (max n (sfn-fuel x env s st defs))))
                 (:instance a-sx-mono (n (sfn-fuel x env s st defs)) (m (max n (sfn-fuel x env s st defs))))))
          (and stable-under-simplificationp '(:expand ((a-sx x env s st defs n))))))

; ---- the entry's facts, as g-sret-fn-sem and rfn-run state them

(defthm sfe-ok-facts
  (implies (sfe-ok d gdefs sigs st defs procs o b)
           (sfe-let
            (and (consp d) (not (mv-nth 0 (g-st-fn (list fn formals (list nil) t x) gdefs sigs st)))
                 (consp (lkp fn sigs)) (equal (kar sig) formals) (true-listp formals)
                 (equal dums (list (list o :in (kaddr (car dums)))))
                 (no-calls :term x sigs nil) (no-calls :term x defs nil)
                 (not (g-role 'if st)) (not (g-role 'implies st)) (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (not (eq (g-role nil st) :stobj))
                 (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                 (not (member-equal o (g-formals vs))) (not (equal o "r"))
                 (equal (find-proc (g-sym fn nil) procs) (mv-nth 1 (g-st-fn (list fn formals (list nil) t x) gdefs sigs st)))
                 (integerp b)
                 (< (+ 7 (len vs) (acl2-count (mv-nth 1 (g-sret x (g-em vs) 0 nil fn sigs (append (g-formals vs) (st-objs st)) st))))
                    b))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sfe-ok) (theory 'minimal-theory)))))

; the body's value is of the function's type (rfn-run)
(defthm g-sret-fn-ty
  (let ((vs (g-st-vals formals st)))
    (implies (and (not (mv-nth 0 (rfn)))
                  (equal (g-st-dummies formals (list nil) st) (list (list o :in c)))
                  (no-calls :term x sigs nil)
                  (not (g-role 'if st)) (not (g-role 'implies st)) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                  (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                  (not (member-equal o (g-formals vs))) (not (equal o "r"))
                  (int64-listp ks) (equal (len ks) (len vs))
                  (st-ok st o s) (not (car (a-sx x (pairlis$ vs ks) s st defs n))))
             (scalar-ok (kadr (cdr (lkp fn sigs))) (mv-nth 1 (a-sx x (pairlis$ vs ks) s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(binary-append member-equal car-cons cdr-cons cdr-lkp-one) (theory 'minimal-theory))
           :use (g-st-fn-fshape
                 (:instance g-st-dummies-objs (d (list o :in c)) (outs (list nil)))
                 (:instance em-nostobj-g-em-vals (f formals))
                 (:instance rfn-run (vs (g-st-vals formals st)) (key 0) (heap (list (cons 0 s))))
                 (:instance sret-ok-r
                            (rt (kadr (cdr (lkp fn sigs))))
                            (v (mv-nth 1 (a-sx x (pairlis$ (g-st-vals formals st) ks) s st defs n)))
                            (fr (mv-nth 1 (sx-list (grf 1)
                                                   (undef-locals (cons (list "r" (kadr (cdr (lkp fn sigs)))) (g-locals (grf 3)))
                                                                 (fb (g-st-vals formals st) ks (put o (list* :obj :in 0) nil)))
                                                   (list (cons 0 s))))))))))

; ---- sf-orc, the oracle's own defs, st and o apart (the functional instance's lambdas need them)

(defun-sk sf-orc-h (sigs defs st o defs0 st0 o0)
  (forall (f s ks n)
    (let* ((d (lkp f defs)) (sig (cdr (lkp f sigs)))
           (r (a-sxf (kaddr d) (pairlis$ (true-list-fix (kadr d)) (sf-vals (kar sig) ks st)) s st defs n)))
      (implies (and (consp (lkp f sigs)) (consp d) (st-ok st o s) (int64-listp ks)
                    (equal (len ks) (len (g-st-vals (kar sig) st))) (not (mv-nth 0 r)))
               (and (equal (s-fn-val-h (g-sym f nil) s ks defs0 st0 o0) (mv nil (mv-nth 1 r)))
                    (scalar-ok (kadr sig) (mv-nth 1 r)))))))

(in-theory (disable sf-orc-h))

; one f: the entry's body, a-sxf on sf-orc's env, is the oracle's a-sx
(defthm kar-lkp-key (implies (consp (lkp k al)) (equal (kar (lkp k al)) k)) :hints (("Goal" :in-theory (enable kar))))

(defthm s-fn-val-h-answers
  (let* ((d (sfd-src name defs)) (x (kaddr d)) (vs (g-st-vals (kadr d) st)) (env (pairlis$ vs ks)))
    (implies (and (consp d) (int64-listp ks) (equal (len ks) (len vs)) (st-ok st o s) (not (mv-nth 0 (a-sx x env s st defs n))))
             (equal (s-fn-val-h name s ks defs st o) (list nil (mv-nth 1 (a-sx x env s st defs n))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (s-fn-val-h) (a-sx st-ok sfd-src int64-listp))
           :use ((:instance sfn-fuel-agrees (x (kaddr (sfd-src name defs))) (env (pairlis$ (g-st-vals (kadr (sfd-src name defs)) st) ks)))))))

(defthm sf-orc-ent
  (let* ((d (lkp f defs)) (sig (cdr (lkp f sigs)))
         (r (a-sxf (kaddr d) (pairlis$ (true-list-fix (kadr d)) (sf-vals (kar sig) ks st)) s st defs n)))
    (implies (and (sfd-ok defs gdefs sigs st procs o b)
                  (consp (lkp f sigs)) (consp d) (st-ok st o s) (int64-listp ks)
                  (equal (len ks) (len (g-st-vals (kar sig) st))) (not (mv-nth 0 r)))
             (and (equal (s-fn-val-h (g-sym f nil) s ks defs st o) (mv nil (mv-nth 1 r)))
                  (scalar-ok (kadr sig) (mv-nth 1 r)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(sfd-ok kar-lkp-key mv-nth-0-car) (theory 'minimal-theory))
           :use ((:instance sfd-src-ok (ds defs) (name (g-sym f nil)))
                 (:instance sfd-src-lkp (ds defs))
                 (:instance sfe-ok-facts (d (lkp f defs)))
                 (:instance true-list-fix-true (x (kadr (lkp f defs))))
                 (:instance a-sxf-nodefs (x (kaddr (lkp f defs)))
                            (env (pairlis$ (kadr (lkp f defs)) (sf-vals (kadr (lkp f defs)) ks st))))
                 (:instance a-sx-sf-vals (x (kaddr (lkp f defs))) (formals (kadr (lkp f defs))))
                 (:instance s-fn-val-h-answers (name (g-sym f nil)))
                 (:instance g-sret-fn-ty (fn f) (formals (kadr (lkp f defs))) (x (kaddr (lkp f defs)))
                            (c (kaddr (car (g-st-dummies (kadr (lkp f defs)) (list nil) st)))))))))

(defthm sf-orc-h-holds
  (implies (sfd-ok defs gdefs sigs st procs o b) (sf-orc-h sigs defs st o defs st o))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (sf-orc-h) (sfd-ok a-sxf s-fn-val-h st-ok int64-listp scalar-ok))
           :use ((:instance sf-orc-ent (f (mv-nth 0 (sf-orc-h-witness sigs defs st o defs st o)))
                            (s (mv-nth 1 (sf-orc-h-witness sigs defs st o defs st o)))
                            (ks (mv-nth 2 (sf-orc-h-witness sigs defs st o defs st o)))
                            (n (mv-nth 3 (sf-orc-h-witness sigs defs st o defs st o))))))))

; ---- p-sflits

(defun-sk p-sflits-h (procs b defs0 st0 o0)
  (forall (name s ks ob caller heap fuel)
    (let ((p (find-proc name procs)))
      (implies (and (not (mv-nth 0 (s-fn-val-h name s ks defs0 st0 o0))) (not (mv-nth 0 (obj-of ob caller)))
                    (equal (cdr (lkp (mv-nth 1 (obj-of ob caller)) heap)) s)
                    (integerp fuel) (< b fuel))
               (and (eq (kar p) :function) (int64-listp ks) (< (+ 4 (len ks)) b)
                    (sfl-dums (nth 4 (true-list-fix p)) ks)
                    (equal (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                           (mv nil (mv-nth 1 (s-fn-val-h name s ks defs0 st0 o0)) heap)))))))

(in-theory (disable p-sflits-h))

(defthm val-dums-g-dummies (val-dums (g-dummies vs)))

(defthm len-g-dummies (equal (len (g-dummies vs)) (len vs)))

(defthm obj-of-binding
  (implies (not (mv-nth 0 (obj-of ob caller)))
           (equal (cdr (lkp ob caller)) (list* :obj (mv-nth 2 (obj-of ob caller)) (mv-nth 1 (obj-of ob caller)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable obj-of))))

(defthm kar-consp (implies (consp d) (equal (kar d) (car d))) :hints (("Goal" :in-theory (enable kar))))

; the generated FUNCTION's head and dummies
(defthm rfn-fn-parts
  (implies (and (not (mv-nth 0 (rfn))) (equal (g-st-dummies formals (list nil) st) (list (list o :in c)))
                (equal (len ks) (len (g-st-vals formals st))))
           (and (equal (kar (mv-nth 1 (rfn))) :function)
                (sfl-dums (nth 4 (true-list-fix (mv-nth 1 (rfn)))) ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (sfl-dums kar kadr) (g-st-fn g-sret g-st-dummies g-st-vals g-role g-dummies g-locals g-reaches
                                                g-called g-fcalls g-sym g-st-fn-fshape g-formals g-em st-objs))
           :use g-st-fn-fshape)))

; one entry: the generated FUNCTION on literals (g-sret-fn-sem)
(defthm p-sflits-ent
  (let* ((p (find-proc name procs))
         (key (mv-nth 1 (obj-of ob caller))))
    (implies (and (sfd-ok1 defs gdefs sigs st defs procs o b)
                  (not (mv-nth 0 (s-fn-val-h name s ks defs st o))) (not (mv-nth 0 (obj-of ob caller)))
                  (equal (cdr (lkp key heap)) s) (integerp fuel) (< b fuel))
             (and (eq (kar p) :function) (int64-listp ks) (< (+ 4 (len ks)) b)
                  (sfl-dums (nth 4 (true-list-fix p)) ks)
                  (equal (f-invoke p (cons (list :var ob) (g-lits ks)) caller heap procs fuel)
                         (mv nil (mv-nth 1 (s-fn-val-h name s ks defs st o)) heap)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(kar-consp mv-nth-0-car (:type-prescription acl2-count)) (theory 'minimal-theory))
           :use ((:instance sfd-src-ok (ds defs))
                 (:instance sfe-ok-facts (d (sfd-src name defs)))
                 s-fn-val-h-parts obj-of-binding
                 (:instance rfn-fn-parts (fn (kar (sfd-src name defs))) (formals (kadr (sfd-src name defs)))
                            (x (kaddr (sfd-src name defs)))
                            (c (kaddr (car (g-st-dummies (kadr (sfd-src name defs)) (list nil) st)))))
                 (:instance g-sret-fn-sem (fn (kar (sfd-src name defs))) (formals (kadr (sfd-src name defs)))
                            (x (kaddr (sfd-src name defs)))
                            (c (kaddr (car (g-st-dummies (kadr (sfd-src name defs)) (list nil) st))))
                            (n (sfn-fuel (kaddr (sfd-src name defs)) (pairlis$ (g-st-vals (kadr (sfd-src name defs)) st) ks)
                                         s st defs))
                            (key (mv-nth 1 (obj-of ob caller))) (intent (mv-nth 2 (obj-of ob caller))))))))

(defthm p-sflits-h-holds
  (implies (sfd-ok defs gdefs sigs st procs o b) (p-sflits-h procs b defs st o))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (p-sflits-h) (sfd-ok1 s-fn-val-h f-invoke find-proc obj-of g-lits int64-listp))
           :use ((:instance p-sflits-ent
                            (name (mv-nth 0 (p-sflits-h-witness procs b defs st o)))
                            (s (mv-nth 1 (p-sflits-h-witness procs b defs st o)))
                            (ks (mv-nth 2 (p-sflits-h-witness procs b defs st o)))
                            (ob (mv-nth 3 (p-sflits-h-witness procs b defs st o)))
                            (caller (mv-nth 4 (p-sflits-h-witness procs b defs st o)))
                            (heap (mv-nth 5 (p-sflits-h-witness procs b defs st o)))
                            (fuel (mv-nth 6 (p-sflits-h-witness procs b defs st o))))))))
