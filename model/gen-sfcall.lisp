; gen-sfcall: g-sexpr's call of a value function given the stobj, `f(hs,
; args)` (the code `(:fcall f ((:var o) . cs))`), against a-sxf's call case
; (f's body on the arguments' values, S unchanged), on svf under sf-orc --
; gs-call-f, the case gs-sem-thm-f adds; and its names, sn-call-f. With upd
; nil, g-scall-args is g-sargs on the value arguments (g-cvals, gen-stcallst's
; lemma, copied here: the events up to g-scall-args-is-g-sargs are
; gen-stcallst's, redundant where both books are included), their values
; a-sxf-list's at any larger fuel (a-sxf-mono).

(in-package "ACL2")

(include-book "gen-sfexp")
(include-book "gen-sfmono")
(include-book "gen-stnames")

; a call's value arguments, and the objects g-scall-args passes for its stobj formals
(defun g-cvals (formals xs st)
  (cond ((or (atom formals) (atom xs)) nil)
        ((eq (g-role (car formals) st) :stobj) (g-cvals (cdr formals) (cdr xs) st))
        (t (cons (car xs) (g-cvals (cdr formals) (cdr xs) st)))))

(defun g-scs (formals xs st)
  (cond ((or (atom formals) (atom xs)) nil)
        ((eq (g-role (car formals) st) :stobj) (cons (list :var (g-obj (car formals) st)) (g-scs (cdr formals) (cdr xs) st)))
        (t (g-scs (cdr formals) (cdr xs) st))))

(defun all-int64-ty (ts) (if (atom ts) t (and (eq (car ts) :int64) (all-int64-ty (cdr ts)))))

; ---- g-scall-args (upd t) is g-sargs on the value arguments

(defun gsc-ind (formals xs em cnt locs sigs fnames st)
  (cond ((or (atom formals) (atom xs)) (list em cnt locs))
        ((eq (g-role (car formals) st) :stobj) (gsc-ind (cdr formals) (cdr xs) em cnt locs sigs fnames st))
        (t (mv-let (e s c ty cnt locs) (g-sexpr (car xs) em cnt locs sigs fnames st)
             (declare (ignore e s c ty))
             (gsc-ind (cdr formals) (cdr xs) em cnt locs sigs fnames st)))))

(defthm append-true-list-fix-left (equal (append (true-list-fix a) b) (append a b)))

(defmacro gsc (k) `(mv-nth ,k (g-scall-args formals xs t em cnt locs sigs fnames st)))
(defmacro gsa (k) `(mv-nth ,k (g-sargs (g-cvals formals xs st) em cnt locs sigs fnames st)))

(defthm g-scall-args-is-g-sargs
  (implies (not (gsc 0))
           (and (not (gsa 0)) (equal (g-flat (gsc 1)) (gsa 1)) (equal (gsc 2) (g-scs formals xs st))
                (equal (gsc 3) (gsa 2)) (equal (gsc 4) (gsa 4)) (equal (gsc 5) (gsa 5)) (all-int64-ty (gsa 3))))
  :hints (("Goal" :induct (gsc-ind formals xs em cnt locs sigs fnames st)
           :in-theory (disable g-sexpr)
           :expand ((g-scall-args formals xs t em cnt locs sigs fnames st)
                    (g-sargs (g-cvals formals xs st) em cnt locs sigs fnames st)
                    (g-sargs nil em cnt locs sigs fnames st)
                    (g-cvals formals xs st)))))

(defthm sfc-ok-imp
  (implies (and (gs-impp x st) (sfc-ok :term x sigs st))
           (and (sfc-ok :term (cadr x) sigs st) (sfc-ok :term (caddr x) sigs st)))
  :hints (("Goal" :in-theory (disable g-st-free) :expand ((sfc-ok :term x sigs st) (sfc-ok :list (cdr x) sigs st)
                           (sfc-ok :list (cddr x) sigs st) (sfc-ok :list (cdddr x) sigs st)))))

(defthm sfc-ok-the-check
  (implies (and (consp x) (eq (car x) 'the-check) (= (len x) 4) (sfc-ok :term x sigs st))
           (sfc-ok :term (cadddr x) sigs st))
  :hints (("Goal" :expand ((sfc-ok :term x sigs st) (sfc-ok :list (cdr x) sigs st)
                           (sfc-ok :list (cddr x) sigs st) (sfc-ok :list (cdddr x) sigs st)))))

(defthm count-g-cvals
  (<= (acl2-count (g-cvals formals xs st)) (acl2-count xs))
  :rule-classes :linear)

; ---- with upd nil and no error, g-scall-args is its upd-t answer, every
; stobj argument its formal

(defun sf-stargs (formals xs st)
  (cond ((or (atom formals) (atom xs)) t)
        ((eq (g-role (car formals) st) :stobj) (and (eq (car xs) (car formals)) (sf-stargs (cdr formals) (cdr xs) st)))
        (t (sf-stargs (cdr formals) (cdr xs) st))))

(defthm g-scall-args-nil-t
  (implies (not (mv-nth 0 (g-scall-args formals xs nil em cnt locs sigs fnames st)))
           (and (equal (g-scall-args formals xs nil em cnt locs sigs fnames st)
                       (g-scall-args formals xs t em cnt locs sigs fnames st))
                (sf-stargs formals xs st)))
  :hints (("Goal" :induct (gsc-ind formals xs em cnt locs sigs fnames st)
           :in-theory (disable g-sexpr)
           :expand ((g-scall-args formals xs nil em cnt locs sigs fnames st)
                    (g-scall-args formals xs t em cnt locs sigs fnames st)))))

; ---- the source side: the arguments' values are the value arguments' ones,
; nil at the stobj's place, at any larger fuel

(defun acv-ind (formals xs st n m)
  (declare (xargs :measure (len formals)))
  (cond ((or (atom formals) (atom xs)) (list n m))
        ((eq (g-role (car formals) st) :stobj) (acv-ind (cdr formals) (cdr xs) st (1- n) m))
        (t (acv-ind (cdr formals) (cdr xs) st (1- n) (1- m)))))

(defthm a-sxf-stobj-var
  (implies (and (symbolp x) (eq (g-role x st) :stobj) (not (zp n)))
           (equal (a-sxf x env s st defs n) (mv nil nil)))
  :hints (("Goal" :expand ((a-sxf x env s st defs n) (g-st-free x st)))))

(defthm g-role-stobj-symbolp
  (implies (equal (g-role x st) :stobj) (symbolp x))
  :rule-classes :forward-chaining)

(defthm a-sxf-stobj-val
  (implies (and (equal (g-role x st) :stobj) (not (mv-nth 0 (a-sxf x env s st defs n))))
           (equal (mv-nth 1 (a-sxf x env s st defs n)) nil))
  :hints (("Goal" :in-theory (disable g-role) :cases ((zp n)) :expand ((a-sxf x env s st defs n)))))

(defthm acall-vals
  (implies (and (not (mv-nth 0 (a-sxf-list xs env s st defs n))) (sf-stargs formals xs st) (equal (len formals) (len xs))
                (integerp m) (<= n m))
           (and (not (mv-nth 0 (a-sxf-list (g-cvals formals xs st) env s st defs m)))
                (equal (mv-nth 1 (a-sxf-list xs env s st defs n))
                       (sf-vals formals (mv-nth 1 (a-sxf-list (g-cvals formals xs st) env s st defs m)) st))))
  :hints (("Goal" :induct (acv-ind formals xs st n m) :in-theory (disable a-sxf g-role)
           :expand ((a-sxf-list xs env s st defs n) (a-sxf-list (g-cvals formals xs st) env s st defs m)
                    (g-cvals formals xs st) (a-sxf-list nil env s st defs m)
                    (:free (a b) (a-sxf-list (cons a b) env s st defs m))))
          (and stable-under-simplificationp
               '(:use ((:instance a-sxf-mono (x (car xs)) (n (1- n)) (m (1- m)))
                       (:instance a-sxf-list-mono (x (g-cvals (cdr formals) (cdr xs) st)) (n (1- m)) (m m)))))))

; ---- the code side

(defthm svs-ok-svlf
  (implies (and (svs-ok-f cs ts vs fr heap) (true-listp vs))
           (equal (svlf cs fr heap) (mv nil vs)))
  :hints (("Goal" :induct (svs-ok-f cs ts vs fr heap) :in-theory (disable svf) :expand ((svlf cs fr heap)))))

(defthm svs-ok-int64
  (implies (and (svs-ok-f cs ts vs fr heap) (all-int64-ty ts) (true-listp vs)) (int64-listp vs))
  :hints (("Goal" :induct (svs-ok-f cs ts vs fr heap) :in-theory (disable svf))))

(defun nl-ind (xs n) (if (atom xs) n (nl-ind (cdr xs) (1- n))))

(defthm a-sxf-list-true
  (true-listp (mv-nth 1 (a-sxf-list xs env s st defs n)))
  :hints (("Goal" :induct (nl-ind xs n) :in-theory (disable a-sxf) :expand ((a-sxf-list xs env s st defs n)))))

(defun sf-stobj (formals st)
  (cond ((atom formals) nil)
        ((eq (g-role (car formals) st) :stobj) (car formals))
        (t (sf-stobj (cdr formals) st))))

(defthm g-scs-one
  (implies (and (one-stobj formals st) (equal (len formals) (len xs)))
           (and (equal (g-scs formals xs st) (list (list :var (g-obj (sf-stobj formals st) st))))
                (eq (g-role (sf-stobj formals st) st) :stobj)))
  :hints (("Goal" :induct (acv-ind formals xs st n m) :in-theory (disable g-role g-obj))
          (and stable-under-simplificationp
               '(:expand ((g-scs formals xs st) (g-scs (cdr formals) (cdr xs) st))))))

(defthm no-stobj-scs
  (implies (no-stobj formals st) (equal (g-scs formals xs st) nil))
  :hints (("Goal" :in-theory (disable g-role g-obj))))

(defthm sfc-ok-cvals
  (implies (sfc-ok :list xs sigs st) (sfc-ok :list (g-cvals formals xs st) sigs st))
  :hints (("Goal" :induct (acv-ind formals xs st n m) :in-theory (disable sfc-ok-free no-calls-sfc-ok))))

(defthm sfc-ok-call-cvals
  (implies (and (sfc-ok :term x sigs st) (consp x) (not (consp (car x))) (not (eq (car x) 'quote)))
           (sfc-ok :list (g-cvals (kar (cdr (lkp (car x) sigs))) (cdr x) st) sigs st))
  :hints (("Goal" :expand ((sfc-ok :term x sigs st)))))

; the call branch of g-sexpr and a-sxf
(defmacro sf-call-hyps ()
  '(and (not-leaf) (not (member-eq (car x) '(if implies the-check))) (not (consp (car x))) (consp (lkp (car x) sigs))))

(defthm g-sexpr-call
  (implies (sf-call-hyps)
           (equal (g-sexpr x em cnt locs sigs fnames st)
                  (let ((sig (cdr (lkp (car x) sigs))))
                    (if (not (equal (len (kar sig)) (len (cdr x)))) (mv :type nil nil nil cnt locs)
                      (mv-let (e sss sc cs cnt locs) (g-scall-args (kar sig) (cdr x) nil em cnt locs sigs fnames st)
                        (if e (mv e nil nil nil cnt locs)
                          (mv nil (g-flat sss) (list :fcall (g-sym (car x) nil) (append sc cs)) (kadr sig) cnt locs)))))))
  :hints (("Goal" :in-theory (disable g-st-free g-mvnth g-role g-scall-args g-flat g-sym) :expand ((g-sexpr x em cnt locs sigs fnames st)))))

(defthm a-sxf-call
  (implies (and (consp x) (not (g-st-free x st)) (not (consp (car x))) (not (member-eq (g-role (car x) st) '(:field :size :elem :xfield :xsize :xelem)))
                (not (eq (car x) 'if)) (not (zp n)))
           (equal (a-sxf x env s st defs n)
                  (mv-let (e vs) (a-sxf-list (cdr x) env s st defs (1- n))
                    (cond (e (mv e nil))
                          ((consp (lkp (car x) defs))
                           (let ((d (lkp (car x) defs)))
                             (a-sxf (kaddr d) (pairlis$ (true-list-fix (kadr d)) vs) s st defs (1- n))))
                          (t (a-prim (car x) vs))))))
  :hints (("Goal" :in-theory (disable g-st-free g-role a-prim) :expand ((a-sxf x env s st defs n)))))

(defthm svf-fcall-open
  (equal (svf (list :fcall name (cons (list :var ob) cs)) fr heap)
         (mv-let (err key intent) (obj-of ob fr)
           (declare (ignore intent))
           (if err (mv err nil)
             (mv-let (err ks) (svlf cs fr heap)
               (if err (mv err nil)
                 (mv-let (err v) (s-fn-val name (cdr (lkp key heap)) ks) (mv err v)))))))
  :hints (("Goal" :expand ((svf (list :fcall name (cons (list :var ob) cs)) fr heap)))))

(defthm obj-is-obj-of
  (implies (obj-is o s fr heap)
           (and (not (mv-nth 0 (obj-of o fr))) (equal (cdr (lkp (mv-nth 1 (obj-of o fr)) heap)) s))))

(defthm sfc-ok-call
  (implies (and (sfc-ok :term x sigs st) (consp x) (not (consp (car x))) (not (eq (car x) 'quote)) (consp (lkp (car x) sigs)))
           (and (one-stobj (kar (cdr (lkp (car x) sigs))) st) (not (member-equal (car x) *g-prims*))
                (sfc-ok :list (cdr x) sigs st)))
  :rule-classes nil
  :hints (("Goal" :expand ((sfc-ok :term x sigs st)))))

(defmacro fsig () '(cdr (lkp (car x) sigs)))
(defmacro gcv () '(g-cvals (kar (fsig)) (cdr x) st))
(defmacro ga (k) `(mv-nth ,k (g-sargs (gcv) em cnt locs sigs fnames st)))
(defmacro fks () '(mv-nth 1 (a-sxf-list (gcv) env s st defs (1- n))))

(defmacro gx (k) `(mv-nth ,k (g-sexpr x em cnt locs sigs fnames st)))
(defmacro sfob () '(g-obj (sf-stobj (kar (fsig)) st) st))

; the code's shape: g-sargs on the value arguments, the call on the object and their codes
(defthm gs-call-shape
  (implies (and (sf-call-hyps) (one-stobj (kar (fsig)) st) (not (gx 0)))
           (and (not (ga 0)) (equal (gx 1) (ga 1)) (equal (gx 3) (kadr (fsig))) (equal (gx 5) (ga 5))
                (equal (gx 2) (list :fcall (g-sym (car x) nil) (cons (list :var (sfob)) (ga 2))))
                (all-int64-ty (ga 3)) (equal (len (kar (fsig))) (len (cdr x)))
                (sf-stargs (kar (fsig)) (cdr x) st)
                (eq (g-role (sf-stobj (kar (fsig)) st) st) :stobj)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-sexpr g-sargs g-scall-args g-st-free g-mvnth g-role g-obj g-sym g-flat
                               g-scall-args-is-g-sargs g-scall-args-nil-t g-scs-one)
           :use ((:instance g-scall-args-nil-t (formals (kar (fsig))) (xs (cdr x)))
                 (:instance g-scall-args-is-g-sargs (formals (kar (fsig))) (xs (cdr x)))
                 (:instance g-scs-one (formals (kar (fsig))) (xs (cdr x)))))))

; the code's run: the value arguments' statements, then the oracle on S and their values
(defthm gs-call-run
  (implies (and (gsa-sem-f (gcv) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (not (ga 0)) (not (car (a-sxf-list (gcv) env s st defs (1- n)))) (sfc-ok :list (gcv) sigs st)
                (em-ok em env fr) (decl-ok (ga 5) fr) (no-prim-defs defs) (sf-orc sigs defs st o)
                (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (obj-is o s fr heap) (all-int64-ty (ga 3)))
           (and (equal (car (sxf-list (ga 1) fr heap)) :normal)
                (equal (mv-nth 2 (sxf-list (ga 1) fr heap)) heap)
                (int64-listp (fks))
                (equal (svf (list :fcall name (cons (list :var o) (ga 2))) (mv-nth 1 (sxf-list (ga 1) fr heap)) heap)
                       (mv-let (e v) (s-fn-val name s (fks)) (mv e v)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-sargs a-sxf-list sxf-list svf svlf svs-ok-f sfc-ok em-ok decl-ok st-ok obj-is
                               gsa-sem-f gsa-sem-use-f g-role)
           :use ((:instance gsa-sem-use-f (xs (gcv)) (n (1- n)))
                 (:instance svs-ok-int64 (cs (ga 2)) (ts (ga 3)) (vs (fks)) (fr (mv-nth 1 (sxf-list (ga 1) fr heap))))
                 (:instance svs-ok-svlf (cs (ga 2)) (ts (ga 3)) (vs (fks)) (fr (mv-nth 1 (sxf-list (ga 1) fr heap))))
                 (:instance obj-is-after-sx-f (ss (ga 1)))
                 (:instance obj-is-obj-of (fr (mv-nth 1 (sxf-list (ga 1) fr heap))))))))

(defthm a-sxf-zp (implies (zp n) (equal (a-sxf x env s st defs n) (mv :fuel nil)))
  :hints (("Goal" :expand ((a-sxf x env s st defs n)))))

; the source's value arguments answer (no int64 needed: gs-call-run then gives it)
(defthm gs-call-src-args
  (implies (and (sf-call-hyps) (sfc-ok :term x sigs st) (not (car (a-sxf x env s st defs n)))
                (no-prim-defs defs) (equal (len (kar (fsig))) (len (cdr x))) (sf-stargs (kar (fsig)) (cdr x) st))
           (not (car (a-sxf-list (gcv) env s st defs (1- n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable a-sxf a-sxf-list g-st-free g-role sfc-ok acall-vals a-prim g-mvnth no-prim-defs)
           :cases ((zp n) (and (not (zp n)) (consp (lkp (car x) defs))) (and (not (zp n)) (not (consp (lkp (car x) defs)))))
           :use ((:instance sfc-ok-call)
                 (:instance acall-vals (formals (kar (fsig))) (xs (cdr x)) (n (1- n)) (m (1- n)))
                 (:instance a-prim-not-prim (f (car x)) (vs (mv-nth 1 (a-sxf-list (cdr x) env s st defs (1- n)))))))))

; the value arguments' values are as many as the value formals (sf-orc's ks)
(defthm len-a-sxf-list
  (implies (not (mv-nth 0 (a-sxf-list xs env s st defs n))) (equal (len (mv-nth 1 (a-sxf-list xs env s st defs n))) (len xs)))
  :hints (("Goal" :induct (nl-ind xs n) :in-theory (disable a-sxf) :expand ((a-sxf-list xs env s st defs n)))))

(defthm len-g-cvals
  (implies (equal (len formals) (len xs)) (equal (len (g-cvals formals xs st)) (len (g-st-vals formals st))))
  :hints (("Goal" :induct (acv-ind formals xs st n m) :in-theory (disable g-role))))

; the source: the arguments' values, then f's body, which the oracle answers (sf-orc)
(defthm gs-call-src
  (implies (and (sf-call-hyps) (sfc-ok :term x sigs st) (not (car (a-sxf x env s st defs n)))
                (no-prim-defs defs) (sf-orc sigs defs st o) (st-ok st o s) (int64-listp (fks))
                (equal (len (kar (fsig))) (len (cdr x))) (sf-stargs (kar (fsig)) (cdr x) st))
           (and (not (car (a-sxf-list (gcv) env s st defs (1- n))))
                (equal (s-fn-val (g-sym (car x) nil) s (fks)) (list nil (mv-nth 1 (a-sxf x env s st defs n))))
                (scalar-ok (kadr (fsig)) (mv-nth 1 (a-sxf x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable a-sxf a-sxf-list g-st-free g-role sfc-ok sf-orc-necc acall-vals st-ok a-prim
                               g-mvnth no-prim-defs)
           :cases ((zp n) (and (not (zp n)) (consp (lkp (car x) defs))) (and (not (zp n)) (not (consp (lkp (car x) defs)))))
           :use ((:instance sfc-ok-call)
                 (:instance acall-vals (formals (kar (fsig))) (xs (cdr x)) (n (1- n)) (m (1- n)))
                 (:instance sf-orc-necc (f (car x)) (ks (fks)) (n (1- n)))
                 (:instance len-a-sxf-list (xs (gcv)) (n (1- n)))
                 (:instance len-g-cvals (formals (kar (fsig))) (xs (cdr x)))
                 (:instance a-prim-not-prim (f (car x)) (vs (mv-nth 1 (a-sxf-list (cdr x) env s st defs (1- n)))))))))

(defthm gst-not-quote
  (implies (and (consp x) (not (g-st-free x st))) (not (equal (car x) 'quote)))
  :rule-classes nil
  :hints (("Goal" :expand ((g-st-free x st)))))

; the call: its value arguments by gsa-sem-f (the induction's), then the oracle
(defthm sfc-mv-nth-cons
  (and (equal (mv-nth 0 (cons a b)) a) (equal (mv-nth 1 (cons a b)) (car b))))

(defthm gs-call-core
  (implies (and (sf-call-hyps)
                (gsa-sem-f (gcv) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (sfc-ok :term x sigs st) (not (gx 0)) (not (car (a-sxf x env s st defs n)))
                (em-ok em env fr) (decl-ok (gx 5) fr) (no-prim-defs defs) (sf-orc sigs defs st o)
                (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (st-ok st o s) (obj-is o s fr heap))
           (and (equal (car (sxf-list (gx 1) fr heap)) :normal)
                (equal (mv-nth 2 (sxf-list (gx 1) fr heap)) heap)
                (not (car (svf (gx 2) (mv-nth 1 (sxf-list (gx 1) fr heap)) heap)))
                (equal (mv-nth 1 (svf (gx 2) (mv-nth 1 (sxf-list (gx 1) fr heap)) heap))
                       (mv-nth 1 (a-sxf x env s st defs n)))
                (scalar-ok (gx 3) (mv-nth 1 (a-sxf x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (set-difference-theories (union-theories '(sfc-mv-nth-cons car-cons cdr-cons (:executable-counterpart member-equal)
                                        (:executable-counterpart equal) (:executable-counterpart not)
                                        (:executable-counterpart zp) (:executable-counterpart binary-+)
                                        (:executable-counterpart unary--) (:executable-counterpart eq))
                                      (theory 'minimal-theory)) '(mv-nth))
           :use ((:instance gst-not-quote)
                 (:instance sfc-ok-call)
                 (:instance sfc-ok-call-cvals)
                 gs-call-shape
                 (:instance st-ok-necc (x (sf-stobj (kar (fsig)) st)))
                 (:instance gs-call-run (name (g-sym (car x) nil)))
                 gs-call-src-args gs-call-src))))

(defthm gs-call-f
  (implies (and (sf-call-hyps)
                (gsa-sem-f (gcv) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (gs-sem-f)
                           (g-sexpr g-sargs g-scall-args a-sxf a-sxf-list sxf-list svf svlf g-st-free g-mvnth g-role g-obj g-sym
                            sfc-ok no-calls sf-orc-necc st-ok-necc obj-is em-ok decl-ok st-ok scalar-ok a-prim gsa-sem-f
                            sf-orc no-prim-defs g-sexpr-call a-sxf-call svf-fcall-open))
           :use gs-call-core)))

; ---- names: the object and the value codes' names

(defthm svs-names-svfl
  (equal (svs-names-f cs) (svfl-names cs))
  :hints (("Goal" :induct (len cs) :expand ((svfl-names cs)))))

(defthm sn-call-f
  (implies (and (sf-call-hyps) (sobjs) (sfc-ok :term x sigs st)
                (sna-ok-f (gcv) em cnt locs sigs fnames st))
           (sn-ok-f x em cnt locs sigs fnames st))
  :hints (("Goal" :do-not-induct t
           :cases ((and (not (mv-nth 0 (g-scall-args (kar (fsig)) (cdr x) nil em cnt locs sigs fnames st)))
                        (equal (len (kar (fsig))) (len (cdr x)))))
           :in-theory (e/d (sn-ok-f sna-ok-f)
                           (g-sexpr g-sargs g-scall-args g-st-free g-mvnth g-role g-obj g-sym sfc-ok no-calls
                            g-scall-args-is-g-sargs g-scall-args-nil-t g-scs-one svs-names-f))
           :use ((:instance sfc-ok-call)
                 (:instance g-scall-args-nil-t (formals (kar (fsig))) (xs (cdr x)))
                 (:instance g-scall-args-is-g-sargs (formals (kar (fsig))) (xs (cdr x)))
                 (:instance g-scs-one (formals (kar (fsig))) (xs (cdr x)))
                 (:instance g-obj-fnames (x (sf-stobj (kar (fsig)) st)))))))
