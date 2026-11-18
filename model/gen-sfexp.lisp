; gen-sfexp: gen-stexp on svf/sxf-list/a-sxf (clone.py), gs-sem-f with sfc-ok
; (calls of value functions given the stobj allowed, their arguments call-free)
; in place of no-calls, and sf-orc (the oracle answers a-sxf of the callee).

(in-package "ACL2")

(include-book "gen-sfx")
(include-book "gen-stsxf")

; ---- which calls: a value function given the stobj, exactly one stobj
; formal (its object first in the code); no other call (as no-calls: layer
; 2's calls, which g-expr translates, excluded)

(defun no-stobj (formals st)
  (if (atom formals) t (and (not (eq (g-role (car formals) st) :stobj)) (no-stobj (cdr formals) st))))

(defun one-stobj (formals st)
  (cond ((atom formals) nil)
        ((eq (g-role (car formals) st) :stobj) (no-stobj (cdr formals) st))
        (t (one-stobj (cdr formals) st))))

(defun sfc-ok (flag x sigs st)
  (declare (xargs :measure (acl2-count x)))
  (cond ((eq flag :list) (if (atom x) t (and (sfc-ok :term (car x) sigs st) (sfc-ok :list (cdr x) sigs st))))
        ((or (atom x) (eq (car x) 'quote)) t)
        ((consp (car x)) (and (sfc-ok :term (kaddr (car x)) sigs st) (sfc-ok :list (cdr x) sigs st)))
        (t (and (or (not (consp (lkp (car x) sigs)))
                    (and (not (g-st-free x st)) (one-stobj (kar (cdr (lkp (car x) sigs))) st)
                         (not (member-equal (car x) *g-prims*))))
                (sfc-ok :list (cdr x) sigs st)))))

(defthm sfc-ok-free
  (implies (and (sfc-ok flag x sigs st) (if (eq flag :list) (g-st-free-list x st) (g-st-free x st)))
           (no-calls flag x sigs nil))
  :hints (("Goal" :induct (sfc-ok flag x sigs st) :expand ((g-st-free x st) (g-st-free-list x st)))))

(defthm no-calls-sfc-ok
  (implies (no-calls flag x sigs nil) (sfc-ok flag x sigs st)))

(defthm sfc-ok-elem
  (implies (and (consp x) (not (equal (car x) 'quote)) (not (consp (car x))) (sfc-ok :term x sigs st))
           (sfc-ok :term (cadr x) sigs st))
  :hints (("Goal" :expand ((sfc-ok :term x sigs st) (sfc-ok :list (cdr x) sigs st)))))

(defthm sfc-ok-if
  (implies (and (gs-ifp x st) (sfc-ok :term x sigs st))
           (and (sfc-ok :term (cadr x) sigs st) (sfc-ok :term (caddr x) sigs st)
                (sfc-ok :term (cadddr x) sigs st)))
  :hints (("Goal" :in-theory (disable g-st-free) :expand ((sfc-ok :term x sigs st) (sfc-ok :list (cdr x) sigs st)
                           (sfc-ok :list (cddr x) sigs st) (sfc-ok :list (cdddr x) sigs st)
                           (sfc-ok :list (cddddr x) sigs st)))))

(defthm sfc-ok-prim
  (implies (gs-primp x sigs st) (equal (sfc-ok :term x sigs st) (sfc-ok :list (cdr x) sigs st)))
  :hints (("Goal" :expand ((sfc-ok :term x sigs st)))))

(defthm sfc-ok-lambda-parts
  (implies (and (consp x) (consp (car x)) (sfc-ok :term x sigs st))
           (and (sfc-ok :term (caddr (car x)) sigs st) (sfc-ok :list (cdr x) sigs st)))
  :hints (("Goal" :expand ((sfc-ok :term x sigs st)))))

(defthm sfc-ok-list-parts
  (implies (sfc-ok :list xs sigs st)
           (and (sfc-ok :term (car xs) sigs st) (sfc-ok :list (cdr xs) sigs st)))
  :hints (("Goal" :expand ((sfc-ok :list xs sigs st) (sfc-ok :term nil sigs st)))))

(defthm sfc-ok-sym-args
  (implies (and (consp x) (not (eq (car x) 'quote)) (not (consp (car x))) (sfc-ok :term x sigs st))
           (sfc-ok :list (cdr x) sigs st))
  :hints (("Goal" :expand ((sfc-ok :term x sigs st)))))

(defthm sfc-ok-cons
  (implies (consp xs)
           (equal (sfc-ok :list xs sigs st) (and (sfc-ok :term (car xs) sigs st) (sfc-ok :list (cdr xs) sigs st)))))

; the call's environment: nil for the stobj formal, the values in order
(defun sf-vals (formals ks st)
  (cond ((atom formals) nil)
        ((eq (g-role (car formals) st) :stobj) (cons nil (sf-vals (cdr formals) ks st)))
        (t (cons (car ks) (sf-vals (cdr formals) (cdr ks) st)))))

; the oracle answers what the callee's body answers (a-sxf), of its type
(defun-sk sf-orc (sigs defs st o)
  (forall (f s ks n)
    (let* ((d (lkp f defs)) (sig (cdr (lkp f sigs)))
           (r (a-sxf (kaddr d) (pairlis$ (true-list-fix (kadr d)) (sf-vals (kar sig) ks st)) s st defs n)))
      (implies (and (consp (lkp f sigs)) (consp d) (st-ok st o s) (int64-listp ks) (not (mv-nth 0 r)))
               (and (equal (s-fn-val (g-sym f nil) s ks) (mv nil (mv-nth 1 r)))
                    (scalar-ok (kadr sig) (mv-nth 1 r)))))))

(in-theory (disable sf-orc))

(defun sxk-ind-f (flag s fr heap)
  (declare (xargs :measure (acl2-count s) :verify-guards nil))
  (if (atom s) (list fr heap)
    (if (eq flag :stmt)
        (mv-let (err v) (svf (kadr s) fr heap)
          (declare (ignore err))
          (list (sxk-ind-f :list (kaddr s) fr heap) (sxk-ind-f :list (kadddr s) fr heap)
                (sxk-ind-f :list (kadr (lkp v (kaddr s))) fr heap)))
      (mv-let (st fr2 h2) (sxf (car s) fr heap)
        (declare (ignore st))
        (list (sxk-ind-f :stmt (car s) fr heap) (sxk-ind-f :list (cdr s) fr2 h2))))))

(defun skp-stmt-f (n s fr heap)
  (mv-let (st fr2 h2) (sxf s fr heap)
    (declare (ignore st h2))
    (and (implies (not (member-equal n (asg :list (list s)))) (equal (lkp n fr2) (lkp n fr)))
         (equal (dty n fr2) (dty n fr)))))

(defun skp-list-f (n ss fr heap)
  (mv-let (st fr2 h2) (sxf-list ss fr heap)
    (declare (ignore st h2))
    (and (implies (not (member-equal n (asg :list ss))) (equal (lkp n fr2) (lkp n fr)))
         (equal (dty n fr2) (dty n fr)))))

(defthm skp-assign-f
  (implies (eq (kar s) :assign) (skp-stmt-f n s fr heap))
  :hints (("Goal" :expand ((sxf s fr heap) (asg :list (list s))))))

(defthm skp-if-f
  (implies (and (eq (kar s) :if) (skp-list-f n (kaddr s) fr heap) (skp-list-f n (kadddr s) fr heap))
           (skp-stmt-f n s fr heap))
  :hints (("Goal" :in-theory (disable dty sxf-list) :expand ((sxf s fr heap) (asg :list (list s))))))

(defthm skp-select-f
  (implies (and (eq (kar s) :select) (skp-list-f n (kadddr s) fr heap)
                (skp-list-f n (kadr (lkp (mv-nth 1 (svf (kadr s) fr heap)) (kaddr s))) fr heap))
           (skp-stmt-f n s fr heap))
  :hints (("Goal" :in-theory (disable dty sxf-list) :expand ((sxf s fr heap) (asg :list (list s)))
           :use ((:instance asg-lkp-arm (k (mv-nth 1 (svf (kadr s) fr heap))) (arms (kaddr s)))))))

(defthm skp-other-f
  (implies (not (member-equal (kar s) '(:assign :if :select))) (skp-stmt-f n s fr heap))
  :hints (("Goal" :in-theory (disable dty) :expand ((sxf s fr heap)))))

(defthm skp-nil-f
  (implies (atom ss) (skp-list-f n ss fr heap))
  :hints (("Goal" :expand ((sxf-list ss fr heap)))))

(defthm skp-cons-f
  (implies (and (consp ss) (skp-stmt-f n (car ss) fr heap)
                (skp-list-f n (cdr ss) (mv-nth 1 (sxf (car ss) fr heap)) (mv-nth 2 (sxf (car ss) fr heap))))
           (skp-list-f n ss fr heap))
  :hints (("Goal" :in-theory (disable dty sxf) :expand ((sxf-list ss fr heap) (asg :list ss)))))

(defthm skp-flag-f
  (if (eq flag :stmt) (skp-stmt-f n s fr heap) (skp-list-f n s fr heap))
  :rule-classes nil
  :hints (("Goal" :induct (sxk-ind-f flag s fr heap) :do-not-induct t
           :in-theory (disable skp-stmt-f skp-list-f sxf sxf-list kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select))))))

(defthm sx-list-keeps-f
  (and (implies (not (member-equal n (asg :list s)))
                (equal (lkp n (mv-nth 1 (sxf-list s fr heap))) (lkp n fr)))
       (equal (dty n (mv-nth 1 (sxf-list s fr heap))) (dty n fr)))
  :hints (("Goal" :use (:instance skp-flag-f (flag :list)))))

(defthm sx-list-agree-f
  (implies (not (intersectp-equal ns (asg :list s)))
           (lkp-agree ns fr (mv-nth 1 (sxf-list s fr heap))))
  :hints (("Goal" :induct (lkp-agree-ind ns))))

(defthm decl-ok-after-sx-f
  (equal (decl-ok locs (mv-nth 1 (sxf-list s fr heap))) (decl-ok locs fr))
  :hints (("Goal" :induct (len locs))))

(defthm em-ok-after-sx-f
  (implies (and (em-ok em env fr) (not (intersectp-equal (asg :list s) (em-names em))))
           (em-ok em env (mv-nth 1 (sxf-list s fr heap))))
  :hints (("Goal" :do-not-induct t :expand ((em-ok em env (mv-nth 1 (sxf-list s fr heap))))
           :in-theory (e/d (var-ok) (em-ok-necc sxf-list sx-list-keeps-f not-member-intersect))
           :use ((:instance em-ok-necc (x (em-ok-witness em env (mv-nth 1 (sxf-list s fr heap)))))
                 (:instance sx-list-keeps-f (n (cadr (lkp (em-ok-witness em env (mv-nth 1 (sxf-list s fr heap))) em))))
                 (:instance not-member-intersect (y (cadr (lkp (em-ok-witness em env (mv-nth 1 (sxf-list s fr heap))) em)))
                            (a (em-names em)) (b (asg :list s)))))))

(defun sko-stmt-f (o s fr heap)
  (mv-let (st fr2 h2) (sxf s fr heap)
    (declare (ignore st h2))
    (implies (equal (cadr (lkp o fr)) :obj) (equal (lkp o fr2) (lkp o fr)))))

(defun sko-list-f (o ss fr heap)
  (mv-let (st fr2 h2) (sxf-list ss fr heap)
    (declare (ignore st h2))
    (implies (equal (cadr (lkp o fr)) :obj) (equal (lkp o fr2) (lkp o fr)))))

(defthm sko-assign-f
  (implies (eq (kar s) :assign) (sko-stmt-f o s fr heap))
  :hints (("Goal" :expand ((sxf s fr heap)))))

(defthm sko-if-f
  (implies (and (eq (kar s) :if) (sko-list-f o (kaddr s) fr heap) (sko-list-f o (kadddr s) fr heap))
           (sko-stmt-f o s fr heap))
  :hints (("Goal" :in-theory (disable sxf-list) :expand ((sxf s fr heap)))))

(defthm sko-select-f
  (implies (and (eq (kar s) :select) (sko-list-f o (kadddr s) fr heap)
                (sko-list-f o (kadr (lkp (mv-nth 1 (svf (kadr s) fr heap)) (kaddr s))) fr heap))
           (sko-stmt-f o s fr heap))
  :hints (("Goal" :in-theory (disable sxf-list) :expand ((sxf s fr heap)))))

(defthm sko-other-f
  (implies (not (member-equal (kar s) '(:assign :if :select))) (sko-stmt-f o s fr heap))
  :hints (("Goal" :expand ((sxf s fr heap)))))

(defthm sko-nil-f
  (implies (atom ss) (sko-list-f o ss fr heap))
  :hints (("Goal" :expand ((sxf-list ss fr heap)))))

(defthm sko-cons-f
  (implies (and (consp ss) (sko-stmt-f o (car ss) fr heap)
                (sko-list-f o (cdr ss) (mv-nth 1 (sxf (car ss) fr heap)) (mv-nth 2 (sxf (car ss) fr heap))))
           (sko-list-f o ss fr heap))
  :hints (("Goal" :in-theory (disable sxf) :expand ((sxf-list ss fr heap)))))

(defthm sko-flag-f
  (if (eq flag :stmt) (sko-stmt-f o s fr heap) (sko-list-f o s fr heap))
  :rule-classes nil
  :hints (("Goal" :induct (sxk-ind-f flag s fr heap) :do-not-induct t
           :in-theory (disable sko-stmt-f sko-list-f sxf sxf-list kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select))))))

(defthm sx-list-keeps-obj-f
  (implies (equal (cadr (lkp o fr)) :obj) (equal (lkp o (mv-nth 1 (sxf-list ss fr heap))) (lkp o fr)))
  :hints (("Goal" :use (:instance sko-flag-f (flag :list) (s ss)))))

(defun sapp-ind-f (a fr heap)
  (if (atom a) (list fr heap)
    (mv-let (st fr2 h2) (sxf (car a) fr heap) (declare (ignore st)) (sapp-ind-f (cdr a) fr2 h2))))

(defthm sx-list-append-f
  (equal (sxf-list (append a b) fr heap)
         (mv-let (st fr2 h2) (sxf-list a fr heap)
           (if (eq st :normal) (sxf-list b fr2 h2) (mv st fr2 h2))))
  :hints (("Goal" :induct (sapp-ind-f a fr heap) :in-theory (disable sxf)
           :expand ((sxf-list a fr heap) (sxf-list (cons (car a) (append (cdr a) b)) fr heap) (sxf-list b fr heap)))))

(mutual-recursion
 (defun svf-names (e)
  (declare (xargs :guard t :measure (acl2-count e)))
  (case (kar e)
    ((:var :comp :size) (list (kadr e)))
    (:elem (cons (kadr e) (svf-names (kadddr e))))
    (:fcall (cons (kadr (kar (kaddr e))) (svfl-names (kdr (kaddr e)))))
    ((:neg :not) (svf-names (kadr e)))
    ((:add :sub :mul :eq :lt :le :ge :max) (append (svf-names (kadr e)) (svf-names (kaddr e))))
    (otherwise nil)))
 (defun svfl-names (cs)
  (declare (xargs :guard t :measure (acl2-count cs)))
  (if (atom cs) nil (append (svf-names (car cs)) (svfl-names (cdr cs))))))

(defun svf-ind (flag e)
  (declare (xargs :measure (acl2-count e)))
  (cond ((eq flag :list) (if (atom e) nil (list (svf-ind :one (car e)) (svf-ind :list (cdr e)))))
        ((atom e) nil)
        ((eq (kar e) :fcall) (svf-ind :list (kdr (kaddr e))))
        (t (list (svf-ind :one (kadr e)) (svf-ind :one (kaddr e)) (svf-ind :one (kadddr e))))))

(defthm comp-of-agree
  (implies (equal (lkp o fr) (lkp o fr2)) (equal (comp-of o c fr2 heap) (comp-of o c fr heap)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable comp-of obj-of))))

(defthm obj-of-agree
  (implies (equal (lkp o fr) (lkp o fr2)) (equal (obj-of o fr2) (obj-of o fr)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable obj-of))))

(defthm sv-agree-flag-f
  (if (eq flag :list)
      (implies (lkp-agree (svfl-names e) fr fr2) (equal (svlf e fr2 heap) (svlf e fr heap)))
    (implies (lkp-agree (svf-names e) fr fr2) (equal (svf e fr2 heap) (svf e fr heap))))
  :rule-classes nil
  :hints (("Goal" :induct (svf-ind flag e) :in-theory (disable binop arith read-elem svf-is-sv sv-is-fv-f cs-expr cf-expr comp-of)
           :expand ((svf e fr heap) (svf e fr2 heap) (svf-names e) (svlf e fr heap) (svlf e fr2 heap) (svfl-names e)
                    (lkp-agree (cons (cadr (car (caddr e))) (svfl-names (cdr (caddr e)))) fr fr2)))
          (and stable-under-simplificationp
               '(:use ((:instance comp-of-agree (o (kadr e)) (c (kaddr e)))
                       (:instance obj-of-agree (o (kadr (kar (kaddr e))))))))))

(defthm sv-agree-f
  (implies (lkp-agree (svf-names e) fr fr2) (equal (svf e fr2 heap) (svf e fr heap)))
  :hints (("Goal" :use (:instance sv-agree-flag-f (flag :one)))))

(defthm svl-agree-f
  (implies (lkp-agree (svfl-names cs) fr fr2) (equal (svlf cs fr2 heap) (svlf cs fr heap)))
  :hints (("Goal" :use (:instance sv-agree-flag-f (flag :list) (e cs)))))

(defthm cf-sv-names-f (implies (cf-expr e) (equal (svf-names e) (ev-names e))))

(defthm obj-is-after-sx-f
  (implies (obj-is o s fr heap) (obj-is o s (mv-nth 1 (sxf-list ss fr heap)) heap)))

(defun gs-sem-f (x em cnt locs sigs fnames st env s defs n fr heap o)
  (mv-let (e ss c ty cnt2 locs2) (g-sexpr x em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-sxf x env s st defs n)
      (implies (and (not e) (not ae) (sfc-ok :term x sigs st) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (sf-orc sigs defs st o) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (obj-is o s fr heap))
               (mv-let (stt fr2 h2) (sxf-list ss fr heap)
                 (mv-let (fe fvv) (svf c fr2 heap)
                   (and (equal stt :normal) (equal h2 heap) (not fe) (equal fvv v) (scalar-ok ty v))))))))

(defthm gs-mvnth-f
  (implies (g-mvnth x) (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable a-ev g-mvnth g-st-free g-sexpr a-ev-mv-nth g-mvnth-free)
           :expand ((a-sxf x env s st defs n))
           :use (g-mvnth-free a-ev-mv-nth))))

(defthm gs-free-f
  (implies (and (g-st-free x st) (not (g-mvnth x))) (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-expr a-ev g-st-free g-mvnth ge-sem fx-list fv)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (a-sxf x env s st defs n))
           :use ((:instance ge-sem-thm (flag :expr) (vars nil) (cs nil))
                 (:instance g-expr-cf)))
          (and stable-under-simplificationp '(:in-theory (e/d (ge-sem) (g-expr a-ev g-st-free g-mvnth fx-list fv))))))

(defthm gs-field-f
  (implies (and (consp x) (eq (g-role (car x) st) :field))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-obj g-comp g-role svf-is-sv)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (a-sxf x env s st defs n) (g-st-free x st)
                    (svf (list :comp (g-obj (car x) st) (g-comp (car x) st)) fr heap) (sxf-list nil fr heap))
           :use ((:instance st-ok-necc (x (car x)))))))

(defthm gs-size-f
  (implies (and (consp x) (eq (g-role (car x) st) :size))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-obj g-comp g-role svf-is-sv)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (a-sxf x env s st defs n) (g-st-free x st)
                    (svf (list :size (g-obj (car x) st) (g-comp (car x) st)) fr heap) (sxf-list nil fr heap))
           :use ((:instance st-ok-necc (x (car x)))))))

(defthm gs-elem-f
  (implies (and (consp x) (eq (g-role (car x) st) :elem)
                (gs-sem-f (cadr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-sexpr a-sxf sxf-list read-elem g-obj g-comp g-role svf-is-sv)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (a-sxf x env s st defs n) (g-st-free x st)
                    (:free (c fr) (svf (list :elem (g-obj (car x) st) (g-comp (car x) st) c) fr heap)))
           :use ((:instance st-ok-necc (x (car x)))))))

(defthm gs-elem-bounds-f
  (implies (and (consp x) (eq (g-role (car x) st) :elem)
                (gs-sem-f (cadr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (not (mv-nth 0 (g-sexpr x em cnt locs sigs fnames st)))
                (not (mv-nth 0 (a-sxf (cadr x) env s st defs (1- n))))
                (equal (mv-nth 0 (a-sxf x env s st defs n)) :bounds)
                (sfc-ok :term x sigs st) (em-ok em env fr)
                (decl-ok (mv-nth 5 (g-sexpr x em cnt locs sigs fnames st)) fr)
                (no-prim-defs defs) (sf-orc sigs defs st o) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (not (equal (car x) 'quote)) (st-ok st o s) (obj-is o s fr heap))
           (mv-let (stt fr2 h2) (sxf-list (mv-nth 1 (g-sexpr x em cnt locs sigs fnames st)) fr heap)
             (and (equal stt :normal) (equal h2 heap)
                  (equal (mv-nth 0 (svf (mv-nth 2 (g-sexpr x em cnt locs sigs fnames st)) fr2 heap)) :bounds))))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-sexpr a-sxf sxf-list read-elem g-obj g-comp g-role)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (:free (s) (a-sxf x env s st defs n)) (g-st-free x st)
                    (:free (c fr) (svf (list :elem (g-obj (car x) st) (g-comp (car x) st) c) fr heap)))
           :use ((:instance st-ok-necc (x (car x)))))
          (and stable-under-simplificationp '(:in-theory (e/d (read-elem) (g-sexpr a-sxf sxf-list g-obj g-comp g-role))))))

(defun svs-ok-f (cs ts vs fr heap)
  (if (atom cs) (atom vs)
    (mv-let (err v) (svf (car cs) fr heap)
      (and (consp vs) (not err) (equal v (car vs)) (scalar-ok (car ts) (car vs))
           (svs-ok-f (cdr cs) (cdr ts) (cdr vs) fr heap)))))

(defun gsa-sem-f (xs em cnt locs sigs fnames st env s defs n fr heap o)
  (mv-let (e ss cs ts cnt2 locs2) (g-sargs xs em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae vs) (a-sxf-list xs env s st defs n)
      (implies (and (not e) (not ae) (sfc-ok :list xs sigs st) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (sf-orc sigs defs st o) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (obj-is o s fr heap))
               (mv-let (stt fr2 h2) (sxf-list ss fr heap)
                 (and (equal stt :normal) (equal h2 heap) (svs-ok-f cs ts vs fr2 heap)))))))

(defthm g-unop-sem-sv-f
  (implies (and (not (car (g-unop op c ty))) (not (car (a-prim op vs)))
                (not (car (svf c fr heap))) (equal (mv-nth 1 (svf c fr heap)) (car vs)) (scalar-ok ty (car vs)))
           (and (not (car (svf (mv-nth 1 (g-unop op c ty)) fr heap)))
                (equal (mv-nth 1 (svf (mv-nth 1 (g-unop op c ty)) fr heap)) (mv-nth 1 (a-prim op vs)))
                (scalar-ok (mv-nth 2 (g-unop op c ty)) (mv-nth 1 (a-prim op vs)))))
  :hints (("Goal" :expand ((svf (list :neg c) fr heap) (svf (list :not c) fr heap) (svf (list :max '(:int 0) c) fr heap)
                           (svf '(:int 0) fr heap)
                           (svf (list :le c '(:int 0)) fr heap) (svf (list :ge c '(:int 0)) fr heap)))))

(defthm g-binop-sem-sv-f
  (implies (and (not (car (g-binop op a ta b tb))) (not (car (a-prim op vs)))
                (not (car (svf a fr heap))) (equal (mv-nth 1 (svf a fr heap)) (car vs)) (scalar-ok ta (car vs))
                (not (car (svf b fr heap))) (equal (mv-nth 1 (svf b fr heap)) (cadr vs)) (scalar-ok tb (cadr vs)))
           (and (not (car (svf (mv-nth 1 (g-binop op a ta b tb)) fr heap)))
                (equal (mv-nth 1 (svf (mv-nth 1 (g-binop op a ta b tb)) fr heap)) (mv-nth 1 (a-prim op vs)))
                (scalar-ok (mv-nth 2 (g-binop op a ta b tb)) (mv-nth 1 (a-prim op vs)))))
  :hints (("Goal" :expand ((svf (list :add a b) fr heap) (svf (list :mul a b) fr heap) (svf (list :eq a b) fr heap)
                           (svf (list :lt a b) fr heap)))))

(defthm svs-ok-cons-f
  (implies (consp cs)
           (equal (svs-ok-f cs ts vs fr heap)
                  (and (consp vs) (not (car (svf (car cs) fr heap))) (equal (mv-nth 1 (svf (car cs) fr heap)) (car vs))
                       (scalar-ok (car ts) (car vs)) (svs-ok-f (cdr cs) (cdr ts) (cdr vs) fr heap)))))

; a primitive call only (g-unop-prim/g-binop-prim give it where g-sexpr answers)
(defthm a-sx-prim-f
  (implies (and (gs-primp x sigs st) (no-prim-defs defs) (member-equal (car x) *g-prims*))
           (equal (a-sxf x env s st defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e vs) (a-sxf-list (cdr x) env s st defs (1- n))
                      (if e (mv e nil) (a-prim (car x) vs))))))
  :hints (("Goal" :in-theory (disable a-sxf-list g-st-free g-mvnth g-role a-prim) :expand ((a-sxf x env s st defs n)))))

(defthm svs-ok-len-f (implies (svs-ok-f cs ts vs fr heap) (equal (len vs) (len cs))) :rule-classes nil)

(defthm gs-prim-f
  (implies (and (gs-primp x sigs st) (gsa-sem-f (cdr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable gs-primp g-sexpr g-sargs a-sxf a-sxf-list no-calls sfc-ok g-unop g-binop a-prim svf scalar-ok)
           :use ((:instance svs-ok-len-f (cs (mv-nth 2 (g-sargs (cdr x) em cnt locs sigs fnames st)))
                            (ts (mv-nth 3 (g-sargs (cdr x) em cnt locs sigs fnames st)))
                            (vs (mv-nth 1 (a-sxf-list (cdr x) env s st defs (1- n))))
                            (fr (mv-nth 1 (sxf-list (mv-nth 1 (g-sargs (cdr x) em cnt locs sigs fnames st)) fr heap))))))))

(defun svs-names-f (cs) (if (atom cs) nil (append (svf-names (car cs)) (svs-names-f (cdr cs)))))

(defun sn-ok-f (x em cnt locs sigs fnames st)
  (mv-let (e ss c ty cnt2 locs2) (g-sexpr x em cnt locs sigs fnames st)
    (declare (ignore ty cnt2))
    (implies (not e)
             (and (subsetp-equal locs locs2)
                  (subsetp-equal (asg :list ss) (strip-cars locs2))
                  (not (intersectp-equal (asg :list ss) (append fnames (em-names em) (strip-cars locs))))
                  (subsetp-equal (svf-names c) (append fnames (em-names em) (strip-cars locs2)))))))

(defun sna-ok-f (xs em cnt locs sigs fnames st)
  (mv-let (e ss cs ts cnt2 locs2) (g-sargs xs em cnt locs sigs fnames st)
    (declare (ignore ts cnt2))
    (implies (not e)
             (and (subsetp-equal locs locs2)
                  (subsetp-equal (asg :list ss) (strip-cars locs2))
                  (not (intersectp-equal (asg :list ss) (append fnames (em-names em) (strip-cars locs))))
                  (subsetp-equal (svs-names-f cs) (append fnames (em-names em) (strip-cars locs2)))))))

(defthm gs-sem-use-f
  (implies (and (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o)
                (not (gsx 0)) (not (car (a-sxf x env s st defs n))) (sfc-ok :term x sigs st) (em-ok em env fr)
                (decl-ok (gsx 5) fr) (no-prim-defs defs) (sf-orc sigs defs st o) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap))
           (and (equal (car (sxf-list (gsx 1) fr heap)) :normal)
                (equal (mv-nth 2 (sxf-list (gsx 1) fr heap)) heap)
                (not (car (svf (gsx 2) (mv-nth 1 (sxf-list (gsx 1) fr heap)) heap)))
                (equal (mv-nth 1 (svf (gsx 2) (mv-nth 1 (sxf-list (gsx 1) fr heap)) heap)) (mv-nth 1 (a-sxf x env s st defs n)))
                (scalar-ok (gsx 3) (mv-nth 1 (a-sxf x env s st defs n)))
                (implies (equal (gsx 3) :logical) (booleanp (mv-nth 1 (a-sxf x env s st defs n))))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (gs-sem-f) (g-sexpr a-sxf sxf-list svf no-calls sfc-ok em-ok decl-ok scalar-ok st-ok obj-is)))))

(defthm gsa-sem-use-f
  (implies (and (gsa-sem-f xs em cnt locs sigs fnames st env s defs n fr heap o)
                (not (gsl 0)) (not (car (a-sxf-list xs env s st defs n))) (sfc-ok :list xs sigs st) (em-ok em env fr)
                (decl-ok (gsl 5) fr) (no-prim-defs defs) (sf-orc sigs defs st o) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap))
           (and (equal (car (sxf-list (gsl 1) fr heap)) :normal)
                (equal (mv-nth 2 (sxf-list (gsl 1) fr heap)) heap)
                (svs-ok-f (gsl 2) (gsl 3) (mv-nth 1 (a-sxf-list xs env s st defs n)) (mv-nth 1 (sxf-list (gsl 1) fr heap)) heap)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (gsa-sem-f) (g-sargs a-sxf-list sxf-list svs-ok-f no-calls sfc-ok em-ok decl-ok st-ok obj-is)))))

(defthm sn-ok-use-f
  (implies (and (sn-ok-f x em cnt locs sigs fnames st) (not (gsx 0)))
           (and (subsetp-equal locs (gsx 5))
                (subsetp-equal (asg :list (gsx 1)) (strip-cars (gsx 5)))
                (not (intersectp-equal (asg :list (gsx 1)) fnames))
                (not (intersectp-equal (asg :list (gsx 1)) (em-names em)))
                (not (intersectp-equal (asg :list (gsx 1)) (strip-cars locs)))
                (subsetp-equal (svf-names (gsx 2)) (append fnames (em-names em) (strip-cars (gsx 5))))))
  :hints (("Goal" :in-theory (disable g-sexpr g-sargs))))

(defthm sna-ok-use-f
  (implies (and (sna-ok-f xs em cnt locs sigs fnames st) (not (gsl 0)))
           (and (subsetp-equal locs (gsl 5))
                (subsetp-equal (asg :list (gsl 1)) (strip-cars (gsl 5)))
                (not (intersectp-equal (asg :list (gsl 1)) fnames))
                (not (intersectp-equal (asg :list (gsl 1)) (em-names em)))
                (not (intersectp-equal (asg :list (gsl 1)) (strip-cars locs)))
                (subsetp-equal (svs-names-f (gsl 2)) (append fnames (em-names em) (strip-cars (gsl 5))))))
  :hints (("Goal" :in-theory (disable g-sexpr g-sargs))))

(in-theory (disable gs-sem-f gsa-sem-f sn-ok-f sna-ok-f))

(defthm gsa-nil-f
  (implies (atom xs) (gsa-sem-f xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (enable gsa-sem-f) :expand ((g-sargs xs em cnt locs sigs fnames st) (sxf-list nil fr heap) (a-sxf-list xs env s st defs n)))))

(defthm gsa-cons-f
  (implies (and (consp xs)
                (gs-sem-f (car xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gsa-sem-f (cdr xs) em (sa1 4) (sa1 5) sigs fnames st env s defs (1- n)
                         (mv-nth 1 (sxf-list (sa1 1) fr heap)) heap o)
                (sn-ok-f (car xs) em cnt locs sigs fnames st)
                (sna-ok-f (cdr xs) em (sa1 4) (sa1 5) sigs fnames st))
           (gsa-sem-f xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t
           :expand ((gsa-sem-f xs em cnt locs sigs fnames st env s defs n fr heap o)
                    (g-sargs xs em cnt locs sigs fnames st) (a-sxf-list xs env s st defs n))
           :in-theory (disable g-sexpr g-sargs a-sxf a-sxf-list no-calls sfc-ok svf sv-agree-f sx-list-agree-f sxf-list
                               decl-ok-subset disjoint-via-subset obj-is st-ok scalar-ok em-ok decl-ok g-role g-mvnth)
           :use ((:instance sv-agree-f (e (sa1 2)) (fr (mv-nth 1 (sxf-list (sa1 1) fr heap)))
                            (fr2 (mv-nth 1 (sxf-list (sa2 1) (mv-nth 1 (sxf-list (sa1 1) fr heap)) heap))))
                 (:instance sx-list-agree-f (ns (svf-names (sa1 2))) (s (sa2 1)) (fr (mv-nth 1 (sxf-list (sa1 1) fr heap))))
                 (:instance decl-ok-subset (a (sa1 5)) (b (sa2 5)))
                 (:instance disjoint-via-subset (a (svf-names (sa1 2))) (b fnames)
                            (c (append (em-names em) (strip-cars (sa1 5)))) (d (asg :list (sa2 1))))))))

(defthm sv-var-put-f
  (implies (scalar-ok ty v) (equal (svf (list :var k) (put k (cons ty v) fr) heap) (mv nil v)))
  :hints (("Goal" :expand ((svf (list :var k) (put k (cons ty v) fr) heap)))))

(defthm sx-assign-run-f
  (implies (and (not (car (svf ca fr heap))) (consp (dty tmp fr)) (scalar-ok (car (dty tmp fr)) (mv-nth 1 (svf ca fr heap))))
           (equal (sxf (list :assign (list :var tmp) ca) fr heap)
                  (mv :normal (put tmp (cons (car (dty tmp fr)) (mv-nth 1 (svf ca fr heap))) fr) heap)))
  :hints (("Goal" :in-theory (e/d (dty) (svf)) :expand ((sxf (list :assign (list :var tmp) ca) fr heap)))))

(defthm sx-if-stmt-f
  (implies (and (not (car (svf c fr heap))) (booleanp (mv-nth 1 (svf c fr heap))))
           (equal (sxf (list :if c a b) fr heap)
                  (if (mv-nth 1 (svf c fr heap)) (sxf-list a fr heap) (sxf-list b fr heap))))
  :hints (("Goal" :expand ((sxf (list :if c a b) fr heap)) :in-theory (disable sxf-list svf))))

(defthm sx-list-one-f
  (equal (sxf-list (list a) fr heap) (mv-let (st fr2 h2) (sxf a fr heap) (mv st fr2 h2)))
  :hints (("Goal" :expand ((sxf-list (list a) fr heap) (:free (fr heap) (sxf-list nil fr heap))))))

(defthm sif-glue-f
  (let ((fr1-f (mv-nth 1 (sxf-list sc fr heap))))
    (implies (and (equal (car (sxf-list sc fr heap)) :normal) (equal (mv-nth 2 (sxf-list sc fr heap)) heap)
                  (not (car (svf cc fr1-f heap))) (equal (mv-nth 1 (svf cc fr1-f heap)) c) (booleanp c)
                  (equal (dty tmp fr) (list ta))
                  (if c (and (equal (car (sxf-list sa fr1-f heap)) :normal) (equal (mv-nth 2 (sxf-list sa fr1-f heap)) heap)
                             (not (car (svf ca (mv-nth 1 (sxf-list sa fr1-f heap)) heap)))
                             (equal (mv-nth 1 (svf ca (mv-nth 1 (sxf-list sa fr1-f heap)) heap)) v) (scalar-ok ta v))
                    (and (equal (car (sxf-list sb fr1-f heap)) :normal) (equal (mv-nth 2 (sxf-list sb fr1-f heap)) heap)
                         (not (car (svf cb (mv-nth 1 (sxf-list sb fr1-f heap)) heap)))
                         (equal (mv-nth 1 (svf cb (mv-nth 1 (sxf-list sb fr1-f heap)) heap)) v) (scalar-ok ta v))))
             (and (equal (car (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) :normal)
                  (equal (mv-nth 2 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)
                  (not (car (svf (list :var tmp) (mv-nth 1 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)))
                  (equal (mv-nth 1 (svf (list :var tmp) (mv-nth 1 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap))
                         v))))
  :hints (("Goal" :do-not-induct t :in-theory (disable sxf svf sxf-list dty))))

(defthm a-sx-if-f
  (implies (gs-ifp x st)
           (equal (a-sxf x env s st defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e c) (a-sxf (cadr x) env s st defs (1- n))
                      (cond (e (mv e nil))
                            (c (a-sxf (caddr x) env s st defs (1- n)))
                            (t (a-sxf (cadddr x) env s st defs (1- n))))))))
  :hints (("Goal" :in-theory (disable g-st-free g-role a-ev a-sxf-list) :expand ((a-sxf x env s st defs n)))))

(defthm sif-then-f
  (let ((fr1-f (mv-nth 1 (sxf-list sc fr heap))))
    (implies (and (equal (car (sxf-list sc fr heap)) :normal) (equal (mv-nth 2 (sxf-list sc fr heap)) heap)
                  (not (car (svf cc fr1-f heap))) (mv-nth 1 (svf cc fr1-f heap)) (booleanp (mv-nth 1 (svf cc fr1-f heap)))
                  (consp (dty tmp fr))
                  (equal (car (sxf-list sa fr1-f heap)) :normal) (equal (mv-nth 2 (sxf-list sa fr1-f heap)) heap)
                  (not (car (svf ca (mv-nth 1 (sxf-list sa fr1-f heap)) heap)))
                  (scalar-ok (car (dty tmp fr)) (mv-nth 1 (svf ca (mv-nth 1 (sxf-list sa fr1-f heap)) heap))))
             (and (equal (car (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) :normal)
                  (equal (mv-nth 2 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)
                  (not (car (svf (list :var tmp) (mv-nth 1 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)))
                  (equal (mv-nth 1 (svf (list :var tmp) (mv-nth 1 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap))
                         (mv-nth 1 (svf ca (mv-nth 1 (sxf-list sa fr1-f heap)) heap))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable sxf svf sxf-list sif-glue-f if-stmts svf-is-sv sv-is-fv-f sxf-sx-list-cons sxf-list-is-sx-list sx-list-is-fx-list-f)
           :use (:instance sif-glue-f (ta (car (dty tmp fr))) (c t)
                           (v (mv-nth 1 (svf ca (mv-nth 1 (sxf-list sa (mv-nth 1 (sxf-list sc fr heap)) heap)) heap)))))))

(defthm sif-else-f
  (let ((fr1-f (mv-nth 1 (sxf-list sc fr heap))))
    (implies (and (equal (car (sxf-list sc fr heap)) :normal) (equal (mv-nth 2 (sxf-list sc fr heap)) heap)
                  (not (car (svf cc fr1-f heap))) (not (mv-nth 1 (svf cc fr1-f heap)))
                  (consp (dty tmp fr))
                  (equal (car (sxf-list sb fr1-f heap)) :normal) (equal (mv-nth 2 (sxf-list sb fr1-f heap)) heap)
                  (not (car (svf cb (mv-nth 1 (sxf-list sb fr1-f heap)) heap)))
                  (scalar-ok (car (dty tmp fr)) (mv-nth 1 (svf cb (mv-nth 1 (sxf-list sb fr1-f heap)) heap))))
             (and (equal (car (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) :normal)
                  (equal (mv-nth 2 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)
                  (not (car (svf (list :var tmp) (mv-nth 1 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)))
                  (equal (mv-nth 1 (svf (list :var tmp) (mv-nth 1 (sxf-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap))
                         (mv-nth 1 (svf cb (mv-nth 1 (sxf-list sb fr1-f heap)) heap))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable sxf svf sxf-list sif-glue-f if-stmts svf-is-sv sv-is-fv-f sxf-sx-list-cons sxf-list-is-sx-list sx-list-is-fx-list-f)
           :use (:instance sif-glue-f (ta (car (dty tmp fr))) (c nil)
                           (v (mv-nth 1 (svf cb (mv-nth 1 (sxf-list sb (mv-nth 1 (sxf-list sc fr heap)) heap)) heap)))))))

(in-theory (disable sif-glue-f))

(defthm gs-sem-else-type-f
  (implies (and (gs-ifp x st) (not (gsx 0))
                (gs-sem-f (cadddr x) em (j2 4) (j2 5) sigs fnames st env s defs n fr heap o)
                (not (car (a-sxf (cadddr x) env s st defs n))) (sfc-ok :term (cadddr x) sigs st) (em-ok em env fr)
                (decl-ok (j3 5) fr) (no-prim-defs defs) (sf-orc sigs defs st o) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap))
           (scalar-ok (j2 3) (mv-nth 1 (a-sxf (cadddr x) env s st defs n))))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)
           :use ((:instance gs-sem-use-f (x (cadddr x)) (cnt (j2 4)) (locs (j2 5))) g-sexpr-if-out))))

(defmacro fr1-f () '(mv-nth 1 (sxf-list (j1 1) fr heap)))

(defthm gsx-if-f
  (implies (and (gs-ifp x st)
                (gs-sem-f (cadr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gs-sem-f (caddr x) em (j1 4) (j1 5) sigs fnames st env s defs (1- n) (fr1-f) heap o)
                (gs-sem-f (cadddr x) em (j2 4) (j2 5) sigs fnames st env s defs (1- n) (fr1-f) heap o)
                (sn-ok-f (cadr x) em cnt locs sigs fnames st)
                (sn-ok-f (caddr x) em (j1 4) (j1 5) sigs fnames st)
                (sn-ok-f (cadddr x) em (j2 4) (j2 5) sigs fnames st))
           (gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gs-sem-f x em cnt locs sigs fnames st env s defs n fr heap o))
           :cases ((mv-nth 1 (a-sxf (cadr x) env s st defs (1- n))))
           :in-theory (disable g-sexpr a-sxf sxf-list sxf svf no-calls sfc-ok em-ok scalar-ok st-ok obj-is gs-ifp
                               g-sexpr-if if-stmts g-tmp nfix dty decl-ok-subset sif-glue-f sv-is-fv-f fv
                               sx-list-is-fx-list-f fx-list sxf-sx-list-cons svf-is-sv sxf-list-is-sx-list)
           :do-not (quote (eliminate-destructors generalize))
           :use ((:instance decl-ok-subset (a (j1 5)) (b (j2 5)))
                 (:instance decl-ok-subset (a (j2 5)) (b (j3 5)))))))
