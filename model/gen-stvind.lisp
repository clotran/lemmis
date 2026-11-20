; gen-stvind: gstv-sem by induction (GEN.md 4 (4a) (2b) and (4)): every
; `stv-plain` statement -- the stobj, field and element updates (dests nil),
; a tuple, a :sub call (updated stobj arguments or not), if, and a lambda
; without mv over them -- run by sxc-list answers a-stv's S' and values.

(in-package "ACL2")

(include-book "gen-stvif")

(defun stv-plain (x outs st sigs)
  (declare (xargs :measure (acl2-count x)))
  (cond ((atom x) (and (st-plain :term x nil st) (no-calls :term x sigs nil) (equal (nvals outs) 0)))
        ((not (true-listp x)) nil)
        ((eq (car x) 'cons) (and (st-plain :acts (g-conses x) outs st) (no-calls :list (g-conses x) sigs nil)))
        ((or (eq (g-role (car x) st) :set) (eq (g-role (car x) st) :seti))
         (and (st-plain :term x nil st) (no-calls :term x sigs nil) (equal (nvals outs) 0)))
        ((eq (car x) 'if)
         (and (no-calls :term (cadr x) sigs nil) (stv-plain (caddr x) outs st sigs) (stv-plain (cadddr x) outs st sigs)))
        ((consp (car x))
         (and (not (member-equal 'mv (cadr (car x)))) (no-calls :list (cdr x) sigs nil)
              (st-plain :acts (cdr x) (cadr (car x)) st) (stv-plain (caddr (car x)) outs st sigs)))
        ((eq (g-role (car x) st) :sub)
         (and (no-calls :list (cdr x) sigs nil) (no-calls :list (g-cvals (g-obj (car x) st) (cdr x) st) sigs nil)
              (st-plain :acts (cdr x) (g-obj (car x) st) st)))
        (t nil)))

(set-irrelevant-formals-ok t)
(set-ignore-ok t)

(defun-nx gstv-ind (x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
  (declare (xargs :measure (acl2-count x) :verify-guards nil
                  :hints (("Goal" :in-theory (disable g-sexpr g-stmt g-svals g-sacts a-sx a-st a-sx-list a-sacts sx-list
                                                      g-role g-mvnth g-tmp nfix okey put)))))
  (cond ((atom x) nil)
        ((not (true-listp x)) nil)
        ((eq (car x) 'cons) nil)
        ((or (eq (g-role (car x) st) :set) (eq (g-role (car x) st) :seti)) nil)
        ((eq (car x) 'if)
         (list (gstv-ind (caddr x) em (e1 4) (e1 5) sigs fnames st outs dests env s defs (1- n) (sfa) heap o)
               (gstv-ind (cadddr x) em (iad 2) (iad 3) sigs fnames st outs dests env s defs (1- n) (sfa) heap o)))
        ((consp (car x))
         (gstv-ind (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests (lenv) (ls1) defs (1- n)
                   (lfc) (lh1) o))
        (t nil)))

(defthm gstv-lam-any
  (implies (and (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (vars))) (sn-hyps) (em-nostobj em st)
                (no-calls :list (cdr x) sigs nil) (st-plain :acts (cdr x) (vars) st)
                (gstv-sem (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests (lenv) (ls1) defs (1- n) (lfc) (lh1) o)
                (stv-grow (caddr (car x)) (append (gl1 2) em) (la 2) (la 3) sigs fnames st outs dests))
           (and (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
                (stv-grow x em cnt locs sigs fnames st outs dests)))
  :hints (("Goal" :do-not-induct t :in-theory (gst-min gstv-lam stv-grow-lam)
           :use ((:instance gst-sem-thm (flag :acts) (x (cdr x)) (vars (vars)) (cnt (gl1 3)) (locs (gl1 4)) (n (1- n)) (fr (lfb)))
                 (:instance stan-ok-holds (vars (vars)) (xs (cdr x)) (cnt (gl1 3)) (locs (gl1 4)))))))

(defthm gstv-sem-thm
  (implies (and (sn-hyps) (em-nostobj em st) (stv-plain x outs st sigs))
           (and (gstv-sem x em cnt locs sigs fnames st outs dests env s defs n fr heap o)
                (stv-grow x em cnt locs sigs fnames st outs dests)))
  :hints (("Goal" :induct (gstv-ind x em cnt locs sigs fnames st outs dests env s defs n fr heap o) :do-not-induct t
           :in-theory (gst-min (:induction gstv-ind) stv-plain em-nostobj-append em-nostobj-g-svals
                               gstv-leaf gstv-cons gstv-sub gstv-if stv-grow-if gstv-lam-any))))
