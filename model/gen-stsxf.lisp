; gen-stsxf: a-sxf, a-sx plus calls of functions given the stobj (GEN.md
; "What remains" 4b): `(f args)` for f defined in defs, reading S, is f's
; body on the arguments' values (a stobj argument's value nil, as a-sx's
; stobj var), S unchanged -- a-ev's call case on stobj terms. A new
; evaluator, so no earlier theorem gains a case; `a-sxf-is-a-sx`: wherever
; a-sx answers no error, a-sxf is a-sx (a-sx answers a-prim's error on such
; a call; under no-prim-defs no primitive is defined).

(in-package "ACL2")

(include-book "gen-stsem")
(include-book "gen-proof")

(set-verify-guards-eagerness 0)

(mutual-recursion
 (defun a-sxf (x env s st defs n)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (mv :fuel nil))
         ((g-st-free x st) (a-ev x env defs n))
         ((atom x) (if (eq (g-role x st) :stobj) (mv nil nil) (mv :stobj nil)))
         ((consp (car x))
          (mv-let (e vs) (a-sxf-list (cdr x) env s st defs (1- n))
            (if e (mv e nil) (a-sxf (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) s st defs (1- n)))))
         ((eq (g-role (car x) st) :field) (let ((p (lkp (g-comp (car x) st) s))) (if (consp p) (mv nil (cdr p)) (mv :type nil))))
         ((eq (g-role (car x) st) :size)
          (let ((p (lkp (g-comp (car x) st) s))) (if (farrayp (cdr p)) (mv nil (len (cddr p))) (mv :type nil))))
         ((eq (g-role (car x) st) :elem)
          (mv-let (e i) (a-sxf (kadr x) env s st defs (1- n))
            (if e (mv e nil) (read-elem (cdr (lkp (g-comp (car x) st) s)) i))))
         ; an extern read: not modelled here (GEN.md 4c step 3), an error
         ((member-eq (g-role (car x) st) '(:xfield :xsize :xelem)) (mv :extern nil))
         ((eq (car x) 'if)
          (mv-let (e c) (a-sxf (kadr x) env s st defs (1- n))
            (cond (e (mv e nil))
                  (c (a-sxf (kaddr x) env s st defs (1- n)))
                  (t (a-sxf (kadddr x) env s st defs (1- n))))))
         (t (mv-let (e vs) (a-sxf-list (cdr x) env s st defs (1- n))
              (cond (e (mv e nil))
                    ((consp (lkp (car x) defs))
                     (let ((d (lkp (car x) defs)))
                       (a-sxf (kaddr d) (pairlis$ (true-list-fix (kadr d)) vs) s st defs (1- n))))
                    (t (a-prim (car x) vs)))))))
 (defun a-sxf-list (xs env s st defs n)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (mv :fuel nil))
         ((atom xs) (mv nil nil))
         (t (mv-let (e v) (a-sxf (car xs) env s st defs (1- n))
              (if e (mv e nil)
                (mv-let (e vs) (a-sxf-list (cdr xs) env s st defs (1- n))
                  (if e (mv e nil) (mv nil (cons v vs))))))))))

(in-theory (disable a-sxf a-sxf-list))

(defthm a-prim-not-prim
  (implies (not (member-equal f *g-prims*)) (car (a-prim f vs)))
  :hints (("Goal" :in-theory (enable a-prim))))

(defthm no-prim-defs-lkp
  (implies (and (no-prim-defs defs) (member-equal f *g-prims*)) (not (consp (lkp f defs))))
  :hints (("Goal" :in-theory (enable lkp))))

(defthm defs-lkp-not-prim
  (implies (and (no-prim-defs defs) (consp (lkp f defs))) (not (member-equal f *g-prims*)))
  :hints (("Goal" :use no-prim-defs-lkp :in-theory (disable no-prim-defs-lkp no-prim-defs))))

(defun asxf-ind (flag x env s st defs n)
  (declare (xargs :measure (nfix n) :verify-guards nil))
  (if (zp n) (list x env)
    (if (eq flag :sx)
        (if (atom x) nil
          (mv-let (e vs) (a-sx-list (cdr x) env s st defs (1- n))
            (declare (ignore e))
            (list (asxf-ind :list (cdr x) env s st defs (1- n))
                  (asxf-ind :sx (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) s st defs (1- n))
                  (asxf-ind :sx (kaddr (lkp (car x) defs)) (pairlis$ (true-list-fix (kadr (lkp (car x) defs))) vs)
                            s st defs (1- n))
                  (asxf-ind :sx (kadr x) env s st defs (1- n))
                  (asxf-ind :sx (kaddr x) env s st defs (1- n))
                  (asxf-ind :sx (kadddr x) env s st defs (1- n)))))
      (if (atom x) nil
        (list (asxf-ind :sx (car x) env s st defs (1- n))
              (asxf-ind :list (cdr x) env s st defs (1- n)))))))

(defthm a-sxf-is-a-sx-flag
  (implies (no-prim-defs defs)
           (if (eq flag :sx)
               (implies (not (mv-nth 0 (a-sx x env s st defs n))) (equal (a-sxf x env s st defs n) (a-sx x env s st defs n)))
             (implies (not (mv-nth 0 (a-sx-list x env s st defs n)))
                      (equal (a-sxf-list x env s st defs n) (a-sx-list x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :induct (asxf-ind flag x env s st defs n)
           :in-theory (disable a-sx a-sx-list a-ev a-prim read-elem g-st-free no-prim-defs)
           :expand ((a-sx x env s st defs n) (a-sxf x env s st defs n) (a-sx-list x env s st defs n)
                    (a-sxf-list x env s st defs n)))))

(defthm a-sxf-is-a-sx
  (implies (and (no-prim-defs defs) (not (mv-nth 0 (a-sx x env s st defs n))))
           (equal (a-sxf x env s st defs n) (a-sx x env s st defs n)))
  :hints (("Goal" :use (:instance a-sxf-is-a-sx-flag (flag :sx)))))

(defthm a-sxf-list-is-a-sx-list
  (implies (and (no-prim-defs defs) (not (mv-nth 0 (a-sx-list x env s st defs n))))
           (equal (a-sxf-list x env s st defs n) (a-sx-list x env s st defs n)))
  :hints (("Goal" :use (:instance a-sxf-is-a-sx-flag (flag :list)))))
