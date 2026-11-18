; gen-sfmono: fuel monotonicity of a-sxf (gen-stsxf), as gen-stmono's
; a-sx-mono: wherever a-sxf (a-sxf-list) answers no error at fuel n, it
; answers the same at any fuel m >= n. A call's value arguments answer the
; same whether or not the stobj argument is evaluated beside them.

(in-package "ACL2")

(include-book "gen-stmono")
(include-book "gen-stsxf")

(defun asxf-mono-ind (flag x env s st defs n m)
  (declare (xargs :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (zp m)) (list x env s)
    (if (eq flag :sx)
        (cond ((or (g-st-free x st) (atom x)) nil)
              (t (mv-let (e vs) (a-sxf-list (cdr x) env s st defs (1- n))
                   (declare (ignore e))
                   (list (asxf-mono-ind :list (cdr x) env s st defs (1- n) (1- m))
                         (asxf-mono-ind :sx (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) s st defs (1- n) (1- m))
                         (asxf-mono-ind :sx (kaddr (lkp (car x) defs)) (pairlis$ (true-list-fix (kadr (lkp (car x) defs))) vs)
                                        s st defs (1- n) (1- m))
                         (asxf-mono-ind :sx (kadr x) env s st defs (1- n) (1- m))
                         (asxf-mono-ind :sx (kaddr x) env s st defs (1- n) (1- m))
                         (asxf-mono-ind :sx (kadddr x) env s st defs (1- n) (1- m))))))
      (if (atom x) nil
        (list (asxf-mono-ind :sx (car x) env s st defs (1- n) (1- m))
              (asxf-mono-ind :list (cdr x) env s st defs (1- n) (1- m)))))))

(defthm a-sxf-mono-flag
  (implies (and (integerp m) (<= n m))
           (if (eq flag :sx)
               (implies (not (mv-nth 0 (a-sxf x env s st defs n))) (equal (a-sxf x env s st defs m) (a-sxf x env s st defs n)))
             (implies (not (mv-nth 0 (a-sxf-list x env s st defs n)))
                      (equal (a-sxf-list x env s st defs m) (a-sxf-list x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :induct (asxf-mono-ind flag x env s st defs n m)
           :in-theory (disable a-sxf a-sxf-list a-ev a-prim read-elem g-st-free)
           :expand ((a-sxf x env s st defs n) (a-sxf x env s st defs m) (a-sxf-list x env s st defs n)
                    (a-sxf-list x env s st defs m)))
          (and stable-under-simplificationp '(:use ((:instance a-ev-mono (n n) (m m)))))))

(defthm a-sxf-mono
  (implies (and (not (mv-nth 0 (a-sxf x env s st defs n))) (integerp m) (<= n m))
           (equal (a-sxf x env s st defs m) (a-sxf x env s st defs n)))
  :rule-classes nil
  :hints (("Goal" :use (:instance a-sxf-mono-flag (flag :sx)))))

(defthm a-sxf-list-mono
  (implies (and (not (mv-nth 0 (a-sxf-list x env s st defs n))) (integerp m) (<= n m))
           (equal (a-sxf-list x env s st defs m) (a-sxf-list x env s st defs n)))
  :rule-classes nil
  :hints (("Goal" :use (:instance a-sxf-mono-flag (flag :list)))))
