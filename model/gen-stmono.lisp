; gen-stmono: fuel monotonicity of the source's meanings (GEN.md 4 (4a) (ii)).
; Wherever a-ev (a-ev-list) answers no error at fuel n, it answers the same
; at any fuel m >= n; and so for a-sx (a-sx-list). The fuel is a bound, not
; part of the meaning: what a call's arguments answer does not depend on
; where in an argument list they are evaluated (a-stc-args spends fuel on
; stobj arguments, a-stcall's a-sx-list does not).

(in-package "ACL2")

(include-book "gen-stsem")

(defun aev-mono-ind (flag x env defs n m)
  (declare (xargs :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (zp m)) (list x env defs)
    (if (eq flag :ev)
        (cond ((or (atom x) (eq (car x) 'quote)) nil)
              ((eq (car x) 'if) (list (aev-mono-ind :ev (kadr x) env defs (1- n) (1- m))
                                      (aev-mono-ind :ev (kaddr x) env defs (1- n) (1- m))
                                      (aev-mono-ind :ev (kadddr x) env defs (1- n) (1- m))))
              (t (mv-let (e vs) (a-ev-list (cdr x) env defs (1- n))
                   (declare (ignore e))
                   (list (aev-mono-ind :list (cdr x) env defs (1- n) (1- m))
                         (aev-mono-ind :ev (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) defs (1- n) (1- m))
                         (aev-mono-ind :ev (kaddr (lkp (car x) defs)) (pairlis$ (true-list-fix (kadr (lkp (car x) defs))) vs)
                                       defs (1- n) (1- m))))))
      (if (atom x) nil
        (list (aev-mono-ind :ev (car x) env defs (1- n) (1- m))
              (aev-mono-ind :list (cdr x) env defs (1- n) (1- m)))))))

(defthm a-ev-mono-flag
  (implies (and (integerp m) (<= n m))
           (if (eq flag :ev)
               (implies (not (mv-nth 0 (a-ev x env defs n))) (equal (a-ev x env defs m) (a-ev x env defs n)))
             (implies (not (mv-nth 0 (a-ev-list x env defs n))) (equal (a-ev-list x env defs m) (a-ev-list x env defs n)))))
  :rule-classes nil
  :hints (("Goal" :induct (aev-mono-ind flag x env defs n m) :in-theory (disable a-ev a-ev-list a-prim)
           :expand ((a-ev x env defs n) (a-ev x env defs m) (a-ev-list x env defs n) (a-ev-list x env defs m)))))

(defthm a-ev-mono
  (implies (and (not (mv-nth 0 (a-ev x env defs n))) (integerp m) (<= n m))
           (equal (a-ev x env defs m) (a-ev x env defs n)))
  :rule-classes nil
  :hints (("Goal" :use (:instance a-ev-mono-flag (flag :ev)))))

(defthm a-ev-list-mono
  (implies (and (not (mv-nth 0 (a-ev-list x env defs n))) (integerp m) (<= n m))
           (equal (a-ev-list x env defs m) (a-ev-list x env defs n)))
  :rule-classes nil
  :hints (("Goal" :use (:instance a-ev-mono-flag (flag :list)))))

(defun asx-mono-ind (flag x env s st defs n m)
  (declare (xargs :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (zp m)) (list x env s)
    (if (eq flag :sx)
        (cond ((or (g-st-free x st) (atom x)) nil)
              ((consp (car x))
               (mv-let (e vs) (a-sx-list (cdr x) env s st defs (1- n))
                 (declare (ignore e))
                 (list (asx-mono-ind :list (cdr x) env s st defs (1- n) (1- m))
                       (asx-mono-ind :sx (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) s st defs (1- n) (1- m)))))
              (t (list (asx-mono-ind :sx (kadr x) env s st defs (1- n) (1- m))
                       (asx-mono-ind :sx (kaddr x) env s st defs (1- n) (1- m))
                       (asx-mono-ind :sx (kadddr x) env s st defs (1- n) (1- m))
                       (asx-mono-ind :list (cdr x) env s st defs (1- n) (1- m)))))
      (if (atom x) nil
        (list (asx-mono-ind :sx (car x) env s st defs (1- n) (1- m))
              (asx-mono-ind :list (cdr x) env s st defs (1- n) (1- m)))))))

(defthm a-sx-mono-flag
  (implies (and (integerp m) (<= n m))
           (if (eq flag :sx)
               (implies (not (mv-nth 0 (a-sx x env s st defs n))) (equal (a-sx x env s st defs m) (a-sx x env s st defs n)))
             (implies (not (mv-nth 0 (a-sx-list x env s st defs n)))
                      (equal (a-sx-list x env s st defs m) (a-sx-list x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :induct (asx-mono-ind flag x env s st defs n m) :in-theory (disable a-sx a-sx-list a-ev a-prim read-elem g-st-free)
           :expand ((a-sx x env s st defs n) (a-sx x env s st defs m) (a-sx-list x env s st defs n) (a-sx-list x env s st defs m)))
          (and stable-under-simplificationp '(:use ((:instance a-ev-mono (n n) (m m)))))))

(defthm a-sx-mono
  (implies (and (not (mv-nth 0 (a-sx x env s st defs n))) (integerp m) (<= n m))
           (equal (a-sx x env s st defs m) (a-sx x env s st defs n)))
  :rule-classes nil
  :hints (("Goal" :use (:instance a-sx-mono-flag (flag :sx)))))

(defthm a-sx-list-mono
  (implies (and (not (mv-nth 0 (a-sx-list x env s st defs n))) (integerp m) (<= n m))
           (equal (a-sx-list x env s st defs m) (a-sx-list x env s st defs n)))
  :rule-classes nil
  :hints (("Goal" :use (:instance a-sx-mono-flag (flag :list)))))
