; gen-stc: a-stc, the source's meaning with stobj calls (GEN.md 4 (4a) (i)).
; a-st plus two cases, through the oracle a-call-val (f ks s) => (mv err s'
; rs), rs the call's results by position (nil at a stobj's):
;   - a call of a :sub f answering S: f's arguments as a lambda's are (the
;     values read S as it was, the stobj arguments' updates threaded), then
;     a-call-val on the values (`a-stc-call`);
;   - the mv lambda: when its vars bind mv to a :sub call, the call runs
;     first (as g-stmt's g-callst does), mv's value is its results rs; a
;     stobj var bound to (mv-nth 'k mv) keeps S (the call updated it), a
;     value var bound to (mv-nth 'k mv) is rs's k-th.
; `a-stc-is-a-st`: on st-plain terms, wherever a-st answers no error,
; a-stc is a-st, so every gst-sem fact about a-st is one about a-stc.

(in-package "ACL2")

(include-book "gen-stcallst")
(include-book "gen-stind")

(set-verify-guards-eagerness 0)

(mutual-recursion
 (defun a-stc (x env s st defs n)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (mv :fuel s))
         ((symbolp x) (if (eq (g-role x st) :stobj) (mv nil s) (mv :stobj s)))
         ((atom x) (mv :stobj s))
         ((eq (g-role (car x) st) :set)
          (mv-let (e v) (a-sx (kadr x) env s st defs (1- n))
            (if e (mv e s)
              (mv-let (e s1) (a-stc (kaddr x) env s st defs (1- n))
                (if e (mv e s) (mv nil (put (g-comp (car x) st) v s1)))))))
         ((eq (g-role (car x) st) :seti)
          (mv-let (e i) (a-sx (kadr x) env s st defs (1- n))
            (if e (mv e s)
              (mv-let (e v) (a-sx (kaddr x) env s st defs (1- n))
                (if e (mv e s)
                  (mv-let (e s1) (a-stc (kadddr x) env s st defs (1- n))
                    (let ((p (cdr (lkp (g-comp (car x) st) s1))))
                      (cond (e (mv e s))
                            ((not (and (farrayp p) (integerp i))) (mv :type s))
                            ((not (and (<= 0 i) (< i (len (cdr p))))) (mv :bounds s))
                            (t (mv nil (put (g-comp (car x) st) (cons :array (update-nth i v (cdr p))) s1)))))))))))
         ((eq (car x) 'if)
          (mv-let (e c) (a-sx (kadr x) env s st defs (1- n))
            (cond (e (mv e s))
                  (c (a-stc (kaddr x) env s st defs (1- n)))
                  (t (a-stc (kadddr x) env s st defs (1- n))))))
         ((consp (car x))
          ; mv's call first (on S), then the arguments as a-st's lambda
          (mv-let (e mvv s0)
            (if (member-equal 'mv (kadr (car x)))
                (a-stc-call (g-arg-of 'mv (kadr (car x)) (cdr x)) env s st defs (1- n))
              (mv nil nil s))
            (if e (mv e s)
              (mv-let (e vs s1) (a-stc-args (kadr (car x)) (cdr x) env s s0 mvv st defs (1- n))
                (if e (mv e s)
                  (a-stc (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) s1 st defs (1- n)))))))
         ((eq (g-role (car x) st) :sub)
          (mv-let (e rs s1) (a-stc-call x env s st defs (1- n))
            (declare (ignore rs))
            (if e (mv e s) (mv nil s1))))
         (t (mv :stobj s))))
 (defun a-stc-args (vars xs env s0 s mvv st defs n)
   ; a-st-args, plus: mv's value is mvv; an mv-nth of mv is its result
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (mv :fuel nil s))
         ((atom xs) (mv nil nil s))
         ((eq (kar vars) 'mv)
          (mv-let (e vs s2) (a-stc-args (kdr vars) (cdr xs) env s0 s mvv st defs (1- n))
            (mv e (cons mvv vs) s2)))
         ((eq (g-role (kar vars) st) :stobj)
          (if (g-mvnth (car xs))
              (mv-let (e vs s2) (a-stc-args (kdr vars) (cdr xs) env s0 s mvv st defs (1- n))
                (mv e (cons nil vs) s2))
            (mv-let (e s1) (a-stc (car xs) env s st defs (1- n))
              (if e (mv e nil s)
                (mv-let (e vs s2) (a-stc-args (kdr vars) (cdr xs) env s0 s1 mvv st defs (1- n))
                  (mv e (cons nil vs) s2))))))
         (t (mv-let (e v) (if (g-mvnth (car xs))
                              (mv nil (nth (g-mvnth (car xs)) (true-list-fix (cdr (lkp 'mv env)))))
                            (a-sx (car xs) env s0 st defs (1- n)))
              (if e (mv e nil s)
                (mv-let (e vs s2) (a-stc-args (kdr vars) (cdr xs) env s0 s mvv st defs (1- n))
                  (mv e (cons v vs) s2)))))))
 (defun a-stc-call (x env s st defs n)
   ; (mv err results S'): f's arguments, then the oracle
   (declare (xargs :measure (nfix n)))
   (if (zp n) (mv :fuel nil s)
     (mv-let (e vs s1) (a-stc-args (g-obj (kar x) st) (kdr x) env s s nil st defs (1- n))
       (if e (mv e nil s)
         (mv-let (e s2 rs) (a-call-val (kar x) (g-cvals (g-obj (kar x) st) vs st) s1)
           (if e (mv e nil s) (mv nil rs s2))))))))

(in-theory (disable a-stc a-stc-args a-stc-call))

; ---- on st-plain, wherever a-st answers, a-stc is a-st

(defthm a-st-mvnth-err
  (implies (and (g-mvnth x) (not (equal (g-role 'mv-nth st) :set)) (not (equal (g-role 'mv-nth st) :seti)))
           (car (a-st x env s st defs n)))
  :hints (("Goal" :expand ((a-st x env s st defs n)))))

(defthm a-sx-mvnth-err
  (implies (and (g-mvnth x) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st)))
           (car (a-sx x env s st defs n)))
  :hints (("Goal" :in-theory (disable a-ev g-mvnth g-st-free a-ev-mv-nth g-mvnth-free)
           :expand ((a-sx x env s st defs n))
           :use (g-mvnth-free a-ev-mv-nth))))

(defun-nx stc-ind (flag x vars env s0 s st defs n)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) t)
        ((eq flag :args)
         (cond ((atom x) t)
               ((eq (g-role (kar vars) st) :stobj)
                (list (stc-ind :term (car x) nil env s0 s st defs (1- n))
                      (stc-ind :args (cdr x) (kdr vars) env s0 (mv-nth 1 (a-st (car x) env s st defs (1- n))) st defs (1- n))))
               (t (stc-ind :args (cdr x) (kdr vars) env s0 s st defs (1- n)))))
        ((atom x) t)
        ((eq (g-role (car x) st) :set) (stc-ind :term (kaddr x) nil env s0 s st defs (1- n)))
        ((eq (g-role (car x) st) :seti) (stc-ind :term (kadddr x) nil env s0 s st defs (1- n)))
        ((eq (car x) 'if) (list (stc-ind :term (kaddr x) nil env s0 s st defs (1- n))
                                (stc-ind :term (kadddr x) nil env s0 s st defs (1- n))))
        ((consp (car x))
         (list (stc-ind :args (cdr x) (kadr (car x)) env s s st defs (1- n))
               (stc-ind :term (kaddr (car x)) nil
                        (pairlis$ (true-list-fix (kadr (car x))) (mv-nth 1 (a-st-args (kadr (car x)) (cdr x) env s s st defs (1- n))))
                        s0 (mv-nth 2 (a-st-args (kadr (car x)) (cdr x) env s s st defs (1- n))) st defs (1- n))))
        (t t)))

(defthm a-stc-is-a-st-flag
  (let ((hyps (and (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (not (g-role nil st)))))
    (if (eq flag :args)
        (implies (and hyps (st-plain :acts x vars st) (not (member-equal 'mv vars))
                      (not (car (a-st-args vars x env s0 s st defs n))))
                 (equal (a-stc-args vars x env s0 s nil st defs n) (a-st-args vars x env s0 s st defs n)))
      (implies (and hyps (st-plain :term x nil st) (not (car (a-st x env s st defs n))))
               (equal (a-stc x env s st defs n) (a-st x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :induct (stc-ind flag x vars env s0 s st defs n)
           :in-theory (disable a-sx g-mvnth g-role put lkp g-comp farrayp)
           :expand ((a-stc x env s st defs n) (a-st x env s st defs n)
                    (a-stc-args vars x env s0 s nil st defs n) (a-st-args vars x env s0 s st defs n)
                    (st-plain :term x nil st) (st-plain :acts x vars st)))))

(defthm a-stc-is-a-st
  (implies (and (st-plain :term x nil st) (not (car (a-st x env s st defs n)))
                (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (not (g-role nil st)))
           (equal (a-stc x env s st defs n) (a-st x env s st defs n)))
  :hints (("Goal" :use (:instance a-stc-is-a-st-flag (flag :term)))))
