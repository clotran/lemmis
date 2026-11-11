; gen-stsem: the source's meaning for stobj code, a-st -- what gen-st's
; g-sexpr and g-stmt translate, in ACL2's own order of evaluation. A stobj
; is its components, the alist fsem's heap keeps for its object (comp ->
; integer, or comp -> (:array . elements)); one stobj is threaded (S).
; An index outside its array is the error :bounds, which ACL2's guard
; proof rules out, as an integer outside int64 is :range (a-ev).
;
;   a-sx  a term reading S -> (mv err value)
;   a-st  a term answering S -> (mv err S')
;
; The tests: on clotran's hpg-spush, fsem running g-st-module's subroutine
; leaves hs as a-st leaves S, or both answer :bounds.

(in-package "ACL2")

(include-book "gen-st")

(set-verify-guards-eagerness 0)

(mutual-recursion
 (defun a-sx (x env s st defs n)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (mv :fuel nil))
         ((g-st-free x st) (a-ev x env defs n))
         ((or (atom x) (consp (car x))) (mv :stobj nil))
         ((eq (g-role (car x) st) :field) (let ((p (lkp (g-comp (car x) st) s))) (if (consp p) (mv nil (cdr p)) (mv :type nil))))
         ((eq (g-role (car x) st) :size)
          (let ((p (lkp (g-comp (car x) st) s))) (if (farrayp (cdr p)) (mv nil (len (cddr p))) (mv :type nil))))
         ((eq (g-role (car x) st) :elem)
          (mv-let (e i) (a-sx (kadr x) env s st defs (1- n))
            (if e (mv e nil) (read-elem (cdr (lkp (g-comp (car x) st) s)) i))))
         (t (mv-let (e vs) (a-sx-list (cdr x) env s st defs (1- n))
              (if e (mv e nil) (a-prim (car x) vs))))))
 (defun a-sx-list (xs env s st defs n)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (mv :fuel nil))
         ((atom xs) (mv nil nil))
         (t (mv-let (e v) (a-sx (car xs) env s st defs (1- n))
              (if e (mv e nil)
                (mv-let (e vs) (a-sx-list (cdr xs) env s st defs (1- n))
                  (if e (mv e nil) (mv nil (cons v vs))))))))))

(mutual-recursion
 (defun a-st (x env s st defs n)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (mv :fuel s))
         ((symbolp x) (if (eq (g-role x st) :stobj) (mv nil s) (mv :stobj s)))
         ((atom x) (mv :stobj s))
         ((eq (g-role (car x) st) :set)
          ; the value first, on S as it is; then the inner update
          (mv-let (e v) (a-sx (kadr x) env s st defs (1- n))
            (if e (mv e s)
              (mv-let (e s1) (a-st (kaddr x) env s st defs (1- n))
                (if e (mv e s) (mv nil (put (g-comp (car x) st) v s1)))))))
         ((eq (g-role (car x) st) :seti)
          (mv-let (e i) (a-sx (kadr x) env s st defs (1- n))
            (if e (mv e s)
              (mv-let (e v) (a-sx (kaddr x) env s st defs (1- n))
                (if e (mv e s)
                  (mv-let (e s1) (a-st (kadddr x) env s st defs (1- n))
                    (let ((p (cdr (lkp (g-comp (car x) st) s1))))
                      (cond (e (mv e s))
                            ((not (and (farrayp p) (integerp i))) (mv :type s))
                            ((not (and (<= 0 i) (< i (len (cdr p))))) (mv :bounds s))
                            (t (mv nil (put (g-comp (car x) st) (cons :array (update-nth i v (cdr p))) s1)))))))))))
         ((eq (car x) 'if)
          (mv-let (e c) (a-sx (kadr x) env s st defs (1- n))
            (cond (e (mv e s))
                  (c (a-st (kaddr x) env s st defs (1- n)))
                  (t (a-st (kadddr x) env s st defs (1- n))))))
         ((consp (car x))
          ; the arguments in the outer scope, in order; a stobj's is its update
          (mv-let (e vs s1) (a-st-args (kadr (car x)) (cdr x) env s st defs (1- n))
            (if e (mv e s)
              (a-st (kaddr (car x)) (pairlis$ (true-list-fix (kadr (car x))) vs) s1 st defs (1- n)))))
         (t (mv :stobj s))))
 (defun a-st-args (vars xs env s st defs n)
   ; (mv err vals S'): a stobj var's value is nil, the stobj being S
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (mv :fuel nil s))
         ((atom xs) (mv nil nil s))
         ((eq (g-role (kar vars) st) :stobj)
          (mv-let (e s1) (a-st (car xs) env s st defs (1- n))
            (if e (mv e nil s)
              (mv-let (e vs s2) (a-st-args (kdr vars) (cdr xs) env s1 st defs (1- n))
                (mv e (cons nil vs) s2)))))
         (t (mv-let (e v) (a-sx (car xs) env s st defs (1- n))
              (if e (mv e nil s)
                (mv-let (e vs s2) (a-st-args (kdr vars) (cdr xs) env s st defs (1- n))
                  (mv e (cons v vs) s2))))))))

; ---- the tests: fsem on g-st-module's hpg_spush against a-st on the source

(defconst *spush-mod*
  (mv-let (e ps) (g-st-module *spush-raw* nil '(hpg-spush) *heapg-st*) (list :module "m" (if e nil ps))))

; hs: err, msp, mtag, mref
(defun spush-objs (err msp mtag mref)
  (list (list "hs" (list (list "err" :scalar err) (list "msp" :scalar msp)
                         (list "mtag" :array mtag) (list "mref" :array mref)))))

(defun spush-agree (err msp mtag mref tag ref)
  (declare (xargs :mode :program))
  (let ((out (fsem-run *spush-mod* (spush-objs err msp mtag mref) nil
                       (list (list :call "hpg_spush" (list '(:var "hs") (g-lit tag) (g-lit ref)))
                             '(:print (:comp "hs" "err")) '(:print (:comp "hs" "msp"))
                             '(:print (:elem "hs" "mtag" (:int 0))) '(:print (:elem "hs" "mref" (:int 0))))
                       10000)))
    (mv-let (e s) (a-st (nth 4 (car *spush-raw*)) (list (cons 'tag tag) (cons 'ref ref))
                        (mk-comps (cadr (car (spush-objs err msp mtag mref)))) *heapg-st* nil 10000)
      (if e
          (equal out (list (list :error e)))
        (equal out (list (cdr (lkp "err" s)) (cdr (lkp "msp" s))
                         (car (cddr (lkp "mtag" s))) (car (cddr (lkp "mref" s)))))))))

(assert-event (and (spush-agree 0 0 '(9 9) '(9 9) 5 7)       ; pushed
                   (spush-agree 0 1 '(9 9) '(9 9) -5 -7)     ; pushed at 1
                   (spush-agree 0 2 '(9 9) '(9 9) 5 7)       ; full: err
                   (spush-agree 0 1 '(9 9) '(9) 5 7)         ; mref short: :bounds
                   (spush-agree 0 0 '(9) '(9) -9223372036854775808 7)))

; and the values are the pushed ones, not a shared error
(assert-event (mv-let (e s) (a-st (nth 4 (car *spush-raw*)) '((tag . 5) (ref . 7))
                                  (mk-comps (cadr (car (spush-objs 0 0 '(9 9) '(9 9))))) *heapg-st* nil 10000)
                (and (not e) (equal (lkp "msp" s) '("msp" . 1)) (equal (lkp "mtag" s) '("mtag" :array 5 9))
                     (equal (lkp "mref" s) '("mref" :array 7 9)))))
(assert-event (equal (car (mv-list 2 (a-st (nth 4 (car *spush-raw*)) '((tag . 5) (ref . 7))
                                     (mk-comps (cadr (car (spush-objs 0 1 '(9 9) '(9))))) *heapg-st* nil 10000)))
                     :bounds))
