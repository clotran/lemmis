; gen-cf: fsem on code without calls or loops, fuel-free. fv and fx are
; f-ev and f-ex with the fuel taken out, on the expressions and statements
; the translation emits for a function with no call and no loop; fsem with
; any fuel past the code's size answers what they answer (fv-is-f-ev,
; fx-is-f-ex). gen-proof.lisp reasons about fv and fx, not about fuel.

(in-package "ACL2")

(include-book "fsem")

(defun cf-expr (e)
  (declare (xargs :guard t))
  (case (kar e)
    ((:int :true :false :huge :var) t)
    ((:neg :not) (cf-expr (kadr e)))
    ((:add :sub :mul :eq :lt :le :ge :max) (and (cf-expr (kadr e)) (cf-expr (kaddr e))))
    (otherwise nil)))

(defun fv (e fr)
  (declare (xargs :guard t))
  (case (kar e)
    (:int (if (int-lit-p (kadr e)) (mv nil (kadr e)) (mv :syntax nil)))
    (:true (mv nil t))
    (:false (mv nil nil))
    (:huge (mv nil *int64-max*))
    (:var (let ((b (cdr (lkp (kadr e) fr))))
            (cond ((not (and (consp b) (member-eq (car b) '(:int64 :logical)))) (mv :type nil))
                  ((eq (cdr b) :undef) (mv :undefined nil))
                  (t (mv nil (cdr b))))))
    (:neg (mv-let (err a) (fv (kadr e) fr) (if err (mv err nil) (arith :sub 0 a))))
    (:not (mv-let (err a) (fv (kadr e) fr)
            (cond (err (mv err nil)) ((booleanp a) (mv nil (not a))) (t (mv :type nil)))))
    ((:add :sub :mul :eq :lt :le :ge :max)
     (mv-let (err a) (fv (kadr e) fr)
       (if err (mv err nil)
         (mv-let (err b) (fv (kaddr e) fr)
           (if err (mv err nil) (binop (kar e) a b))))))
    (otherwise (mv :syntax nil))))

(defun fv-ind (e k)
  (declare (xargs :measure (nfix k)))
  (if (zp k) e (list (fv-ind (kadr e) (1- k)) (fv-ind (kaddr e) (1- k)))))

(defthm count-kadr-kaddr
  (implies (consp e)
           (and (< (acl2-count (kadr e)) (acl2-count e))
                (< (acl2-count (kaddr e)) (acl2-count e))
                (< (acl2-count (kadddr e)) (acl2-count e))))
  :rule-classes :linear)

(defthm fv-is-f-ev
  (implies (and (cf-expr e) (< (acl2-count e) k) (integerp k))
           (equal (f-ev e fr heap procs k) (fv e fr)))
  :hints (("Goal" :induct (fv-ind e k) :expand ((f-ev e fr heap procs k)))))

; ---- statements: an assignment to a variable, if, select, return

(mutual-recursion
 (defun cf-stmt (s)
   (declare (xargs :guard t :measure (acl2-count s)))
   (case (kar s)
     (:assign (and (eq (kar (kadr s)) :var) (cf-expr (kaddr s))))
     (:if (and (cf-expr (kadr s)) (cf-stmts (kaddr s)) (cf-stmts (kadddr s))))
     (:select (and (cf-expr (kadr s)) (cf-arms (kaddr s)) (cf-stmts (kadddr s))))
     (:return t)
     (:cycle (equal s '(:cycle)))
     (otherwise nil)))
 (defun cf-arms (arms)
   (declare (xargs :guard t :measure (acl2-count arms)))
   (if (atom arms) t (and (cf-stmts (kadr (car arms))) (cf-arms (cdr arms)))))
 (defun cf-stmts (ss)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) t (and (cf-stmt (car ss)) (cf-stmts (cdr ss))))))

(mutual-recursion
 (defun fx (s fr)
   (declare (xargs :guard t :measure (acl2-count s)))
   (case (kar s)
     (:assign (mv-let (err v) (fv (kaddr s) fr)
                (if err (mv (errst err) fr)
                  (let ((b (cdr (lkp (kadr (kadr s)) fr))))
                    (if (and (consp b) (scalar-ok (car b) v))
                        (mv :normal (put (kadr (kadr s)) (cons (car b) v) fr))
                      (mv (errst :type) fr))))))
     (:if (mv-let (err c) (fv (kadr s) fr)
            (cond (err (mv (errst err) fr))
                  ((not (booleanp c)) (mv (errst :type) fr))
                  (c (fx-list (kaddr s) fr))
                  (t (fx-list (kadddr s) fr)))))
     (:select (mv-let (err k) (fv (kadr s) fr)
                (cond (err (mv (errst err) fr))
                      ((not (integerp k)) (mv (errst :type) fr))
                      (t (fx-arms k (kaddr s) (kadddr s) fr)))))
     (:return (mv :return fr))
     (:cycle (mv :cycle fr))
     (otherwise (mv (errst :syntax) fr))))
 (defun fx-arms (k arms dflt fr)
   ; fsem's (lkp k arms), then its statements
   (declare (xargs :guard t :measure (+ 1 (acl2-count arms) (acl2-count dflt))))
   (cond ((atom arms) (fx-list dflt fr))
         ((and (consp (car arms)) (equal (caar arms) k)) (fx-list (kadr (car arms)) fr))
         (t (fx-arms k (cdr arms) dflt fr))))
 (defun fx-list (ss fr)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) (mv :normal fr)
     (mv-let (st fr2) (fx (car ss) fr)
       (if (eq st :normal) (fx-list (cdr ss) fr2) (mv st fr2))))))



(defthm fx-arms-is-lkp
  (equal (fx-arms k arms dflt fr)
         (let ((arm (lkp k arms))) (fx-list (if arm (kadr arm) dflt) fr)))
  :hints (("Goal" :induct (len arms) :expand ((fx-arms k arms dflt fr)))))

(defthm count-lkp-arm
  (<= (acl2-count (kadr (lkp k arms))) (acl2-count arms))
  :rule-classes :linear)

(defthm cf-arms-lkp
  (implies (cf-arms arms) (cf-stmts (kadr (lkp k arms)))))

; the induction: f-ex's, with the fuel and the frame
(defun fx-ind (flag s fr k)
  (declare (xargs :measure (acl2-count s) :verify-guards nil))
  (if (or (zp k) (atom s)) (list fr k)
    (if (eq flag :stmt)
        (mv-let (err v) (fv (kadr s) fr)
          (declare (ignore err))
          (list (fx-ind :list (kaddr s) fr (1- k))
                (fx-ind :list (kadddr s) fr (1- k))
                (fx-ind :list (kadr (lkp v (kaddr s))) fr (1- k))))
      (mv-let (st fr2) (fx (car s) fr)
        (declare (ignore st))
        (list (fx-ind :stmt (car s) fr (1- k))
              (fx-ind :list (cdr s) fr2 (1- k)))))))

;; f-ex opened one statement kind at a time, so the proof below never opens
;; the whole of f-ex
(defthm f-ex-assign-var
  (implies (and (posp k) (eq (kar s) :assign) (eq (kar (kadr s)) :var))
           (equal (f-ex s fr heap procs k)
                  (mv-let (err v) (f-ev (kaddr s) fr heap procs (1- k))
                    (if err (mv (errst err) fr heap)
                      (let ((b (cdr (lkp (kadr (kadr s)) fr))))
                        (if (and (consp b) (scalar-ok (car b) v))
                            (mv :normal (put (kadr (kadr s)) (cons (car b) v) fr) heap)
                          (mv (errst :type) fr heap)))))))
  :hints (("Goal" :expand ((f-ex s fr heap procs k)))))

(defthm f-ex-if
  (implies (and (posp k) (eq (kar s) :if))
           (equal (f-ex s fr heap procs k)
                  (mv-let (err c) (f-ev (kadr s) fr heap procs (1- k))
                    (cond (err (mv (errst err) fr heap))
                          ((not (booleanp c)) (mv (errst :type) fr heap))
                          (c (f-ex-list (kaddr s) fr heap procs (1- k)))
                          (t (f-ex-list (kadddr s) fr heap procs (1- k)))))))
  :hints (("Goal" :expand ((f-ex s fr heap procs k)))))

(defthm f-ex-select
  (implies (and (posp k) (eq (kar s) :select))
           (equal (f-ex s fr heap procs k)
                  (mv-let (err key) (f-ev (kadr s) fr heap procs (1- k))
                    (cond (err (mv (errst err) fr heap))
                          ((not (integerp key)) (mv (errst :type) fr heap))
                          (t (let ((arm (lkp key (kaddr s))))
                               (f-ex-list (if arm (kadr arm) (kadddr s)) fr heap procs (1- k))))))))
  :hints (("Goal" :expand ((f-ex s fr heap procs k)))))

(defthm f-ex-return
  (implies (and (posp k) (eq (kar s) :return))
           (equal (f-ex s fr heap procs k) (mv :return fr heap)))
  :hints (("Goal" :expand ((f-ex s fr heap procs k)))))

(defthm f-ex-list-nil
  (implies (and (posp k) (atom ss)) (equal (f-ex-list ss fr heap procs k) (mv :normal fr heap)))
  :hints (("Goal" :expand ((f-ex-list ss fr heap procs k)))))

(defthm f-ex-list-open
  (implies (and (posp k) (consp ss))
           (equal (f-ex-list ss fr heap procs k)
                  (progn$
                    (mv-let (st fr2 h) (f-ex (car ss) fr heap procs (1- k))
                      (if (eq st :normal) (f-ex-list (cdr ss) fr2 h procs (1- k)) (mv st fr2 h))))))
  :hints (("Goal" :expand ((f-ex-list ss fr heap procs k)))))

;; fx-is-f-ex: f-ex and f-ex-list with fuel past (acl2-count s) answer what
;; fx and fx-list answer on cf code, the heap unchanged. One lemma per
;; statement kind, each taking its sub-lists' results as hypotheses; the
;; induction below then only dispatches.

(defun +h (r heap) (declare (xargs :guard t)) (list (mv-nth 0 r) (mv-nth 1 r) heap))

(defthm +h-list (equal (+h (list a b) heap) (list a b heap)))

(defthm cf-stmt-kinds
  (implies (cf-stmt s) (member-eq (kar s) '(:assign :if :select :return :cycle)))
  :rule-classes :forward-chaining)

(defthm cf-stmt-other
  (implies (and (not (equal (kar s) :assign)) (not (equal (kar s) :if))
                (not (equal (kar s) :select)) (not (equal (kar s) :return)) (not (equal (kar s) :cycle)))
           (not (cf-stmt s)))
  :hints (("Goal" :expand ((cf-stmt s)))))

(defthm cf-stmt-consp
  (implies (cf-stmt s) (consp s))
  :rule-classes :forward-chaining)

(defthm cf-stmts-parts
  (implies (and (cf-stmts ss) (consp ss)) (and (cf-stmt (car ss)) (cf-stmts (cdr ss)))))

(defthm cf-stmt-parts
  (implies (cf-stmt s)
           (and (implies (eq (kar s) :if) (and (cf-stmts (kaddr s)) (cf-stmts (kadddr s))))
                (implies (eq (kar s) :select)
                         (and (cf-stmts (kadddr s)) (cf-stmts (kadr (lkp k (kaddr s))))))))
  :hints (("Goal" :expand ((cf-stmt s)) :use ((:instance cf-arms-lkp (arms (kaddr s)))))))

(defthm fx-f-ex-assign
  (implies (and (cf-stmt s) (eq (kar s) :assign) (integerp k) (< (acl2-count s) k))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :in-theory (disable f-ex) :expand ((fx s fr) (cf-stmt s)))))

(defthm fx-f-ex-return
  (implies (and (eq (kar s) :return) (integerp k) (< (acl2-count s) k))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :in-theory (disable f-ex) :expand ((fx s fr)))))

(defthm fx-f-ex-cycle
  (implies (and (eq (kar s) :cycle) (integerp k) (< (acl2-count s) k))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :expand ((fx s fr) (f-ex s fr heap procs k)))))

(defthm fx-f-ex-if
  (implies (and (cf-stmt s) (eq (kar s) :if) (integerp k) (< (acl2-count s) k)
                (equal (f-ex-list (kaddr s) fr heap procs (1- k)) (+h (fx-list (kaddr s) fr) heap))
                (equal (f-ex-list (kadddr s) fr heap procs (1- k)) (+h (fx-list (kadddr s) fr) heap)))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-ex f-ex-list fx-list +h) :expand ((fx s fr) (cf-stmt s)))))

(defthm fx-f-ex-select
  (implies (and (cf-stmt s) (eq (kar s) :select) (integerp k) (< (acl2-count s) k)
                (equal (f-ex-list (kadddr s) fr heap procs (1- k)) (+h (fx-list (kadddr s) fr) heap))
                (equal (f-ex-list (kadr (lkp (mv-nth 1 (fv (kadr s) fr)) (kaddr s))) fr heap procs (1- k))
                       (+h (fx-list (kadr (lkp (mv-nth 1 (fv (kadr s) fr)) (kaddr s))) fr) heap)))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-ex f-ex-list fx-list +h) :expand ((fx s fr) (cf-stmt s)))))

(defthm fx-f-ex-list-nil
  (implies (and (atom ss) (integerp k) (< (acl2-count ss) k))
           (equal (f-ex-list ss fr heap procs k) (+h (fx-list ss fr) heap)))
  :hints (("Goal" :in-theory (disable f-ex-list) :expand ((fx-list ss fr)))))

(defthm fx-f-ex-list-cons
  (implies (and (consp ss) (integerp k) (< (acl2-count ss) k)
                (equal (f-ex (car ss) fr heap procs (1- k)) (+h (fx (car ss) fr) heap))
                (equal (f-ex-list (cdr ss) (mv-nth 1 (fx (car ss) fr)) heap procs (1- k))
                       (+h (fx-list (cdr ss) (mv-nth 1 (fx (car ss) fr))) heap)))
           (equal (f-ex-list ss fr heap procs k) (+h (fx-list ss fr) heap)))
  :hints (("Goal" :in-theory (disable f-ex f-ex-list fx) :expand ((fx-list ss fr)))))

(defthm fx-is-f-ex-flag
  (implies (and (integerp k) (< (acl2-count s) k))
           (if (eq flag :stmt)
               (implies (cf-stmt s) (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
             (implies (cf-stmts s) (equal (f-ex-list s fr heap procs k) (+h (fx-list s fr) heap)))))
  :rule-classes nil
  :hints (("Goal" :induct (fx-ind flag s fr k) :do-not-induct t
           :in-theory (disable f-ex f-ex-list fx fx-list cf-stmt cf-stmts +h
                               f-ex-assign-var f-ex-if f-ex-select f-ex-return
                               f-ex-list-nil f-ex-list-open kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select) (eq (kar s) :return)
                         (eq (kar s) :cycle))))))

(defthm fx-is-f-ex
  (implies (and (cf-stmt s) (integerp k) (< (acl2-count s) k))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :use (:instance fx-is-f-ex-flag (flag :stmt)))))

(defthm fx-list-is-f-ex-list
  (implies (and (cf-stmts ss) (integerp k) (< (acl2-count ss) k))
           (equal (f-ex-list ss fr heap procs k) (+h (fx-list ss fr) heap)))
  :hints (("Goal" :use (:instance fx-is-f-ex-flag (flag :list) (s ss)))))

; ---- sequencing

(defun app-ind (a fr)
  (if (atom a) fr
    (mv-let (st fr2) (fx (car a) fr) (declare (ignore st)) (app-ind (cdr a) fr2))))

(defthm fx-list-append
  (equal (fx-list (append a b) fr)
         (mv-let (st fr2) (fx-list a fr)
           (if (eq st :normal) (fx-list b fr2) (mv st fr2))))
  :hints (("Goal" :induct (app-ind a fr) :in-theory (disable fx)
           :expand ((fx-list a fr) (fx-list (append a b) fr)))))

(defthm cf-stmts-append
  (equal (cf-stmts (append a b)) (and (cf-stmts a) (cf-stmts b))))

; ---- what code reads and writes: an expression reads its ev-names; a
; statement list writes only its asg names, and keeps every name's type

(defun ev-names (e)
  (declare (xargs :guard t))
  (case (kar e)
    (:var (list (kadr e)))
    ((:neg :not) (ev-names (kadr e)))
    ((:add :sub :mul :eq :lt :le :ge :max) (append (ev-names (kadr e)) (ev-names (kaddr e))))
    (otherwise nil)))

(defun lkp-agree (ns fr fr2)
  (declare (xargs :guard t))
  (if (atom ns) t (and (equal (lkp (car ns) fr) (lkp (car ns) fr2)) (lkp-agree (cdr ns) fr fr2))))

(defthm lkp-agree-append
  (equal (lkp-agree (append a b) fr fr2) (and (lkp-agree a fr fr2) (lkp-agree b fr fr2))))

(defthm fv-agree
  (implies (lkp-agree (ev-names e) fr fr2) (equal (fv e fr2) (fv e fr)))
  :hints (("Goal" :induct (fv e fr) :in-theory (disable binop arith))))

; flag :list a statement list, :arms a select's arms
(defun asg (flag x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (cond ((atom x) nil)
        ((eq flag :arms) (append (asg :list (kadr (car x))) (asg :arms (cdr x))))
        (t (append (let ((s (car x)))
                     (case (kar s)
                       (:assign (list (kadr (kadr s))))
                       (:if (append (asg :list (kaddr s)) (asg :list (kadddr s))))
                       (:select (append (asg :arms (kaddr s)) (asg :list (kadddr s))))
                       (otherwise nil)))
                   (asg :list (cdr x))))))

(defthm member-app
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))

(defthm app-assoc (equal (append (append a b) c) (append a (append b c))))

(defthm asg-append
  (equal (asg :list (append a b)) (append (asg :list a) (asg :list b)))
  :hints (("Goal" :induct (len a) :expand ((asg :list (append a b)) (asg :list a)))))

(defthm asg-lkp-arm
  (implies (not (member-equal n (asg :arms arms))) (not (member-equal n (asg :list (kadr (lkp k arms))))))
  :hints (("Goal" :induct (len arms) :expand ((lkp k arms) (asg :arms arms)))))

(defthm lkp-put
  (equal (lkp n (put k v fr)) (if (equal n k) (cons k v) (lkp n fr))))

(defun asg-ind (flag s fr)
  (declare (xargs :measure (acl2-count s) :verify-guards nil))
  (if (atom s) fr
    (if (eq flag :stmt)
        (mv-let (err v) (fv (kadr s) fr)
          (declare (ignore err))
          (list (asg-ind :list (kaddr s) fr) (asg-ind :list (kadddr s) fr)
                (asg-ind :list (kadr (lkp v (kaddr s))) fr)))
      (mv-let (st fr2) (fx (car s) fr)
        (declare (ignore st))
        (list (asg-ind :stmt (car s) fr) (asg-ind :list (cdr s) fr2))))))

(defun dty (n fr) (declare (xargs :guard t)) (let ((b (cdr (lkp n fr)))) (if (consp b) (list (car b)) nil)))

(defthm dty-put
  (equal (dty n (put k v fr)) (if (equal n k) (if (consp v) (list (car v)) nil) (dty n fr))))

(defthm asg-cons
  (implies (syntaxp (not (equal b ''nil)))
           (equal (asg :list (cons a b)) (append (asg :list (list a)) (asg :list b))))
  :hints (("Goal" :expand ((asg :list (cons a b)) (asg :list (list a)) (asg :list b)))))

(defun kp-stmt (n s fr)
  (mv-let (st fr2) (fx s fr)
    (declare (ignore st))
    (and (implies (not (member-equal n (asg :list (list s)))) (equal (lkp n fr2) (lkp n fr)))
         (equal (dty n fr2) (dty n fr)))))

(defun kp-list (n ss fr)
  (mv-let (st fr2) (fx-list ss fr)
    (declare (ignore st))
    (and (implies (not (member-equal n (asg :list ss))) (equal (lkp n fr2) (lkp n fr)))
         (equal (dty n fr2) (dty n fr)))))

(defthm kp-assign
  (implies (eq (kar s) :assign) (kp-stmt n s fr))
  :hints (("Goal" :expand ((fx s fr) (asg :list (list s))))))

(defthm kp-if
  (implies (and (eq (kar s) :if) (kp-list n (kaddr s) fr) (kp-list n (kadddr s) fr))
           (kp-stmt n s fr))
  :hints (("Goal" :in-theory (disable dty fx-list) :expand ((fx s fr) (asg :list (list s))))))

(defthm kp-select
  (implies (and (eq (kar s) :select) (kp-list n (kadddr s) fr)
                (kp-list n (kadr (lkp (mv-nth 1 (fv (kadr s) fr)) (kaddr s))) fr))
           (kp-stmt n s fr))
  :hints (("Goal" :in-theory (disable dty fx-list) :expand ((fx s fr) (asg :list (list s)))
           :use ((:instance asg-lkp-arm (k (mv-nth 1 (fv (kadr s) fr))) (arms (kaddr s)))))))

(defthm kp-other
  (implies (not (member-equal (kar s) '(:assign :if :select))) (kp-stmt n s fr))
  :hints (("Goal" :in-theory (disable dty) :expand ((fx s fr)))))

(defthm kp-nil
  (implies (atom ss) (kp-list n ss fr))
  :hints (("Goal" :expand ((fx-list ss fr)))))

(defthm kp-cons
  (implies (and (consp ss) (kp-stmt n (car ss) fr) (kp-list n (cdr ss) (mv-nth 1 (fx (car ss) fr))))
           (kp-list n ss fr))
  :hints (("Goal" :in-theory (disable dty fx) :expand ((fx-list ss fr) (asg :list ss)))))

(defthm kar-atom (implies (atom x) (equal (kar x) nil)))

(defthm kp-flag
  (if (eq flag :stmt) (kp-stmt n s fr) (kp-list n s fr))
  :rule-classes nil
  :hints (("Goal" :induct (asg-ind flag s fr) :do-not-induct t
           :in-theory (disable kp-stmt kp-list fx fx-list kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select))))))

(defthm fx-list-keeps
  (and (implies (not (member-equal n (asg :list s)))
                (equal (lkp n (mv-nth 1 (fx-list s fr))) (lkp n fr)))
       (equal (dty n (mv-nth 1 (fx-list s fr))) (dty n fr)))
  :hints (("Goal" :use (:instance kp-flag (flag :list)))))

(defun lkp-agree-ind (ns) (if (atom ns) ns (lkp-agree-ind (cdr ns))))

(defthm fx-list-agree
  (implies (not (intersectp-equal ns (asg :list s)))
           (lkp-agree ns fr (mv-nth 1 (fx-list s fr))))
  :hints (("Goal" :induct (lkp-agree-ind ns))))
