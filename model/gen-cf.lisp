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

; Next (GEN.md, "What remains"): fx-is-f-ex, by fx-ind -- f-ex and f-ex-list
; with fuel past (acl2-count s) answer what fx and fx-list answer on cf-stmts,
; the heap unchanged. A first attempt, the openers above and f-ex disabled,
; ran past 240 s of CPU: split it by statement kind before trying again.

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
