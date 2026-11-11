; gen-callev: layer 3, fuel out of the way with calls (GEN.md, calls (b)).
; fv answers a call by the oracle f-call-val (gen-cf). Under p-orc -- "the
; oracle is what the procedures answer": wherever f-call-val answers a value
; on the values the arguments evaluate to, f-ev of the call answers it at
; any fuel past b -- f-ev with fuel past (3 + b) * size is fv on ce-ok
; expressions (fv-is-f-ev-c), and f-ex is fx on statements of them
; (fx-is-f-ex-c), whenever fv (fx) answers no error.

(in-package "ACL2")

(include-book "gen-call")

; the arguments answer ks at the fuels f-bind evaluates them at: the i-th
; (from 0) at fuel - 1 - i (gen-callarg's args-at without the int64 check)
(defun evs-at (as fr heap procs fuel ks)
  (if (atom as) (and (atom ks) (posp fuel))
    (and (consp ks) (posp fuel)
         (mv-let (e v) (f-ev (car as) fr heap procs (1- fuel)) (and (not e) (equal v (car ks))))
         (evs-at (cdr as) fr heap procs (1- fuel) (cdr ks)))))

; the oracle is what the procedures answer, at any fuel past b
(defun-sk p-orc (procs heap b)
  (forall (x fr ks fuel)
    (implies (and (eq (kar x) :fcall) (not (mv-nth 0 (f-call-val (kadr x) ks)))
                  (evs-at (kaddr x) fr heap procs (- fuel 2) ks) (integerp fuel) (< b fuel))
             (equal (f-ev x fr heap procs fuel) (mv nil (mv-nth 1 (f-call-val (kadr x) ks)))))))

(in-theory (disable p-orc))

; the fuel: a part's bound plus 3 + b is within the whole's
(defthm fcb-sub
  (implies (and (consp e) (natp b))
           (and (<= (+ 3 b (* (+ 3 b) (acl2-count (kadr e)))) (* (+ 3 b) (acl2-count e)))
                (<= (+ 3 b (* (+ 3 b) (acl2-count (kaddr e)))) (* (+ 3 b) (acl2-count e)))
                (<= (+ 3 b (* (+ 3 b) (acl2-count (kadddr e)))) (* (+ 3 b) (acl2-count e)))
                (<= (+ 3 b (* (+ 3 b) (acl2-count (car e)))) (* (+ 3 b) (acl2-count e)))
                (<= (+ 3 b (* (+ 3 b) (acl2-count (cdr e)))) (* (+ 3 b) (acl2-count e)))))
  :rule-classes :linear
  :hints (("Goal" :nonlinearp t :use count-kadr-kaddr)))

(defthm fcb-nonneg
  (implies (natp b) (<= 0 (* (+ 3 b) (acl2-count e))))
  :rule-classes :linear)

(defun fvc-ind (flag e k)
  (declare (xargs :measure (acl2-count e)))
  (if (atom e) k
    (if (eq flag :list)
        (list (fvc-ind :one (car e) (1- k)) (fvc-ind :list (cdr e) (1- k)))
      (list (fvc-ind :one (kadr e) (1- k)) (fvc-ind :one (kaddr e) (1- k)) (fvc-ind :list (kaddr e) (- k 2))))))

(defmacro fvc-hyps () '(and (p-orc procs heap b) (natp b) (integerp k) (< (* (+ 3 b) (acl2-count e)) k)))

(defthm fv-fcall-open
  (implies (equal (kar e) :fcall)
           (equal (fv e fr)
                  (mv-let (err vs) (fv-list (kaddr e) fr)
                    (if err (mv err nil)
                      (mv-let (err v) (f-call-val (kadr e) vs) (if err (mv err nil) (mv nil v)))))))
  :hints (("Goal" :expand ((fv e fr)))))

(defthm fv-fcall-noerr
  (implies (and (consp e) (equal (car e) :fcall) (not (car (fv e fr))))
           (and (not (car (fv-list (caddr e) fr)))
                (not (car (f-call-val (cadr e) (mv-nth 1 (fv-list (caddr e) fr)))))))
  :hints (("Goal" :expand ((fv e fr)))))

(defthm fv-is-f-ev-c-fcall
  (implies (and (equal (kar e) :fcall) (fvc-hyps) (not (mv-nth 0 (fv e fr)))
                (evs-at (kaddr e) fr heap procs (- k 2) (mv-nth 1 (fv-list (kaddr e) fr))))
           (equal (f-ev e fr heap procs k) (fv e fr)))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-ev fv-list evs-at)
           :use (:instance p-orc-necc (x e) (ks (mv-nth 1 (fv-list (kaddr e) fr))) (fuel k)))))

(defthm fv-is-f-ev-c-other
  (implies (and (ce-ok :one e) (not (equal (kar e) :fcall)) (integerp k) (< 0 k) (not (mv-nth 0 (fv e fr)))
                (implies (and (ce-ok :one (kadr e)) (not (mv-nth 0 (fv (kadr e) fr))))
                         (equal (f-ev (kadr e) fr heap procs (1- k)) (fv (kadr e) fr)))
                (implies (and (ce-ok :one (kaddr e)) (not (mv-nth 0 (fv (kaddr e) fr))))
                         (equal (f-ev (kaddr e) fr heap procs (1- k)) (fv (kaddr e) fr))))
           (equal (f-ev e fr heap procs k) (fv e fr)))
  :hints (("Goal" :do-not-induct t :in-theory (disable fv-fcall-open binop arith)
           :expand ((ce-ok :one e) (fv e fr) (f-ev e fr heap procs k)))))

(defthm evs-at-cons
  (implies (and (consp as) (posp k) (not (car (f-ev (car as) fr heap procs (1- k))))
                (equal (mv-nth 1 (f-ev (car as) fr heap procs (1- k))) v)
                (evs-at (cdr as) fr heap procs (1- k) vs))
           (evs-at as fr heap procs k (cons v vs))))

(defthm fv-list-parts
  (implies (and (consp es) (not (car (fv-list es fr))))
           (and (not (car (fv (car es) fr))) (not (car (fv-list (cdr es) fr)))
                (equal (mv-nth 1 (fv-list es fr)) (cons (mv-nth 1 (fv (car es) fr)) (mv-nth 1 (fv-list (cdr es) fr))))))
  :hints (("Goal" :expand ((fv-list es fr)))))

(defthm fv-list-atom
  (implies (atom es) (equal (fv-list es fr) (mv nil nil)))
  :hints (("Goal" :expand ((fv-list es fr)))))

(defthm ce-ok-list-parts
  (implies (and (consp es) (ce-ok :list es)) (and (ce-ok :one (car es)) (ce-ok :list (cdr es)))))

(defthm fv-is-f-ev-c-flag
  (if (eq flag :list)
      (implies (and (ce-ok :list e) (fvc-hyps) (not (mv-nth 0 (fv-list e fr))))
               (evs-at e fr heap procs k (mv-nth 1 (fv-list e fr))))
    (implies (and (ce-ok :one e) (fvc-hyps) (not (mv-nth 0 (fv e fr))))
             (equal (f-ev e fr heap procs k) (fv e fr))))
  :rule-classes nil
  :hints (("Goal" :induct (fvc-ind flag e k) :do-not-induct t
           :in-theory (disable f-ev fv fv-list evs-at ce-ok fv-fcall-open)
           :expand ((evs-at e fr heap procs k nil) (ce-ok :one e)))))

(defthm fv-is-f-ev-c
  (implies (and (ce-ok :one e) (fvc-hyps) (not (mv-nth 0 (fv e fr))))
           (equal (f-ev e fr heap procs k) (fv e fr)))
  :hints (("Goal" :use (:instance fv-is-f-ev-c-flag (flag :one)))))

; ---- statements of ce-ok expressions: f-ex is fx when fx answers no error

(mutual-recursion
 (defun cc-stmt (s)
   (declare (xargs :measure (acl2-count s)))
   (case (kar s)
     (:assign (and (eq (kar (kadr s)) :var) (ce-ok :one (kaddr s))))
     (:if (and (ce-ok :one (kadr s)) (cc-stmts (kaddr s)) (cc-stmts (kadddr s))))
     (:select (and (ce-ok :one (kadr s)) (cc-arms (kaddr s)) (cc-stmts (kadddr s))))
     (:return t)
     (:cycle (equal s '(:cycle)))
     (otherwise nil)))
 (defun cc-arms (arms)
   (declare (xargs :measure (acl2-count arms)))
   (if (atom arms) t (and (cc-stmts (kadr (car arms))) (cc-arms (cdr arms)))))
 (defun cc-stmts (ss)
   (declare (xargs :measure (acl2-count ss)))
   (if (atom ss) t (and (cc-stmt (car ss)) (cc-stmts (cdr ss))))))

(defthm cc-arms-lkp (implies (cc-arms arms) (cc-stmts (kadr (lkp k arms)))))

(defthm cc-stmts-parts
  (implies (and (cc-stmts ss) (consp ss)) (and (cc-stmt (car ss)) (cc-stmts (cdr ss)))))

(defthm cc-stmt-parts
  (implies (cc-stmt s)
           (and (implies (eq (kar s) :if) (and (ce-ok :one (kadr s)) (cc-stmts (kaddr s)) (cc-stmts (kadddr s))))
                (implies (eq (kar s) :select)
                         (and (ce-ok :one (kadr s)) (cc-stmts (kadddr s)) (cc-stmts (kadr (lkp k (kaddr s))))))
                (implies (eq (kar s) :assign) (and (eq (kar (kadr s)) :var) (ce-ok :one (kaddr s))))
                (member-eq (kar s) '(:assign :if :select :return :cycle))))
  :hints (("Goal" :expand ((cc-stmt s)) :use ((:instance cc-arms-lkp (arms (kaddr s)))))))

(defthm cc-stmt-other
  (implies (and (not (equal (kar s) :assign)) (not (equal (kar s) :if))
                (not (equal (kar s) :select)) (not (equal (kar s) :return)) (not (equal (kar s) :cycle)))
           (not (cc-stmt s)))
  :hints (("Goal" :expand ((cc-stmt s)))))

(defthm fcb-mono
  (implies (and (natp b) (natp x) (natp y) (< x y)) (<= (+ 3 b (* (+ 3 b) x)) (* (+ 3 b) y)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm fcb-lkp
  (implies (and (consp s) (natp b))
           (<= (+ 3 b (* (+ 3 b) (acl2-count (kadr (lkp k (kaddr s)))))) (* (+ 3 b) (acl2-count s))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fcb-sub count-kadr-kaddr count-lkp-arm lkp kadr kaddr acl2-count)
           :use ((:instance count-kadr-kaddr (e s)) (:instance count-lkp-arm (arms (kaddr s)))
                 (:instance fcb-mono (x (acl2-count (kadr (lkp k (kaddr s))))) (y (acl2-count s)))))))

(defmacro fxc-hyps () '(and (p-orc procs heap b) (natp b) (integerp k) (< (* (+ 3 b) (acl2-count s)) k)))
(defmacro ok-st (x) `(not (errstp (car ,x))))

(defthm fv-err-fx
  (and (implies (and (equal (kar s) :assign) (mv-nth 0 (fv (kaddr s) fr))) (errstp (car (fx s fr))))
       (implies (and (member-equal (kar s) '(:if :select)) (mv-nth 0 (fv (kadr s) fr))) (errstp (car (fx s fr)))))
  :hints (("Goal" :expand ((fx s fr)))))

(defthm fxc-assign
  (implies (and (cc-stmt s) (eq (kar s) :assign) (fxc-hyps) (ok-st (fx s fr)))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :in-theory (disable f-ex fv-err-fx) :use fv-err-fx :expand ((fx s fr)))))

(defthm fxc-if
  (implies (and (cc-stmt s) (eq (kar s) :if) (fxc-hyps) (ok-st (fx s fr))
                (implies (ok-st (fx-list (kaddr s) fr))
                         (equal (f-ex-list (kaddr s) fr heap procs (1- k)) (+h (fx-list (kaddr s) fr) heap)))
                (implies (ok-st (fx-list (kadddr s) fr))
                         (equal (f-ex-list (kadddr s) fr heap procs (1- k)) (+h (fx-list (kadddr s) fr) heap))))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-ex f-ex-list fx-list +h fv-err-fx) :use fv-err-fx
           :expand ((fx s fr)))))

(defthm fxc-select
  (implies (and (cc-stmt s) (eq (kar s) :select) (fxc-hyps) (ok-st (fx s fr))
                (implies (ok-st (fx-list (kadddr s) fr))
                         (equal (f-ex-list (kadddr s) fr heap procs (1- k)) (+h (fx-list (kadddr s) fr) heap)))
                (implies (ok-st (fx-list (kadr (lkp (mv-nth 1 (fv (kadr s) fr)) (kaddr s))) fr))
                         (equal (f-ex-list (kadr (lkp (mv-nth 1 (fv (kadr s) fr)) (kaddr s))) fr heap procs (1- k))
                                (+h (fx-list (kadr (lkp (mv-nth 1 (fv (kadr s) fr)) (kaddr s))) fr) heap))))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-ex f-ex-list fx-list +h fv-err-fx) :use fv-err-fx
           :expand ((fx s fr)))))

(defthm fxc-list-cons
  (implies (and (consp ss) (integerp k) (< 0 k) (ok-st (fx-list ss fr))
                (implies (ok-st (fx (car ss) fr))
                         (equal (f-ex (car ss) fr heap procs (1- k)) (+h (fx (car ss) fr) heap)))
                (implies (ok-st (fx-list (cdr ss) (mv-nth 1 (fx (car ss) fr))))
                         (equal (f-ex-list (cdr ss) (mv-nth 1 (fx (car ss) fr)) heap procs (1- k))
                                (+h (fx-list (cdr ss) (mv-nth 1 (fx (car ss) fr))) heap))))
           (equal (f-ex-list ss fr heap procs k) (+h (fx-list ss fr) heap)))
  :hints (("Goal" :in-theory (disable f-ex f-ex-list fx) :expand ((fx-list ss fr)))))

(defthm fx-list-atom (implies (atom ss) (equal (fx-list ss fr) (list :normal fr)))
  :hints (("Goal" :expand ((fx-list ss fr)))))

(defthm fx-is-f-ex-c-flag
  (implies (fxc-hyps)
           (if (eq flag :stmt)
               (implies (and (cc-stmt s) (ok-st (fx s fr))) (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
             (implies (and (cc-stmts s) (ok-st (fx-list s fr)))
                      (equal (f-ex-list s fr heap procs k) (+h (fx-list s fr) heap)))))
  :rule-classes nil
  :hints (("Goal" :induct (fx-ind flag s fr k) :do-not-induct t
           :in-theory (disable f-ex f-ex-list fx fx-list cc-stmt cc-stmts +h errstp
                               f-ex-assign-var f-ex-if f-ex-select f-ex-return
                               f-ex-list-open kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select) (eq (kar s) :return)
                         (eq (kar s) :cycle))))))

(defthm fx-is-f-ex-c
  (implies (and (cc-stmt s) (fxc-hyps) (ok-st (fx s fr)))
           (equal (f-ex s fr heap procs k) (+h (fx s fr) heap)))
  :hints (("Goal" :use (:instance fx-is-f-ex-c-flag (flag :stmt)))))

(defthm fx-list-is-f-ex-list-c
  (implies (and (cc-stmts s) (fxc-hyps) (ok-st (fx-list s fr)))
           (equal (f-ex-list s fr heap procs k) (+h (fx-list s fr) heap)))
  :hints (("Goal" :use (:instance fx-is-f-ex-c-flag (flag :list)))))
