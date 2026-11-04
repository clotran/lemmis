; gen-call: layer 3's first piece. With calls, an expression's value still
; depends on the frame only through the names it reads: a call's callee
; frame is built from the argument values alone (f-bind), so two caller
; frames agreeing on the names an expression reads give it the same value,
; at every fuel (ag-ok-thm, over fsem's clique: f-ev, f-bind, f-invoke).
; This is what keeps a value computed before a temporary's assignment.

(in-package "ACL2")

(include-book "gen-cf")

(set-irrelevant-formals-ok t)

; the expressions g-expr makes: cf-expr's, and function calls of them
(defun ce-ok (flag e)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flag :list) (if (atom e) t (and (ce-ok :one (car e)) (ce-ok :list (cdr e))))
    (case (kar e)
      ((:int :true :false :huge :var) t)
      ((:neg :not) (ce-ok :one (kadr e)))
      ((:add :sub :mul :eq :lt :le :ge :max) (and (ce-ok :one (kadr e)) (ce-ok :one (kaddr e))))
      (:fcall (ce-ok :list (kaddr e)))
      (otherwise nil))))

(defun ce-names (flag e)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flag :list) (if (atom e) nil (append (ce-names :one (car e)) (ce-names :list (cdr e))))
    (case (kar e)
      (:var (list (kadr e)))
      ((:neg :not) (ce-names :one (kadr e)))
      ((:add :sub :mul :eq :lt :le :ge :max) (append (ce-names :one (kadr e)) (ce-names :one (kaddr e))))
      (:fcall (ce-names :list (kaddr e)))
      (otherwise nil))))

(defun-nx ag-ok (flag x d callee outs fr fr2 heap procs fuel)
  (case flag
    (:ev (implies (and (ce-ok :one x) (lkp-agree (ce-names :one x) fr fr2))
                  (equal (f-ev x fr heap procs fuel) (f-ev x fr2 heap procs fuel))))
    (:bind (implies (and (ce-ok :list x) (lkp-agree (ce-names :list x) fr fr2))
                    (equal (f-bind d x fr callee outs heap procs fuel) (f-bind d x fr2 callee outs heap procs fuel))))
    (otherwise (implies (and (eq (kar d) :function) (ce-ok :list x) (lkp-agree (ce-names :list x) fr fr2))
                        (equal (f-invoke d x fr heap procs fuel) (f-invoke d x fr2 heap procs fuel))))))

(defun-nx ag-ind (flag x d callee outs fr fr2 heap procs fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) nil
    (case flag
      (:ev (list (ag-ind :ev (kadr x) d callee outs fr fr2 heap procs (1- fuel))
                 (ag-ind :ev (kaddr x) d callee outs fr fr2 heap procs (1- fuel))
                 (ag-ind :invoke (kaddr x) (find-proc (kadr x) procs) callee outs fr fr2 heap procs (1- fuel))))
      (:bind (list (ag-ind :ev (car x) d callee outs fr fr2 heap procs (1- fuel))
                   (ag-ind :bind (cdr x) (cdr d)
                           (put (kar (car d)) (cons :int64 (mv-nth 1 (f-ev (car x) fr heap procs (1- fuel)))) callee)
                           outs fr fr2 heap procs (1- fuel))
                   (ag-ind :bind (cdr x) (cdr d)
                           (put (kar (car d)) (list* :obj (kadr (car d)) (mv-nth 1 (obj-of (kadr (car x)) fr))) callee)
                           outs fr fr2 heap procs (1- fuel))
                   (ag-ind :bind (cdr x) (cdr d) (put (kar (car d)) (cons :int64 :undef) callee)
                           (cons (cons (kar (car d)) (kadr (car x))) outs) fr fr2 heap procs (1- fuel))))
      (otherwise (ag-ind :bind x (nth 4 (true-list-fix d)) nil nil fr fr2 heap procs (1- fuel))))))

(defthm lkp-agree-ce-list
  (implies (consp x)
           (equal (lkp-agree (ce-names :list x) fr fr2)
                  (and (lkp-agree (ce-names :one (car x)) fr fr2) (lkp-agree (ce-names :list (cdr x)) fr fr2)))))

(in-theory (disable f-ev f-bind f-invoke f-ex f-ex-list))

(defthm ag-ev-case
  (implies (and (not (zp fuel))
                (ag-ok :ev (kadr x) d callee outs fr fr2 heap procs (1- fuel))
                (ag-ok :ev (kaddr x) d callee outs fr fr2 heap procs (1- fuel))
                (ag-ok :invoke (kaddr x) (find-proc (kadr x) procs) callee outs fr fr2 heap procs (1- fuel)))
           (ag-ok :ev x d0 callee0 outs0 fr fr2 heap procs fuel))
  :hints (("Goal" :do-not-induct t
           :expand ((f-ev x fr heap procs fuel) (f-ev x fr2 heap procs fuel) (ce-ok :one x) (ce-names :one x)))))

(defthm ag-bind-case
  (implies (and (not (zp fuel))
                (ag-ok :ev (car x) d callee outs fr fr2 heap procs (1- fuel))
                (ag-ok :bind (cdr x) (cdr d)
                       (put (kar (car d)) (cons :int64 (mv-nth 1 (f-ev (car x) fr heap procs (1- fuel)))) callee)
                       outs fr fr2 heap procs (1- fuel))
                (ag-ok :bind (cdr x) (cdr d)
                       (put (kar (car d)) (list* :obj (kadr (car d)) (mv-nth 1 (obj-of (kadr (car x)) fr))) callee)
                       outs fr fr2 heap procs (1- fuel))
                (ag-ok :bind (cdr x) (cdr d) (put (kar (car d)) (cons :int64 :undef) callee)
                       (cons (cons (kar (car d)) (kadr (car x))) outs) fr fr2 heap procs (1- fuel)))
           (ag-ok :bind x d callee outs fr fr2 heap procs fuel))
  :hints (("Goal" :do-not-induct t :in-theory (disable put)
           :expand ((f-bind d x fr callee outs heap procs fuel) (f-bind d x fr2 callee outs heap procs fuel)
                    (ce-ok :list x) (ce-names :list x) (ce-names :one (car x)) (ce-ok :one (car x))))))

(defthm ag-invoke-case
  (implies (and (not (zp fuel))
                (ag-ok :bind x (nth 4 (true-list-fix d)) nil nil fr fr2 heap procs (1- fuel)))
           (ag-ok :invoke x d callee outs fr fr2 heap procs fuel))
  :hints (("Goal" :do-not-induct t
           :expand ((f-invoke d x fr heap procs fuel) (f-invoke d x fr2 heap procs fuel)))))

(defthm ag-zp-case
  (implies (zp fuel) (ag-ok flag x d callee outs fr fr2 heap procs fuel))
  :hints (("Goal" :expand ((f-ev x fr heap procs fuel) (f-ev x fr2 heap procs fuel)
                           (f-bind d x fr callee outs heap procs fuel) (f-bind d x fr2 callee outs heap procs fuel)
                           (f-invoke d x fr heap procs fuel) (f-invoke d x fr2 heap procs fuel)))))

(defthm ag-ok-flag
  (implies (and (syntaxp (not (equal flag '':invoke))) (not (equal flag :ev)) (not (equal flag :bind)))
           (equal (ag-ok flag x d callee outs fr fr2 heap procs fuel) (ag-ok :invoke x d callee outs fr fr2 heap procs fuel)))
  :hints (("Goal" :in-theory (disable f-ev f-bind f-invoke))))

(in-theory (disable ag-ok))

(defthm ag-ok-thm
  (ag-ok flag x d callee outs fr fr2 heap procs fuel)
  :rule-classes nil
  :hints (("Goal" :induct (ag-ind flag x d callee outs fr fr2 heap procs fuel) :do-not-induct t
           :in-theory (disable kar kadr kaddr kadddr put obj-of))))

(defthm f-ev-agree
  (implies (and (ce-ok :one x) (lkp-agree (ce-names :one x) fr fr2))
           (equal (f-ev x fr2 heap procs fuel) (f-ev x fr heap procs fuel)))
  :hints (("Goal" :use (:instance ag-ok-thm (flag :ev)) :in-theory (enable ag-ok))))
