; gen-callarg: layer 3, f-bind of argument expressions (GEN.md). g-fn-sem
; binds literals (g-lits); a call in generated code passes expressions. A
; function g-fn makes has only VALUE dummies (g-dummies), so f-bind reads
; each argument's value and nothing else of the caller: when the argument
; expressions answer int64 values ks at the fuels f-bind evaluates them at
; (args-at), f-invoke on them is f-invoke on (g-lits ks), from any caller.

(in-package "ACL2")

(include-book "gen-fn")
(include-book "gen-call")

; each argument answers its value at the fuel f-bind gives it: the i-th
; (from 0) at fuel - 1 - i
(defun args-at (as caller heap procs fuel ks)
  (if (atom as) (and (atom ks) (posp fuel))
    (and (consp ks) (posp fuel)
         (mv-let (e v) (f-ev (car as) caller heap procs (1- fuel)) (and (not e) (equal v (car ks))))
         (int64p (car ks))
         (args-at (cdr as) caller heap procs (1- fuel) (cdr ks)))))

(defun fbi-as (vs as ks fr fuel)
  (if (atom vs) (list as ks fr fuel)
    (fbi-as (cdr vs) (cdr as) (cdr ks) (put (g-formal (car vs)) (cons :int64 (car ks)) fr) (1- fuel))))

(defthm f-bind-g-dummies-args
  (implies (and (args-at as caller heap procs fuel ks) (equal (len ks) (len vs)))
           (equal (f-bind (g-dummies vs) as caller callee outs heap procs fuel)
                  (mv nil (fb vs ks callee) outs)))
  :hints (("Goal" :induct (fbi-as vs as ks callee fuel) :in-theory (disable f-ev put g-formal)
           :expand ((fb vs ks callee) (f-bind nil as caller callee outs heap procs fuel)
                    (f-bind (g-dummies vs) as caller callee outs heap procs fuel)
                    (f-bind (cons (list (g-formal (car vs)) :value :int64) (g-dummies (cdr vs)))
                            as caller callee outs heap procs fuel)))))

(defthm f-invoke-args
  (implies (and (equal (kar p) :function) (equal (nth 4 (true-list-fix p)) (g-dummies vs))
                (args-at as caller heap procs (1- fuel) ks)
                (int64-listp ks) (equal (len ks) (len vs)) (integerp fuel) (< (+ 5 (len vs)) fuel))
           (equal (f-invoke p as caller heap procs fuel)
                  (f-invoke p (g-lits ks) caller2 heap procs fuel)))
  :hints (("Goal" :in-theory (disable f-bind f-ex-list f-bind-g-dummies-args f-bind-g-dummies g-dummies g-lits fb)
           :expand ((f-invoke p as caller heap procs fuel) (f-invoke p (g-lits ks) caller2 heap procs fuel))
           :use ((:instance f-bind-g-dummies-args (fuel (1- fuel)) (callee nil) (outs nil))
                 (:instance f-bind-g-dummies (fuel (1- fuel)) (caller caller2) (callee nil) (outs nil))))))
