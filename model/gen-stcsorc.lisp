; gen-stcsorc: g-st-fn-sem from the caller's side (GEN.md 4 (4a) (iii), first
; piece). g-st-fn-sem invokes the generated subroutine on literals; a caller's
; CALL passes argument codes cs. Here the CALL statement itself, from any
; caller frame: when the codes answer int64 ks by sv (svs-is, as c-sorc
; states them), f-ex of `CALL f(ob, cs)` at fuel past the codes' and the
; body's size answers :normal, the caller's frame unchanged, the heap's key
; put to a-st's S'. This is what c-sorc and p-sorc ask of a generated
; subroutine with one stobj answering itself (no OUT results: those need
; g-stmt's cons case, not yet in gst-sem).

(in-package "ACL2")

(include-book "gen-stfn")
(include-book "gen-stcallst")

(defthm int64-listp-int64s (implies (int64-listp ks) (int64s ks)))

; f-bind of the value dummies on codes answering ks
(defun fbc (vs cs ks fr fuel)
  (if (atom vs) (list cs ks fr fuel)
    (fbc (cdr vs) (cdr cs) (cdr ks) (put (g-formal (car vs)) (cons :int64 (car ks)) fr) (1- fuel))))

(defthm f-bind-g-dummies-codes
  (implies (and (svs-is cs ks caller heap) (int64s ks) (equal (len ks) (len vs))
                (integerp fuel) (< (+ 1 (len vs) (acl2-count cs)) fuel))
           (equal (f-bind (g-dummies vs) cs caller callee outs heap procs fuel)
                  (mv nil (fb vs ks callee) outs)))
  :hints (("Goal" :induct (fbc vs cs ks callee fuel) :in-theory (disable f-ev put g-formal sv)
           :expand ((f-bind (g-dummies vs) cs caller callee outs heap procs fuel) (fb vs ks callee) (svs-is cs ks caller heap)))))

; f-invoke of a subroutine depends on its arguments only through f-bind
(defthm f-invoke-same-bind
  (implies (and (equal (kar p) :subroutine) (posp fuel)
                (equal (f-bind (nth 3 (true-list-fix p)) a1 caller nil nil heap procs (1- fuel))
                       (f-bind (nth 3 (true-list-fix p)) a2 caller nil nil heap procs (1- fuel))))
           (equal (f-invoke p a1 caller heap procs fuel) (f-invoke p a2 caller heap procs fuel)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable f-bind f-ex-list undef-locals copy-out errstp)
           :expand ((f-invoke p a1 caller heap procs fuel) (f-invoke p a2 caller heap procs fuel)))))

(defthm f-bind-cons-codes
  (implies (and (svs-is cs ks caller heap) (int64-listp ks) (equal (len ks) (len vs))
                (integerp fuel) (< (+ 6 (len vs) (acl2-count cs)) fuel))
           (equal (f-bind (cons d (g-dummies vs)) (cons a cs) caller callee outs heap procs fuel)
                  (f-bind (cons d (g-dummies vs)) (cons a (g-lits ks)) caller callee outs heap procs fuel)))
  :hints (("Goal" :in-theory (disable f-ev obj-of put g-dummies g-lits fb svs-is)
           :expand ((f-bind (cons d (g-dummies vs)) (cons a cs) caller callee outs heap procs fuel)
                    (f-bind (cons d (g-dummies vs)) (cons a (g-lits ks)) caller callee outs heap procs fuel)))))

(defthm f-invoke-st-codes
  (implies (and (equal (kar p) :subroutine) (equal (nth 3 (true-list-fix p)) (cons d (g-dummies vs)))
                (svs-is cs ks caller heap) (int64-listp ks) (equal (len ks) (len vs))
                (integerp fuel) (< (+ 8 (len vs) (acl2-count cs)) fuel))
           (equal (f-invoke p (cons a cs) caller heap procs fuel)
                  (f-invoke p (cons a (g-lits ks)) caller heap procs fuel)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable f-bind f-invoke g-dummies g-lits svs-is f-bind-cons-codes)
           :use ((:instance f-invoke-same-bind (a1 (cons a cs)) (a2 (cons a (g-lits ks))))
                 (:instance f-bind-cons-codes (fuel (1- fuel)) (callee nil) (outs nil))))))

;  the generated subroutine's head and dummies
(defthm gfn-sub-shape
  (implies (and (not (mv-nth 0 (gfn))) sv (eq (g-role sv st) :stobj))
           (and (equal (kar (mv-nth 1 (gfn))) :subroutine)
                (equal (nth 3 (true-list-fix (mv-nth 1 (gfn))))
                       (append (g-st-dummies formals (list sv) st) (g-dummies (g-st-vals formals st))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable g-st-fn g-stmt g-reaches g-called g-fcalls g-ccalls g-has g-st-dummies g-dummies
                                      g-locals g-em g-formals g-st-vals g-role g-sym)
           :use g-st-fn-shape)))

; the CALL statement, from any caller frame
(defthm g-st-fn-call
  (let ((vs (g-st-vals formals st)) (outs (list sv)))
    (implies (and (not (mv-nth 0 (gfn))) sv (eq (g-role sv st) :stobj) (tself-ok fn st)
                  (equal (g-st-dummies formals outs st) (list (list o :inout c)))
                  (stfn-hyps0)
                  (equal (find-proc fname procs) (mv-nth 1 (gfn)))
                  (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                  (svs-is cs ks caller heap)
                  (integerp fuel) (< (+ 9 (len ks) (acl2-count cs) (acl2-count (gbody (gsf 1)))) fuel))
             (equal (f-ex (list :call fname (cons (list :var ob) cs)) caller heap procs fuel)
                    (mv :normal caller (put key (mv-nth 1 (a-st x (pairlis$ vs ks) s st defs n)) heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-st-fn g-stmt g-st-dummies g-dummies g-st-vals g-role g-lits f-invoke f-ex-list a-st
                               st-plain no-calls st-ok st-wf svs-is g-st-fn-sem g-st-fn-shape g-has find-proc lkp put
                               g-reaches g-called g-fcalls g-ccalls g-locals g-em g-formals g-sym tself-ok lf-ok
                               g-st-fn-err stfn-run stl-holds stfn-body f-bind no-prim-defs int64-listp g-mvnth)
           :expand ((f-ex (list :call fname (cons (list :var ob) cs)) caller heap procs fuel))
           :use ((:instance g-st-fn-sem (fuel (1- fuel)))
                 gfn-sub-shape
                 (:instance f-invoke-st-codes (p (mv-nth 1 (gfn))) (d (list o :inout c)) (vs (g-st-vals formals st))
                            (a (list :var ob)) (fuel (1- fuel)))))))
