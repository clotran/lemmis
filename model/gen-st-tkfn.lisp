; gen-st-tkfn: function calls in a stobj subroutine's assignments, for
; gen-st-take (hpg-run-take). f-asg-val-t answers a call `f(args)` of
; hpg_size_class or hpg_class_len: the arguments by sv, then the callee's
; ACL2 value. asg-t-fcall: f-ev of such a call is that value, when the
; procedures' hpg_size_class, hpg_class_len and hpg_n40 are the generated
; ones -- from gen-disch-loop's hpg-size-class-fortran-correct and
; gen-disch-call's hpg-class-len-fortran-correct, through gen-callarg's
; f-invoke-args. A book of its own because gen-disch-call (gen-ret's
; macros) clashes with gen-stlst's: it is included locally here, and the
; generated procedures are exported as constants.

(in-package "ACL2")

(include-book "gen-stok")
(include-book "gen-proof")
(local (include-book "gen-disch-call"))

; clotran's definitions, as gen-disch / gen-disch-loop copy them (redundant here)
(defun hpg-n40 (x)
  (declare (xargs :guard t))
  (if (and (natp x) (<= x 1099511627776)) x 0))

(defun hpg-size-class (n c p)
  (declare (xargs :measure (nfix (- (+ 1 1099511627776) (nfix p)))
                  :guard (and (natp n) (<= n 1099511627776) (natp c) (<= c 64) (natp p) (<= 1 p)
                              (<= p (* 2 1099511627776)))))
  (if (or (not (natp p)) (< p 1) (<= n p) (< 1099511627776 p) (not (natp c)) (<= 64 c))
      c
    (hpg-size-class n (+ 1 c) (* 2 p))))

(defun hpg-class-len (c k p)
  (declare (xargs :measure (nfix (- (nfix c) (nfix k)))
                  :guard (and (natp c) (<= c 64) (natp k) (natp p) (<= p 1099511627776))))
  (if (or (not (natp c)) (not (natp k)) (<= c k) (< 64 c))
      (hpg-n40 p)
    (hpg-class-len c (+ 1 k) (hpg-n40 (* 2 (hpg-n40 p))))))

; the generated procedures (g-module of heapgn), as constants
(make-event
 (mv-let (err ps) (g-module *heapgn-raw* *heapgn-bools*)
   (declare (ignore err))
   `(progn (defconst *tk-hsc* ',(find-proc "hpg_size_class" ps))
           (defconst *tk-hcl* ',(find-proc "hpg_class_len" ps))
           (defconst *tk-n40* ',(find-proc "hpg_n40" ps)))))

(local (defthm tk-procs
         (and (equal *tk-hsc* (hproc "hpg_size_class")) (equal *tk-hcl* (hproc "hpg_class_len"))
              (equal *tk-n40* (hproc "hpg_n40")))
         :rule-classes nil))

; ---- the oracle: the arguments by sv, then the callee's ACL2 value

(defun svl-t (as fr heap)
  (if (atom as) (mv nil nil)
    (mv-let (e v) (sv (car as) fr heap)
      (if e (mv e nil)
        (mv-let (e2 vs) (svl-t (cdr as) fr heap)
          (if e2 (mv e2 nil) (mv nil (cons v vs))))))))

(defun f-asg-val-t (e fr heap)
  (declare (xargs :verify-guards nil))
  (mv-let (err ks) (svl-t (kaddr e) fr heap)
    (cond ((or err (not (int64-listp ks)) (not (equal (len ks) 3))) (mv :orc nil))
          ((equal (kadr e) "hpg_size_class") (mv nil (hpg-size-class (car ks) (cadr ks) (caddr ks))))
          ((equal (kadr e) "hpg_class_len") (mv nil (hpg-class-len (car ks) (cadr ks) (caddr ks))))
          (t (mv :orc nil)))))

; the arguments answer their sv values at the fuels f-bind gives them
(local (defun svl-ind (as fuel) (if (atom as) fuel (svl-ind (cdr as) (1- fuel)))))

(local (defthm args-at-svl
  (implies (and (not (mv-nth 0 (svl-t as fr heap))) (int64-listp (mv-nth 1 (svl-t as fr heap)))
                (integerp fuel) (< (acl2-count as) fuel))
           (args-at as fr heap procs fuel (mv-nth 1 (svl-t as fr heap))))
  :hints (("Goal" :induct (svl-ind as fuel) :in-theory (disable sv f-ev sv-ok-is-f-ev))
          ("Subgoal *1/2" :use ((:instance sv-ok-is-f-ev (e (car as)) (k (1- fuel))))))))

(local (defthm int64-list-three
  (implies (and (int64-listp ks) (equal (len ks) 3)) (equal (list (car ks) (cadr ks) (caddr ks)) ks))
  :hints (("Goal" :expand ((int64-listp ks) (int64-listp (cdr ks)) (int64-listp (cddr ks)) (int64-listp (cdddr ks)))))))

(local (defthm int64-list-three-p
  (implies (and (int64-listp ks) (equal (len ks) 3)) (and (int64p (car ks)) (int64p (cadr ks)) (int64p (caddr ks))))
  :hints (("Goal" :expand ((int64-listp ks) (int64-listp (cdr ks)) (int64-listp (cddr ks)))))))

(defconst *rt-b0*
  (+ 20 (* 450 (+ 2 (acl2-count *tk-hsc*))) (* 200 (* (+ 11 (acl2-count *tk-n40*)) (+ 2 (acl2-count *tk-hcl*))))))

(defmacro rt-finds ()
  '(and (equal (find-proc "hpg_size_class" procs) *tk-hsc*)
        (equal (find-proc "hpg_class_len" procs) *tk-hcl*)
        (equal (find-proc "hpg_n40" procs) *tk-n40*)))

(local (defthm f-ev-fcall-open-t
  (implies (and (posp fuel) (eq (kar x) :fcall) (eq (kar (find-proc (kadr x) procs)) :function))
           (equal (f-ev x fr heap procs fuel)
                  (list (mv-nth 0 (f-invoke (find-proc (kadr x) procs) (kaddr x) fr heap procs (1- fuel)))
                        (mv-nth 1 (f-invoke (find-proc (kadr x) procs) (kaddr x) fr heap procs (1- fuel))))))
  :hints (("Goal" :expand ((f-ev x fr heap procs fuel)) :in-theory (disable f-invoke find-proc)))))

; one lemma per callee, on any int64 values ks the arguments answer
(defmacro tk-fcall-lemma (thm name pc vs fthm fvs extra)
  `(local (defthm ,thm
     (implies (and (eq (kar e) :fcall) (equal (kadr e) ,name) (equal (find-proc ,name procs) ,pc) ,@extra
                   (args-at (kaddr e) fr heap procs (- fuel 2) ks) (int64-listp ks) (equal (len ks) 3)
                   (integerp fuel) (< *rt-b0* fuel))
              (equal (f-ev e fr heap procs fuel) (list nil (,(car fvs) (car ks) (cadr ks) (caddr ks)))))
     :hints (("Goal" :do-not-induct t
              :in-theory (disable f-ev f-invoke args-at g-lits ,(car fvs) f-invoke-args ,fthm find-proc int64-listp)
              :use (tk-procs int64-list-three int64-list-three-p
                    (:instance f-invoke-args (p ,pc) (vs ',vs) (as (kaddr e)) (caller fr) (caller2 fr) (fuel (1- fuel)))
                    (:instance ,fthm (caller fr) (fuel (1- fuel))
                               (,(nth 1 fvs) (car ks)) (,(nth 2 fvs) (cadr ks)) (,(nth 3 fvs) (caddr ks)))))))))

(tk-fcall-lemma fcall-hsc "hpg_size_class" *tk-hsc* (n c p) hpg-size-class-fortran-correct (hpg-size-class n c p) nil)
(tk-fcall-lemma fcall-hcl "hpg_class_len" *tk-hcl* (c k p) hpg-class-len-fortran-correct (hpg-class-len c k p)
                ((equal (find-proc "hpg_n40" procs) *tk-n40*)))

(defthm asg-t-fcall
  (implies (and (eq (kar e) :fcall) (not (mv-nth 0 (f-asg-val-t e fr heap))) (rt-finds)
                (integerp fuel) (< (+ *rt-b0* (acl2-count e)) fuel))
           (equal (f-ev e fr heap procs fuel) (mv nil (mv-nth 1 (f-asg-val-t e fr heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (f-asg-val-t) (f-ev svl-t args-at-svl fcall-hsc fcall-hcl int64-listp))
           :use ((:instance args-at-svl (as (kaddr e)) (fuel (- fuel 2)))
                 (:instance fcall-hsc (ks (mv-nth 1 (svl-t (kaddr e) fr heap))))
                 (:instance fcall-hcl (ks (mv-nth 1 (svl-t (kaddr e) fr heap))))))))
