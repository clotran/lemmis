; gen-stcall: CALL statements in the heap-aware fuel-free meaning (GEN.md
; "What remains" 4 (4a), first piece). sxc is sx plus a :call case answered
; by an oracle, s-call-val, on the call's name, argument expressions, frame
; and heap: (mv err frame' heap'). Under p-sorc -- "the oracle is what the
; procedures answer": wherever s-call-val answers without error, f-ex of
; the CALL at any fuel past b + its size answers :normal with its frame and
; heap -- f-ex-list at fuel past b + the statements' size is sxc-list
; wherever sxc-list answers no error (sxc-ok-is-f-ex-list), as gen-stok's
; sx-ok-is-f-ex-list is for sx. And wherever sx answers no error, sxc is sx
; (sxc-is-sx), so every gs-sem/gst-sem lemma on sx carries over.
; A new evaluator, not a case added to sx: sx's theorems (gen-stok's
; sx-ok-is-f-ex-list, so g-st-fn-sem) would otherwise need p-sorc.
; DO stays a :syntax error here: the tail loop's DO is reasoned on f-ex
; directly, as g-fn-sem-loop does for functions (4b).

(in-package "ACL2")

(include-book "gen-stok")

(encapsulate (((s-call-val * * * *) => (mv * * *)))
  (local (defun s-call-val (name args fr heap) (declare (ignore name args fr heap)) (mv :unknown nil nil))))

(mutual-recursion
 (defun sxc (x frame heap)
   (declare (xargs :guard t :measure (acl2-count x) :verify-guards nil))
   (case (kar x)
     (:assign (sx x frame heap))
     (:if (mv-let (err c) (sv (kadr x) frame heap)
            (cond (err (mv (errst err) frame heap))
                  ((not (booleanp c)) (mv (errst :type) frame heap))
                  (c (sxc-list (kaddr x) frame heap))
                  (t (sxc-list (kadddr x) frame heap)))))
     (:select (mv-let (err k) (sv (kadr x) frame heap)
                (cond (err (mv (errst err) frame heap))
                      ((not (integerp k)) (mv (errst :type) frame heap))
                      (t (let ((arm (lkp k (kaddr x))))
                           (sxc-list (if arm (kadr arm) (kadddr x)) frame heap))))))
     ((:cycle :exit :return) (mv (kar x) frame heap))
     (:call (mv-let (err fr2 h2) (s-call-val (kadr x) (kaddr x) frame heap)
              (if err (mv (errst err) frame heap) (mv :normal fr2 h2))))
     (otherwise (mv (errst :syntax) frame heap))))
 (defun sxc-list (ss frame heap)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) (mv :normal frame heap)
     (mv-let (st fr2 h2) (sxc (car ss) frame heap)
       (if (eq st :normal) (sxc-list (cdr ss) fr2 h2) (mv st fr2 h2))))))

(in-theory (disable sxc sxc-list))

(defun sxc-ind (flag s fr heap k)
  (declare (xargs :measure (acl2-count s) :verify-guards nil))
  (if (or (zp k) (atom s)) (list fr heap k)
    (if (eq flag :stmt)
        (mv-let (err v) (sv (kadr s) fr heap)
          (declare (ignore err))
          (list (sxc-ind :list (kaddr s) fr heap (1- k))
                (sxc-ind :list (kadddr s) fr heap (1- k))
                (sxc-ind :list (kadr (lkp v (kaddr s))) fr heap (1- k))))
      (mv-let (st fr2 h2) (sxc (car s) fr heap)
        (declare (ignore st))
        (list (sxc-ind :stmt (car s) fr heap (1- k))
              (sxc-ind :list (cdr s) fr2 h2 (1- k)))))))

; ---- wherever sx answers no error, sxc is sx (no CALL was run)

(defthm sxc-is-sx-flag
  (if (eq flag :stmt)
      (implies (not (errstp (mv-nth 0 (sx s fr heap)))) (equal (sxc s fr heap) (sx s fr heap)))
    (implies (not (errstp (mv-nth 0 (sx-list s fr heap)))) (equal (sxc-list s fr heap) (sx-list s fr heap))))
  :rule-classes nil
  :hints (("Goal" :induct (sxc-ind flag s fr heap (1+ (acl2-count s))) :do-not-induct t
           :in-theory (disable sv))
          (and stable-under-simplificationp
               '(:expand ((sx s fr heap) (sx-list s fr heap) (sxc s fr heap) (sxc-list s fr heap))))))

(defthm sxc-is-sx
  (implies (not (errstp (mv-nth 0 (sx s fr heap)))) (equal (sxc s fr heap) (sx s fr heap)))
  :hints (("Goal" :use (:instance sxc-is-sx-flag (flag :stmt)))))

(defthm sxc-list-is-sx-list
  (implies (not (errstp (mv-nth 0 (sx-list ss fr heap)))) (equal (sxc-list ss fr heap) (sx-list ss fr heap)))
  :hints (("Goal" :use (:instance sxc-is-sx-flag (flag :list) (s ss)))))

; ---- the oracle is what the procedures answer

(defun-sk p-sorc (procs b)
  (forall (x fr heap fuel)
    (implies (and (eq (kar x) :call) (not (mv-nth 0 (s-call-val (kadr x) (kaddr x) fr heap)))
                  (integerp fuel) (< (+ b (acl2-count x)) fuel))
             (equal (f-ex x fr heap procs fuel)
                    (mv :normal (mv-nth 1 (s-call-val (kadr x) (kaddr x) fr heap))
                        (mv-nth 2 (s-call-val (kadr x) (kaddr x) fr heap)))))))

(in-theory (disable p-sorc))

(defthm sxc-call-f-ex
  (implies (and (p-sorc procs b) (equal (kar s) :call) (not (errstp (mv-nth 0 (sxc s fr heap))))
                (integerp k) (< (+ b (acl2-count s)) k))
           (equal (f-ex s fr heap procs k) (sxc s fr heap)))
  :hints (("Goal" :in-theory (disable f-ex p-sorc-necc)
           :use (:instance p-sorc-necc (x s) (fuel k))
           :expand ((sxc s fr heap)))))

(defthm sxc-assign-f-ex
  (implies (and (equal (kar s) :assign) (not (errstp (mv-nth 0 (sxc s fr heap)))) (integerp k) (< (acl2-count s) k))
           (equal (f-ex s fr heap procs k) (sxc s fr heap)))
  :hints (("Goal" :in-theory (disable f-ex sx) :expand ((sxc s fr heap)))))

(defthm sxc-ok-is-f-ex-flag
  (implies (and (p-sorc procs b) (natp b) (integerp k) (< (+ b (acl2-count s)) k))
           (if (eq flag :stmt)
               (implies (and (not (equal (kar s) :assign)) (not (equal (kar s) :call))
                             (not (errstp (mv-nth 0 (sxc s fr heap)))))
                        (equal (f-ex s fr heap procs k) (sxc s fr heap)))
             (implies (not (errstp (mv-nth 0 (sxc-list s fr heap))))
                      (equal (f-ex-list s fr heap procs k) (sxc-list s fr heap)))))
  :rule-classes nil
  :hints (("Goal" :induct (sxc-ind flag s fr heap k) :do-not-induct t
           :in-theory (disable f-ex f-ex-list f-ex-return sv-is-f-ev sx-is-f-ex sx-assign-ok-cs sx
                               sx-ok-assign-f-ex))
          (and stable-under-simplificationp
               '(:expand ((sxc s fr heap) (sxc-list s fr heap))))))

(defthm sxc-ok-is-f-ex-list
  (implies (and (p-sorc procs b) (natp b) (not (errstp (mv-nth 0 (sxc-list ss fr heap))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxc-list ss fr heap)))
  :hints (("Goal" :use (:instance sxc-ok-is-f-ex-flag (flag :list) (s ss)))))
