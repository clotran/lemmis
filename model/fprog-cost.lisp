; fprog-cost: fpu-cost, the bound on fpu's work (fprog.lisp): a successful
; parse makes at most 32 calls per statement it consumes, plus fpu-d nt.

(in-package "ACL2")

(include-book "fprog")

; ---- cost: fpu-steps counts fpu's calls (generated: bb mksteps.bb fprog.lisp fpu fpu-steps)

(defun
 fpu-steps
 (nt toks)
 (declare (xargs :guard t :measure (+ (* 8 (len toks)) (fpu-rank nt)) :verify-guards nil))
 (let
  ((s (kar toks)))
  (case
   nt
   (:program
    (mv-let
     (ok us r)
     (fpu :units toks)
     (declare (ignorable ok us r))
     (let ((c1 (fpu-steps :units toks))) (if (and ok (consp us)) (+ 1 c1) (+ 1 c1)))))
   (:units
    (if
     (atom toks)
     (+ 1)
     (mv-let
      (ok u r)
      (fpu :unit toks)
      (declare (ignorable ok u r))
      (let
       ((c2 (fpu-steps :unit toks)))
       (if
        (not (and ok (< (len r) (len toks))))
        (+ 1 c2)
        (mv-let
         (ok2 us r2)
         (fpu :units r)
         (declare (ignorable ok2 us r2))
         (let ((c3 (fpu-steps :units r))) (if ok2 (+ 1 c3 c2) (+ 1 c3 c2)))))))))
   ((:unit :sub)
    (if
     (not
      (if
       (eq nt :unit)
       (member-eq (kar s) ' (:program :module :function :subroutine))
       (member-eq (kar s) ' (:function :subroutine))))
     (+ 1)
     (mv-let
      (ok sp r)
      (fpu :spec (cdr toks))
      (declare (ignorable ok sp r))
      (let
       ((c4 (fpu-steps :spec (cdr toks))))
       (if
        (not (and ok (<= (len r) (len (cdr toks)))))
        (+ 1 c4)
        (mv-let
         (ok2 ex r2)
         (if (eq (kar s) :module) (mv t nil r) (fpu :exec r))
         (declare (ignorable ok2 ex r2))
         (let
          ((c5 (if (eq (kar s) :module) 0 (fpu-steps :exec r))))
          (if
           (not (and ok2 (<= (len r2) (len r))))
           (+ 1 c5 c4)
           (mv-let
            (ok3 in r3)
            (fpu :int r2)
            (declare (ignorable ok3 in r3))
            (let
             ((c6 (fpu-steps :int r2)))
             (if (not (and ok3 (consp r3) (end-ok (car r3) s))) (+ 1 c6 c5 c4) (+ 1 c6 c5 c4))))))))))))
   (:spec
    (mv-let
     (ok us r)
     (fpu :uses toks)
     (declare (ignorable ok us r))
     (let
      ((c7 (fpu-steps :uses toks)))
      (if
       (not (and ok (<= (len r) (len toks))))
       (+ 1 c7)
       (let*
        ((imp (if (equal (kar r) ' (:implicit-none)) (car r) nil)) (r1 (if imp (cdr r) r)))
        (mv-let
         (ok2 ds r2)
         (fpu :decls r1)
         (declare (ignorable ok2 ds r2))
         (let ((c8 (fpu-steps :decls r1))) (if ok2 (+ 1 c8 c7) (+ 1 c8 c7)))))))))
   ((:uses :comps)
    (if
     (and (consp toks) (if (eq nt :uses) (eq (kar s) :use) (member-eq (kar s) ' (:decl :tdecl))))
     (mv-let
      (ok xs r)
      (fpu nt (cdr toks))
      (declare (ignorable ok xs r))
      (let ((c9 (fpu-steps nt (cdr toks)))) (if ok (+ 1 c9) (+ 1 c9))))
     (+ 1)))
   (:decls
    (if
     (member-eq (kar s) ' (:decl :tdecl :type :save :dimstmt :implicit :data))
     (mv-let
      (ok d r)
      (fpu :decl toks)
      (declare (ignorable ok d r))
      (let
       ((c10 (fpu-steps :decl toks)))
       (if
        (not (and ok (< (len r) (len toks))))
        (+ 1 c10)
        (mv-let
         (ok2 ds r2)
         (fpu :decls r)
         (declare (ignorable ok2 ds r2))
         (let ((c11 (fpu-steps :decls r))) (if ok2 (+ 1 c11 c10) (+ 1 c11 c10)))))))
     (+ 1)))
   (:decl
    (cond
     ((not (consp toks)) (+ 1))
     ((eq (kar s) :type)
      (mv-let
       (ok cs r)
       (fpu :comps (cdr toks))
       (declare (ignorable ok cs r))
       (let
        ((c12 (fpu-steps :comps (cdr toks))))
        (if (and ok (consp r) (tend-ok (car r) s)) (+ 1 c12) (+ 1 c12)))))
     ((member-eq (kar s) ' (:decl :tdecl :save :dimstmt :implicit :data)) (+ 1))
     (t (+ 1))))
   (:exec
    (if
     (c-start-p s)
     (mv-let
      (ok c r)
      (fpu :c toks)
      (declare (ignorable ok c r))
      (let
       ((c13 (fpu-steps :c toks)))
       (if
        (not (and ok (< (len r) (len toks))))
        (+ 1 c13)
        (mv-let
         (ok2 cs r2)
         (fpu :exec r)
         (declare (ignorable ok2 cs r2))
         (let ((c14 (fpu-steps :exec r))) (if ok2 (+ 1 c14 c13) (+ 1 c14 c13)))))))
     (+ 1)))
   (:c
    (case
     (kar s)
     (:if-then
      (mv-let
       (ok blk r)
       (fpu :exec (cdr toks))
       (declare (ignorable ok blk r))
       (let
        ((c15 (fpu-steps :exec (cdr toks))))
        (if
         (not (and ok (<= (len r) (len (cdr toks)))))
         (+ 1 c15)
         (mv-let
          (ok2 eifs r2)
          (fpu :eifs r)
          (declare (ignorable ok2 eifs r2))
          (let
           ((c16 (fpu-steps :eifs r)))
           (if
            (not (and ok2 (<= (len r2) (len r))))
            (+ 1 c16 c15)
            (mv-let
             (ok3 els r3)
             (if
              (equal (kar r2) ' (:else))
              (mv-let (ok4 b r4) (fpu :exec (cdr r2)) (mv ok4 (list b) r4))
              (mv t nil r2))
             (declare (ignorable ok3 els r3))
             (let
              ((c17 (if (equal (kar r2) ' (:else)) (fpu-steps :exec (cdr r2)) 0)))
              (if (and ok3 (equal (kar r3) ' (:end "if" nil))) (+ 1 c17 c16 c15) (+ 1 c17 c16 c15)))))))))))
     (:do
      (mv-let
       (ok blk r)
       (fpu :exec (cdr toks))
       (declare (ignorable ok blk r))
       (let
        ((c18 (fpu-steps :exec (cdr toks))))
        (if (and ok (equal (kar r) ' (:end "do" nil))) (+ 1 c18) (+ 1 c18)))))
     (:block
      (mv-let
       (ok ds r)
       (fpu :decls (cdr toks))
       (declare (ignorable ok ds r))
       (let
        ((c19 (fpu-steps :decls (cdr toks))))
        (if
         (not (and ok (<= (len r) (len (cdr toks)))))
         (+ 1 c19)
         (mv-let
          (ok2 blk r2)
          (fpu :exec r)
          (declare (ignorable ok2 blk r2))
          (let
           ((c20 (fpu-steps :exec r)))
           (if (and ok2 (equal (kar r2) ' (:end "block" nil))) (+ 1 c20 c19) (+ 1 c20 c19))))))))
     (:select
      (mv-let
       (ok arms r)
       (fpu :arms (cdr toks))
       (declare (ignorable ok arms r))
       (let
        ((c21 (fpu-steps :arms (cdr toks))))
        (if
         (and ok (equal (kar r) ' (:end "select" nil)) (<= (count-defaults arms) 1))
         (+ 1 c21)
         (+ 1 c21)))))
     (otherwise (if (c-start-p s) (+ 1) (+ 1)))))
   (:arms
    (if
     (member-eq (kar s) ' (:case :case-default))
     (mv-let
      (ok blk r)
      (fpu :exec (cdr toks))
      (declare (ignorable ok blk r))
      (let
       ((c22 (fpu-steps :exec (cdr toks))))
       (if
        (not (and ok (<= (len r) (len (cdr toks)))))
        (+ 1 c22)
        (mv-let
         (ok2 as r2)
         (fpu :arms r)
         (declare (ignorable ok2 as r2))
         (let ((c23 (fpu-steps :arms r))) (if ok2 (+ 1 c23 c22) (+ 1 c23 c22)))))))
     (+ 1)))
   (:eifs
    (if
     (eq (kar s) :else-if)
     (mv-let
      (ok blk r)
      (fpu :exec (cdr toks))
      (declare (ignorable ok blk r))
      (let
       ((c24 (fpu-steps :exec (cdr toks))))
       (if
        (not (and ok (<= (len r) (len (cdr toks)))))
        (+ 1 c24)
        (mv-let
         (ok2 es r2)
         (fpu :eifs r)
         (declare (ignorable ok2 es r2))
         (let ((c25 (fpu-steps :eifs r))) (if ok2 (+ 1 c25 c24) (+ 1 c25 c24)))))))
     (+ 1)))
   (:int
    (if
     (equal s ' (:contains))
     (mv-let
      (ok ss r)
      (fpu :subs (cdr toks))
      (declare (ignorable ok ss r))
      (let ((c26 (fpu-steps :subs (cdr toks)))) (if ok (+ 1 c26) (+ 1 c26))))
     (+ 1)))
   (:subs
    (if
     (member-eq (kar s) ' (:function :subroutine))
     (mv-let
      (ok u r)
      (fpu :sub toks)
      (declare (ignorable ok u r))
      (let
       ((c27 (fpu-steps :sub toks)))
       (if
        (not (and ok (< (len r) (len toks))))
        (+ 1 c27)
        (mv-let
         (ok2 us r2)
         (fpu :subs r)
         (declare (ignorable ok2 us r2))
         (let ((c28 (fpu-steps :subs r))) (if ok2 (+ 1 c28 c27) (+ 1 c28 c27)))))))
     (+ 1)))
   (otherwise (+ 1)))))

(defthm fpu-steps-natp (natp (fpu-steps nt toks)) :rule-classes :type-prescription)

; the constant each nt adds; a unit, a subprogram and an executable
; construct always read their own first and last statements, so they owe
; less than nothing
(defun fpu-d (nt)
  (declare (xargs :guard t))
  (case nt (:program 8) (:spec 12) ((:unit :sub :c :decl) -15) (otherwise 4)))

; a successful parse makes at most 32 calls per statement it consumes,
; plus fpu-d nt
(defthm fpu-cost
  (implies (mv-nth 0 (fpu nt toks))
           (<= (+ (fpu-steps nt toks) (* 32 (len (mv-nth 2 (fpu nt toks)))))
               (+ (* 32 (len toks)) (fpu-d nt))))
  :hints (("Goal" :induct (fpu-steps nt toks) :in-theory (enable member-equal len-cdr-consp))
          (fpu-step-hint id clause '((fpu nt toks) (fpu-steps nt toks)))))

; the openers stay closed past here
(in-theory (disable fgu-cons-open fyu-cons-open fpu-open))
