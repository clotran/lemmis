; fstmt-steps: the first half of fps-steps's case clauses (generated:
; bb regen-steps.bb fstmt.lisp fps fps-steps fp imp-specs); fstmt-steps2.lisp holds
; the rest and the defun, fstmt-cost.lisp bounds it.

(in-package "ACL2")

(defconst *fps-steps-1*
 '((:stmt (let ((c1 (fps-steps (stmt-nt tk) toks))) (+ 1 c1)))
    (:s-head
     (if (and (or (equal tk (kw "program")) (equal tk (kw "module"))) (name-tok-p (kadr toks))) (+ 1) (+ 1)))
    (:s-end
     (if
      (not (equal tk (kw "end")))
      (+ 1)
      (if
       (tok-in (kadr toks) *end-kinds*)
       (if (and (tok-in (kadr toks) *unit-ends*) (name-tok-p (kaddr toks))) (+ 1) (+ 1))
       (+ 1))))
    (:s-other
     (cond
      ((equal tk (kw "contains")) (+ 1))
      ((equal tk (kw "block")) (+ 1))
      ((and (equal tk (kw "implicit")) (equal (kadr toks) (kw "none"))) (+ 1))
      ((equal tk (kw "implicit"))
       (mv-let
        (ok ss r)
        (imp-specs (kdr toks))
        (declare (ignorable ok ss r))
        (let ((c2 (imp-specs-steps (kdr toks)))) (if ok (+ 1 c2) (+ 1 c2)))))
      ((equal tk (kw "dimension"))
       (let
        ((dc (and (equal (kadr toks) (op ":")) (equal (kaddr toks) (op ":")))))
        (mv-let
         (ok es r)
         (fps :ents (if dc (kdr (kdr (kdr toks))) (kdr toks)))
         (declare (ignorable ok es r))
         (let
          ((c3 (fps-steps :ents (if dc (kdr (kdr (kdr toks))) (kdr toks)))))
          (if (and ok (consp es) (dim-ents-p es)) (+ 1 c3) (+ 1 c3))))))
      ((equal tk (kw "save"))
       (cond
        ((atom (kdr toks)) (+ 1))
        ((and (equal (kadr toks) (op ":")) (equal (kaddr toks) (op ":")))
         (mv-let
          (ok ns r)
          (fps :onames (kdr (kdr (kdr toks))))
          (declare (ignorable ok ns r))
          (let
           ((c4 (fps-steps :onames (kdr (kdr (kdr toks))))))
           (if (and ok (consp ns)) (+ 1 c4) (+ 1 c4)))))
        (t
         (mv-let
          (ok ns r)
          (fps :onames (kdr toks))
          (declare (ignorable ok ns r))
          (let ((c5 (fps-steps :onames (kdr toks)))) (if (and ok (consp ns)) (+ 1 c5) (+ 1 c5)))))))
      ((and (tok-in tk ' ("allocate" "deallocate")) (equal (kadr toks) (op "(")))
       (mv-let
        (ok as r)
        (fp :args (kdr (kdr toks)))
        (declare (ignorable ok as r))
        (let
         ((c6 (fp-steps :args (kdr (kdr toks)))))
         (let
          ((d (equal tk (kw "deallocate"))))
          (if (and ok (consp as) (alloc-objs-p as d)) (+ 1 c6) (+ 1 c6))))))
      ((and (equal tk (kw "stop")) (consp (kdr toks)))
       (mv-let
        (ok e r)
        (fp :expr (kdr toks))
        (declare (ignorable ok e r))
        (let ((c7 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c7) (+ 1 c7)))))
      ((tok-in tk *simple-kinds*) (+ 1))
      (t (+ 1))))
    (:s-use
     (if
      (not (equal tk (kw "use")))
      (+ 1)
      (let*
       ((t1 (kdr toks))
        (nat
         (cond
          ((and (equal (kar t1) (op ":")) (equal (kadr t1) (op ":"))) :dc)
          ((and
            (equal (kar t1) (op ","))
            (tok-in (kadr t1) ' ("intrinsic" "non_intrinsic"))
            (equal (kaddr t1) (op ":"))
            (equal (kadddr t1) (op ":")))
           (kadr (kadr t1)))
          (t nil)))
        (t2 (cond ((eq nat :dc) (kdr (kdr t1))) (nat (kdr (kdr (kdr (kdr t1))))) (t t1))))
       (cond
        ((not (name-tok-p (kar t2))) (+ 1))
        ((and (equal (kadr t2) (op ",")) (equal (kaddr t2) (kw "only")) (equal (kadddr t2) (op ":")))
         (mv-let
          (ok ns r)
          (fps :onames (kdr (kdr (kdr (kdr t2)))))
          (declare (ignorable ok ns r))
          (let ((c8 (fps-steps :onames (kdr (kdr (kdr (kdr t2))))))) (if ok (+ 1 c8) (+ 1 c8)))))
        (t (+ 1))))))
    (:s-else
     (if
      (not (equal tk (kw "else")))
      (+ 1)
      (if
       (and (equal (kadr toks) (kw "if")) (equal (kaddr toks) (op "(")))
       (mv-let
        (ok e r)
        (fp :expr (kdr (kdr (kdr toks))))
        (declare (ignorable ok e r))
        (let
         ((c9 (fp-steps :expr (kdr (kdr (kdr toks))))))
         (if (and ok (equal (kar r) (op ")")) (equal (kadr r) (kw "then"))) (+ 1 c9) (+ 1 c9))))
       (+ 1))))
    (:s-if
     (if
      (and (equal tk (kw "if")) (equal (kadr toks) (op "(")))
      (mv-let
       (ok e r)
       (fp :expr (kdr (kdr toks)))
       (declare (ignorable ok e r))
       (let
        ((c10 (fp-steps :expr (kdr (kdr toks)))))
        (cond
         ((not (and ok (equal (kar r) (op ")")))) (+ 1 c10))
         ((aif-labs-p (kdr r)) (+ 1 c10))
         ((and (equal (kadr r) (kw "then")) (atom (kdr (kdr r)))) (+ 1 c10))
         ((not (< (len (kdr r)) (len toks))) (+ 1 c10))
         (t
          (mv-let
           (ok2 s r2)
           (fps :stmt (kdr r))
           (declare (ignorable ok2 s r2))
           (let
            ((c11 (fps-steps :stmt (kdr r))))
            (if (and ok2 (action-kind-p (kar s))) (+ 1 c11 c10) (+ 1 c11 c10))))))))
      (+ 1)))
    (:s-do
     (cond
      ((not (equal tk (kw "do"))) (+ 1))
      ((label-int-p (kadr toks))
       (mv-let
        (ok c r)
        (fps :ctl (kdr (kdr toks)))
        (declare (ignorable ok c r))
        (let ((c12 (fps-steps :ctl (kdr (kdr toks))))) (if ok (+ 1 c12) (+ 1 c12)))))
      (t
       (mv-let
        (ok c r)
        (fps :ctl (kdr toks))
        (declare (ignorable ok c r))
        (let ((c13 (fps-steps :ctl (kdr toks)))) (if ok (+ 1 c13) (+ 1 c13)))))))
    (:s-label (if (label-tok-p tk) (+ 1) (+ 1)))
    (:s-goto
     (if (and (equal tk (kw "go")) (equal (kadr toks) (kw "to")) (label-int-p (kaddr toks))) (+ 1) (+ 1)))
    (:s-format (if (and (equal tk (kw "format")) (fmt-tok-p (kadr toks))) (+ 1) (+ 1)))
    (:s-write
     (if
      (not (and (equal tk (kw "write")) (equal (kadr toks) (op "("))))
      (+ 1)
      (mv-let
       (ok cs r)
       (fps :ios (kdr (kdr toks)))
       (declare (ignorable ok cs r))
       (let
        ((c14 (fps-steps :ios (kdr (kdr toks)))))
        (if
         (not (and ok (< (len r) (len toks))))
         (+ 1 c14)
         (mv-let
          (ok2 is r2)
          (fps :oitems r)
          (declare (ignorable ok2 is r2))
          (let ((c15 (fps-steps :oitems r))) (if ok2 (+ 1 c15 c14) (+ 1 c15 c14)))))))))
    (:s-read
     (cond
      ((not (equal tk (kw "read"))) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok cs r)
        (fps :ios (kdr (kdr toks)))
        (declare (ignorable ok cs r))
        (let
         ((c16 (fps-steps :ios (kdr (kdr toks)))))
         (if
          (not (and ok (< (len r) (len toks))))
          (+ 1 c16)
          (mv-let
           (ok2 is r2)
           (fps :oitems r)
           (declare (ignorable ok2 is r2))
           (let ((c17 (fps-steps :oitems r))) (if (and ok2 (all-lone is)) (+ 1 c17 c16) (+ 1 c17 c16))))))))
      ((fmt-head-p (kadr toks))
       (mv-let
        (ok is r)
        (fps :items (kdr (kdr toks)))
        (declare (ignorable ok is r))
        (let ((c18 (fps-steps :items (kdr (kdr toks))))) (if (and ok (all-lone is)) (+ 1 c18) (+ 1 c18)))))
      (t (+ 1))))
    (:ios
     (mv-let
      (ok c r)
      (fps :io toks)
      (declare (ignorable ok c r))
      (let
       ((c19 (fps-steps :io toks)))
       (cond
        ((not (and ok (< (len r) (len toks)))) (+ 1 c19))
        ((and (unit-pos-p c) (equal (kar r) (op ",")) (fmt-head-p (kadr r)))
         (mv-let
          (ok2 cs r2)
          (fps :kios (kdr (kdr r)))
          (declare (ignorable ok2 cs r2))
          (let
           ((c20 (fps-steps :kios (kdr (kdr r)))))
           (let
            ((x (list* c (list :fmt nil (fmt-of (kadr r))) cs)))
            (if (and ok2 (ios-ok x)) (+ 1 c20 c19) (+ 1 c20 c19))))))
        (t
         (mv-let
          (ok2 cs r2)
          (fps :kios r)
          (declare (ignorable ok2 cs r2))
          (let
           ((c21 (fps-steps :kios r)))
           (let ((x (cons c cs))) (if (and ok2 (ios-ok x)) (+ 1 c21 c19) (+ 1 c21 c19))))))))))
    (:kios
     (cond
      ((equal tk (op ")")) (+ 1))
      ((equal tk (op ","))
       (mv-let
        (ok c r)
        (fps :io (kdr toks))
        (declare (ignorable ok c r))
        (let
         ((c22 (fps-steps :io (kdr toks))))
         (if
          (not (and ok (not (unit-pos-p c)) (< (len r) (len toks))))
          (+ 1 c22)
          (mv-let
           (ok2 cs r2)
           (fps :kios r)
           (declare (ignorable ok2 cs r2))
           (let ((c23 (fps-steps :kios r))) (if ok2 (+ 1 c23 c22) (+ 1 c23 c22))))))))
      (t (+ 1))))
    (:io
     (cond
      ((and (equal tk (kw "unit")) (equal (kadr toks) (op "=")))
       (if
        (equal (kaddr toks) (op "*"))
        (+ 1)
        (mv-let
         (ok e r)
         (fp :expr (kdr (kdr toks)))
         (declare (ignorable ok e r))
         (let ((c24 (fp-steps :expr (kdr (kdr toks))))) (if ok (+ 1 c24) (+ 1 c24))))))
      ((and (equal tk (kw "fmt")) (equal (kadr toks) (op "="))) (if (fmt-head-p (kaddr toks)) (+ 1) (+ 1)))
      ((and (equal tk (kw "advance")) (equal (kadr toks) (op "=")))
       (if (char-tok-p (kaddr toks)) (+ 1) (+ 1)))
      ((equal tk (op "*")) (+ 1))
      (t
       (mv-let
        (ok e r)
        (fp :expr toks)
        (declare (ignorable ok e r))
        (let ((c25 (fp-steps :expr toks))) (if ok (+ 1 c25) (+ 1 c25)))))))
    (:oitems
     (if
      (atom toks)
      (+ 1)
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c26 (fp-steps :expr toks)))
        (cond
         ((not (and ok (< (len r) (len toks)))) (+ 1 c26))
         ((atom r) (+ 1 c26))
         ((equal (kar r) (op ","))
          (mv-let
           (ok2 es r2)
           (fps :oitems (kdr r))
           (declare (ignorable ok2 es r2))
           (let ((c27 (fps-steps :oitems (kdr r)))) (if (and ok2 (consp es)) (+ 1 c27 c26) (+ 1 c27 c26)))))
         (t (+ 1 c26)))))))
    (:s-call
     (cond
      ((not (and (equal tk (kw "call")) (name-tok-p (kadr toks)))) (+ 1))
      ((equal (kaddr toks) (op "("))
       (mv-let
        (ok as r)
        (fp :args (kdr (kdr (kdr toks))))
        (declare (ignorable ok as r))
        (let ((c28 (fp-steps :args (kdr (kdr (kdr toks)))))) (if ok (+ 1 c28) (+ 1 c28)))))
      (t (+ 1))))
    (:s-print
     (if
      (and (equal tk (kw "print")) (fmt-head-p (kadr toks)))
      (mv-let
       (ok is r)
       (fps :items (kdr (kdr toks)))
       (declare (ignorable ok is r))
       (let ((c29 (fps-steps :items (kdr (kdr toks))))) (if ok (+ 1 c29) (+ 1 c29))))
      (+ 1)))
    (:s-assign
     (if
      (not (name-tok-p tk))
      (+ 1)
      (if
       (equal (kadr toks) (op "("))
       (mv-let
        (ok as r)
        (fp :args (kdr (kdr toks)))
        (declare (ignorable ok as r))
        (let
         ((c30 (fp-steps :args (kdr (kdr toks)))))
         (cond
          ((not (and ok (no-kw-args as))) (+ 1 c30))
          ((equal (kar r) (op "="))
           (mv-let
            (ok2 e r2)
            (fp :expr (kdr r))
            (declare (ignorable ok2 e r2))
            (let ((c31 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c31 c30) (+ 1 c31 c30)))))
          ((equal (kar r) (op "("))
           (mv-let
            (ok2 g r2)
            (fp :arg (kdr r))
            (declare (ignorable ok2 g r2))
            (let
             ((c32 (fp-steps :arg (kdr r))))
             (if
              (and ok2 (substr-rng-p g) (equal (kar r2) (op ")")) (equal (kadr r2) (op "=")))
              (mv-let
               (ok3 e r3)
               (fp :expr (kdr (kdr r2)))
               (declare (ignorable ok3 e r3))
               (let ((c33 (fp-steps :expr (kdr (kdr r2))))) (if ok3 (+ 1 c33 c32 c30) (+ 1 c33 c32 c30))))
              (+ 1 c32 c30)))))
          ((equal (kar r) (op "%"))
           (mv-let
            (ok2 ps r2)
            (fp :parts r)
            (declare (ignorable ok2 ps r2))
            (let
             ((c34 (fp-steps :parts r)))
             (if
              (and ok2 (consp ps) (equal (kar r2) (op "=")))
              (mv-let
               (ok3 e r3)
               (fp :expr (kdr r2))
               (declare (ignorable ok3 e r3))
               (let ((c35 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c35 c34 c30) (+ 1 c35 c34 c30))))
              (+ 1 c34 c30)))))
          (t (+ 1 c30)))))
       (cond
        ((equal (kadr toks) (op "="))
         (mv-let
          (ok e r)
          (fp :expr (kdr (kdr toks)))
          (declare (ignorable ok e r))
          (let ((c36 (fp-steps :expr (kdr (kdr toks))))) (if ok (+ 1 c36) (+ 1 c36)))))
        ((equal (kadr toks) (op "%"))
         (mv-let
          (ok ps r)
          (fp :parts (kdr toks))
          (declare (ignorable ok ps r))
          (let
           ((c37 (fp-steps :parts (kdr toks))))
           (if
            (and ok (consp ps) (equal (kar r) (op "=")))
            (mv-let
             (ok2 e r2)
             (fp :expr (kdr r))
             (declare (ignorable ok2 e r2))
             (let ((c38 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c38 c37) (+ 1 c38 c37))))
            (+ 1 c37)))))
        (t (+ 1))))))
    (:s-type
     (cond
      ((not (equal tk (kw "type"))) (+ 1))
      ((and (equal (kadr toks) (op "(")) (name-tok-p (kaddr toks)) (equal (kadddr toks) (op ")")))
       (mv-let
        (ok d r)
        (fps :decl-rest (kdr (kdr (kdr (kdr toks)))))
        (declare (ignorable ok d r))
        (let ((c39 (fps-steps :decl-rest (kdr (kdr (kdr (kdr toks))))))) (if ok (+ 1 c39) (+ 1 c39)))))
      ((and (equal (kadr toks) (op ":")) (equal (kaddr toks) (op ":")) (name-tok-p (kadddr toks))) (+ 1))
      ((name-tok-p (kadr toks)) (+ 1))
      (t (+ 1))))
    (:s-select
     (if
      (and (equal tk (kw "select")) (equal (kadr toks) (kw "case")) (equal (kaddr toks) (op "(")))
      (mv-let
       (ok e r)
       (fp :expr (kdr (kdr (kdr toks))))
       (declare (ignorable ok e r))
       (let
        ((c40 (fp-steps :expr (kdr (kdr (kdr toks))))))
        (if (and ok (equal (kar r) (op ")"))) (+ 1 c40) (+ 1 c40))))
      (+ 1)))
    (:s-case
     (cond
      ((not (equal tk (kw "case"))) (+ 1))
      ((equal (kadr toks) (kw "default")) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok rs r)
        (fps :ranges (kdr (kdr toks)))
        (declare (ignorable ok rs r))
        (let ((c41 (fps-steps :ranges (kdr (kdr toks))))) (if ok (+ 1 c41) (+ 1 c41)))))
      (t (+ 1))))
    (:ranges
     (mv-let
      (ok s r)
      (fps :range toks)
      (declare (ignorable ok s r))
      (let
       ((c42 (fps-steps :range toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c42))
        ((equal (kar r) (op ")")) (+ 1 c42))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :ranges (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c43 (fps-steps :ranges (kdr r)))) (if ok2 (+ 1 c43 c42) (+ 1 c43 c42)))))
        (t (+ 1 c42))))))
    (:ixs
     (mv-let
      (ok s r)
      (fps :ix toks)
      (declare (ignorable ok s r))
      (let
       ((c44 (fps-steps :ix toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c44))
        ((equal (kar r) (op ")")) (+ 1 c44))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :ixs (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c45 (fps-steps :ixs (kdr r)))) (if ok2 (+ 1 c45 c44) (+ 1 c45 c44)))))
        (t (+ 1 c44))))))))
