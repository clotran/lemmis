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
      ((equal tk (kw "data"))
       (mv-let
        (ok ss r)
        (fps :dsets (kdr toks))
        (declare (ignorable ok ss r))
        (let ((c4 (fps-steps :dsets (kdr toks)))) (if ok (+ 1 c4) (+ 1 c4)))))
      ((equal tk (kw "save"))
       (cond
        ((atom (kdr toks)) (+ 1))
        ((and (equal (kadr toks) (op ":")) (equal (kaddr toks) (op ":")))
         (mv-let
          (ok ns r)
          (fps :onames (kdr (kdr (kdr toks))))
          (declare (ignorable ok ns r))
          (let
           ((c5 (fps-steps :onames (kdr (kdr (kdr toks))))))
           (if (and ok (consp ns)) (+ 1 c5) (+ 1 c5)))))
        (t
         (mv-let
          (ok ns r)
          (fps :onames (kdr toks))
          (declare (ignorable ok ns r))
          (let ((c6 (fps-steps :onames (kdr toks)))) (if (and ok (consp ns)) (+ 1 c6) (+ 1 c6)))))))
      ((and (tok-in tk ' ("allocate" "deallocate")) (equal (kadr toks) (op "(")))
       (mv-let
        (ok as r)
        (fp :args (kdr (kdr toks)))
        (declare (ignorable ok as r))
        (let
         ((c7 (fp-steps :args (kdr (kdr toks)))))
         (let
          ((d (equal tk (kw "deallocate"))))
          (if (and ok (consp as) (alloc-objs-p as d)) (+ 1 c7) (+ 1 c7))))))
      ((and (equal tk (kw "stop")) (consp (kdr toks)))
       (mv-let
        (ok e r)
        (fp :expr (kdr toks))
        (declare (ignorable ok e r))
        (let ((c8 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c8) (+ 1 c8)))))
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
          (let ((c9 (fps-steps :onames (kdr (kdr (kdr (kdr t2))))))) (if ok (+ 1 c9) (+ 1 c9)))))
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
         ((c10 (fp-steps :expr (kdr (kdr (kdr toks))))))
         (if (and ok (equal (kar r) (op ")")) (equal (kadr r) (kw "then"))) (+ 1 c10) (+ 1 c10))))
       (+ 1))))
    (:s-if
     (if
      (and (equal tk (kw "if")) (equal (kadr toks) (op "(")))
      (mv-let
       (ok e r)
       (fp :expr (kdr (kdr toks)))
       (declare (ignorable ok e r))
       (let
        ((c11 (fp-steps :expr (kdr (kdr toks)))))
        (cond
         ((not (and ok (equal (kar r) (op ")")))) (+ 1 c11))
         ((aif-labs-p (kdr r)) (+ 1 c11))
         ((and (equal (kadr r) (kw "then")) (atom (kdr (kdr r)))) (+ 1 c11))
         ((not (< (len (kdr r)) (len toks))) (+ 1 c11))
         (t
          (mv-let
           (ok2 s r2)
           (fps :stmt (kdr r))
           (declare (ignorable ok2 s r2))
           (let
            ((c12 (fps-steps :stmt (kdr r))))
            (if (and ok2 (action-kind-p (kar s))) (+ 1 c12 c11) (+ 1 c12 c11))))))))
      (+ 1)))
    (:s-do
     (cond
      ((not (equal tk (kw "do"))) (+ 1))
      ((label-int-p (kadr toks))
       (mv-let
        (ok c r)
        (fps :ctl (kdr (kdr toks)))
        (declare (ignorable ok c r))
        (let ((c13 (fps-steps :ctl (kdr (kdr toks))))) (if ok (+ 1 c13) (+ 1 c13)))))
      (t
       (mv-let
        (ok c r)
        (fps :ctl (kdr toks))
        (declare (ignorable ok c r))
        (let ((c14 (fps-steps :ctl (kdr toks)))) (if ok (+ 1 c14) (+ 1 c14)))))))
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
        ((c15 (fps-steps :ios (kdr (kdr toks)))))
        (if
         (not (and ok (< (len r) (len toks))))
         (+ 1 c15)
         (mv-let
          (ok2 is r2)
          (fps :oitems r)
          (declare (ignorable ok2 is r2))
          (let ((c16 (fps-steps :oitems r))) (if ok2 (+ 1 c16 c15) (+ 1 c16 c15)))))))))
    (:s-read
     (cond
      ((not (equal tk (kw "read"))) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok cs r)
        (fps :ios (kdr (kdr toks)))
        (declare (ignorable ok cs r))
        (let
         ((c17 (fps-steps :ios (kdr (kdr toks)))))
         (if
          (not (and ok (< (len r) (len toks))))
          (+ 1 c17)
          (mv-let
           (ok2 is r2)
           (fps :oitems r)
           (declare (ignorable ok2 is r2))
           (let ((c18 (fps-steps :oitems r))) (if (and ok2 (all-lone is)) (+ 1 c18 c17) (+ 1 c18 c17))))))))
      ((fmt-head-p (kadr toks))
       (mv-let
        (ok is r)
        (fps :items (kdr (kdr toks)))
        (declare (ignorable ok is r))
        (let ((c19 (fps-steps :items (kdr (kdr toks))))) (if (and ok (all-lone is)) (+ 1 c19) (+ 1 c19)))))
      (t (+ 1))))
    (:ios
     (mv-let
      (ok c r)
      (fps :io toks)
      (declare (ignorable ok c r))
      (let
       ((c20 (fps-steps :io toks)))
       (cond
        ((not (and ok (< (len r) (len toks)))) (+ 1 c20))
        ((and (unit-pos-p c) (equal (kar r) (op ",")) (fmt-head-p (kadr r)))
         (mv-let
          (ok2 cs r2)
          (fps :kios (kdr (kdr r)))
          (declare (ignorable ok2 cs r2))
          (let
           ((c21 (fps-steps :kios (kdr (kdr r)))))
           (let
            ((x (list* c (list :fmt nil (fmt-of (kadr r))) cs)))
            (if (and ok2 (ios-ok x)) (+ 1 c21 c20) (+ 1 c21 c20))))))
        (t
         (mv-let
          (ok2 cs r2)
          (fps :kios r)
          (declare (ignorable ok2 cs r2))
          (let
           ((c22 (fps-steps :kios r)))
           (let ((x (cons c cs))) (if (and ok2 (ios-ok x)) (+ 1 c22 c20) (+ 1 c22 c20))))))))))
    (:kios
     (cond
      ((equal tk (op ")")) (+ 1))
      ((equal tk (op ","))
       (mv-let
        (ok c r)
        (fps :io (kdr toks))
        (declare (ignorable ok c r))
        (let
         ((c23 (fps-steps :io (kdr toks))))
         (if
          (not (and ok (not (unit-pos-p c)) (< (len r) (len toks))))
          (+ 1 c23)
          (mv-let
           (ok2 cs r2)
           (fps :kios r)
           (declare (ignorable ok2 cs r2))
           (let ((c24 (fps-steps :kios r))) (if ok2 (+ 1 c24 c23) (+ 1 c24 c23))))))))
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
         (let ((c25 (fp-steps :expr (kdr (kdr toks))))) (if ok (+ 1 c25) (+ 1 c25))))))
      ((and (equal tk (kw "fmt")) (equal (kadr toks) (op "="))) (if (fmt-head-p (kaddr toks)) (+ 1) (+ 1)))
      ((and (equal tk (kw "advance")) (equal (kadr toks) (op "=")))
       (if (char-tok-p (kaddr toks)) (+ 1) (+ 1)))
      ((equal tk (op "*")) (+ 1))
      (t
       (mv-let
        (ok e r)
        (fp :expr toks)
        (declare (ignorable ok e r))
        (let ((c26 (fp-steps :expr toks))) (if ok (+ 1 c26) (+ 1 c26)))))))
    (:oitems
     (if
      (atom toks)
      (+ 1)
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c27 (fp-steps :expr toks)))
        (cond
         ((not (and ok (< (len r) (len toks)))) (+ 1 c27))
         ((atom r) (+ 1 c27))
         ((equal (kar r) (op ","))
          (mv-let
           (ok2 es r2)
           (fps :oitems (kdr r))
           (declare (ignorable ok2 es r2))
           (let ((c28 (fps-steps :oitems (kdr r)))) (if (and ok2 (consp es)) (+ 1 c28 c27) (+ 1 c28 c27)))))
         (t (+ 1 c27)))))))
    (:s-call
     (cond
      ((not (and (equal tk (kw "call")) (name-tok-p (kadr toks)))) (+ 1))
      ((equal (kaddr toks) (op "("))
       (mv-let
        (ok as r)
        (fp :args (kdr (kdr (kdr toks))))
        (declare (ignorable ok as r))
        (let ((c29 (fp-steps :args (kdr (kdr (kdr toks)))))) (if ok (+ 1 c29) (+ 1 c29)))))
      (t (+ 1))))
    (:s-print
     (if
      (and (equal tk (kw "print")) (fmt-head-p (kadr toks)))
      (mv-let
       (ok is r)
       (fps :items (kdr (kdr toks)))
       (declare (ignorable ok is r))
       (let ((c30 (fps-steps :items (kdr (kdr toks))))) (if ok (+ 1 c30) (+ 1 c30))))
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
         ((c31 (fp-steps :args (kdr (kdr toks)))))
         (cond
          ((not (and ok (no-kw-args as))) (+ 1 c31))
          ((equal (kar r) (op "="))
           (mv-let
            (ok2 e r2)
            (fp :expr (kdr r))
            (declare (ignorable ok2 e r2))
            (let ((c32 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c32 c31) (+ 1 c32 c31)))))
          ((equal (kar r) (op "("))
           (mv-let
            (ok2 g r2)
            (fp :arg (kdr r))
            (declare (ignorable ok2 g r2))
            (let
             ((c33 (fp-steps :arg (kdr r))))
             (if
              (and ok2 (substr-rng-p g) (equal (kar r2) (op ")")) (equal (kadr r2) (op "=")))
              (mv-let
               (ok3 e r3)
               (fp :expr (kdr (kdr r2)))
               (declare (ignorable ok3 e r3))
               (let ((c34 (fp-steps :expr (kdr (kdr r2))))) (if ok3 (+ 1 c34 c33 c31) (+ 1 c34 c33 c31))))
              (+ 1 c33 c31)))))
          ((equal (kar r) (op "%"))
           (mv-let
            (ok2 ps r2)
            (fp :parts r)
            (declare (ignorable ok2 ps r2))
            (let
             ((c35 (fp-steps :parts r)))
             (if
              (and ok2 (consp ps) (equal (kar r2) (op "=")))
              (mv-let
               (ok3 e r3)
               (fp :expr (kdr r2))
               (declare (ignorable ok3 e r3))
               (let ((c36 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c36 c35 c31) (+ 1 c36 c35 c31))))
              (+ 1 c35 c31)))))
          (t (+ 1 c31)))))
       (cond
        ((equal (kadr toks) (op "="))
         (mv-let
          (ok e r)
          (fp :expr (kdr (kdr toks)))
          (declare (ignorable ok e r))
          (let ((c37 (fp-steps :expr (kdr (kdr toks))))) (if ok (+ 1 c37) (+ 1 c37)))))
        ((equal (kadr toks) (op "%"))
         (mv-let
          (ok ps r)
          (fp :parts (kdr toks))
          (declare (ignorable ok ps r))
          (let
           ((c38 (fp-steps :parts (kdr toks))))
           (if
            (and ok (consp ps) (equal (kar r) (op "=")))
            (mv-let
             (ok2 e r2)
             (fp :expr (kdr r))
             (declare (ignorable ok2 e r2))
             (let ((c39 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c39 c38) (+ 1 c39 c38))))
            (+ 1 c38)))))
        (t (+ 1))))))
    (:s-type
     (cond
      ((not (equal tk (kw "type"))) (+ 1))
      ((and (equal (kadr toks) (op "(")) (name-tok-p (kaddr toks)) (equal (kadddr toks) (op ")")))
       (mv-let
        (ok d r)
        (fps :decl-rest (kdr (kdr (kdr (kdr toks)))))
        (declare (ignorable ok d r))
        (let ((c40 (fps-steps :decl-rest (kdr (kdr (kdr (kdr toks))))))) (if ok (+ 1 c40) (+ 1 c40)))))
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
        ((c41 (fp-steps :expr (kdr (kdr (kdr toks))))))
        (if (and ok (equal (kar r) (op ")"))) (+ 1 c41) (+ 1 c41))))
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
        (let ((c42 (fps-steps :ranges (kdr (kdr toks))))) (if ok (+ 1 c42) (+ 1 c42)))))
      (t (+ 1))))
    (:ranges
     (mv-let
      (ok s r)
      (fps :range toks)
      (declare (ignorable ok s r))
      (let
       ((c43 (fps-steps :range toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c43))
        ((equal (kar r) (op ")")) (+ 1 c43))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :ranges (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c44 (fps-steps :ranges (kdr r)))) (if ok2 (+ 1 c44 c43) (+ 1 c44 c43)))))
        (t (+ 1 c43))))))
    (:ixs
     (mv-let
      (ok s r)
      (fps :ix toks)
      (declare (ignorable ok s r))
      (let
       ((c45 (fps-steps :ix toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c45))
        ((equal (kar r) (op ")")) (+ 1 c45))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :ixs (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c46 (fps-steps :ixs (kdr r)))) (if ok2 (+ 1 c46 c45) (+ 1 c46 c45)))))
        (t (+ 1 c45))))))
    (:ix
     (if
      (and (name-tok-p tk) (equal (kadr toks) (op "=")))
      (mv-let
       (ok lo r)
       (fp :expr (kdr (kdr toks)))
       (declare (ignorable ok lo r))
       (let
        ((c47 (fp-steps :expr (kdr (kdr toks)))))
        (if
         (not (and ok (equal (kar r) (op ":"))))
         (+ 1 c47)
         (mv-let
          (ok2 hi r2)
          (fp :expr (kdr r))
          (declare (ignorable ok2 hi r2))
          (let
           ((c48 (fp-steps :expr (kdr r))))
           (cond
            ((not ok2) (+ 1 c48 c47))
            ((equal (kar r2) (op ":"))
             (mv-let
              (ok3 st r3)
              (fp :expr (kdr r2))
              (declare (ignorable ok3 st r3))
              (let ((c49 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c49 c48 c47) (+ 1 c49 c48 c47)))))
            (t (+ 1 c48 c47))))))))
      (+ 1)))
    (:range
     (if
      (equal tk (op ":"))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let ((c50 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c50) (+ 1 c50))))
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c51 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c51))
         ((not (equal (kar r) (op ":"))) (+ 1 c51))
         ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (+ 1 c51))
         (t
          (mv-let
           (ok2 b r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 b r2))
           (let ((c52 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c52 c51) (+ 1 c52 c51))))))))))))
