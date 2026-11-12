; fstmt-steps: fps-steps, the calls fstmt.lisp's parser makes, generated
; from fps; fstmt-cost.lisp bounds it.

(in-package "ACL2")

(include-book "fstmt-complete")

(set-ignore-ok t)

; ---- cost: fps-steps counts fps's calls, each fp call counted by fp-steps
;      (generated: bb regen-steps.bb fstmt.lisp fps fps-steps fp)
(encapsulate () (local (in-theory (enable stmt-nt tok-in)))
(defun
 fps-steps
 (nt toks)
 (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fps-rank nt)) :verify-guards nil))
 (let
  ((tk (kar toks)))
  (if
   (atom toks)
   (if (member-eq nt ' (:attrs :onames :items :ctl :prefix :init :oitems)) (+ 1) (+ 1))
   (case
    nt
    (:stmt (let ((c1 (fps-steps (stmt-nt tk) toks))) (+ 1 c1)))
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
      ((and (equal tk (kw "implicit")) (equal (kadr toks) (kw "none"))) (+ 1))
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
          (let ((c2 (fps-steps :onames (kdr (kdr (kdr (kdr t2))))))) (if ok (+ 1 c2) (+ 1 c2)))))
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
         ((c3 (fp-steps :expr (kdr (kdr (kdr toks))))))
         (if (and ok (equal (kar r) (op ")")) (equal (kadr r) (kw "then"))) (+ 1 c3) (+ 1 c3))))
       (+ 1))))
    (:s-if
     (if
      (and (equal tk (kw "if")) (equal (kadr toks) (op "(")))
      (mv-let
       (ok e r)
       (fp :expr (kdr (kdr toks)))
       (declare (ignorable ok e r))
       (let
        ((c4 (fp-steps :expr (kdr (kdr toks)))))
        (cond
         ((not (and ok (equal (kar r) (op ")")))) (+ 1 c4))
         ((aif-labs-p (kdr r)) (+ 1 c4))
         ((and (equal (kadr r) (kw "then")) (atom (kdr (kdr r)))) (+ 1 c4))
         ((not (< (len (kdr r)) (len toks))) (+ 1 c4))
         (t
          (mv-let
           (ok2 s r2)
           (fps :stmt (kdr r))
           (declare (ignorable ok2 s r2))
           (let
            ((c5 (fps-steps :stmt (kdr r))))
            (if (and ok2 (action-kind-p (kar s))) (+ 1 c5 c4) (+ 1 c5 c4))))))))
      (+ 1)))
    (:s-do
     (cond
      ((not (equal tk (kw "do"))) (+ 1))
      ((label-int-p (kadr toks))
       (mv-let
        (ok c r)
        (fps :ctl (kdr (kdr toks)))
        (declare (ignorable ok c r))
        (let ((c6 (fps-steps :ctl (kdr (kdr toks))))) (if ok (+ 1 c6) (+ 1 c6)))))
      (t
       (mv-let
        (ok c r)
        (fps :ctl (kdr toks))
        (declare (ignorable ok c r))
        (let ((c7 (fps-steps :ctl (kdr toks)))) (if ok (+ 1 c7) (+ 1 c7)))))))
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
        ((c8 (fps-steps :ios (kdr (kdr toks)))))
        (if
         (not (and ok (< (len r) (len toks))))
         (+ 1 c8)
         (mv-let
          (ok2 is r2)
          (fps :oitems r)
          (declare (ignorable ok2 is r2))
          (let ((c9 (fps-steps :oitems r))) (if ok2 (+ 1 c9 c8) (+ 1 c9 c8)))))))))
    (:s-read
     (cond
      ((not (equal tk (kw "read"))) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok cs r)
        (fps :ios (kdr (kdr toks)))
        (declare (ignorable ok cs r))
        (let
         ((c10 (fps-steps :ios (kdr (kdr toks)))))
         (if
          (not (and ok (< (len r) (len toks))))
          (+ 1 c10)
          (mv-let
           (ok2 is r2)
           (fps :oitems r)
           (declare (ignorable ok2 is r2))
           (let ((c11 (fps-steps :oitems r))) (if (and ok2 (all-lone is)) (+ 1 c11 c10) (+ 1 c11 c10))))))))
      ((fmt-head-p (kadr toks))
       (mv-let
        (ok is r)
        (fps :items (kdr (kdr toks)))
        (declare (ignorable ok is r))
        (let ((c12 (fps-steps :items (kdr (kdr toks))))) (if (and ok (all-lone is)) (+ 1 c12) (+ 1 c12)))))
      (t (+ 1))))
    (:ios
     (mv-let
      (ok c r)
      (fps :io toks)
      (declare (ignorable ok c r))
      (let
       ((c13 (fps-steps :io toks)))
       (cond
        ((not (and ok (< (len r) (len toks)))) (+ 1 c13))
        ((and (unit-pos-p c) (equal (kar r) (op ",")) (fmt-head-p (kadr r)))
         (mv-let
          (ok2 cs r2)
          (fps :kios (kdr (kdr r)))
          (declare (ignorable ok2 cs r2))
          (let
           ((c14 (fps-steps :kios (kdr (kdr r)))))
           (let
            ((x (list* c (list :fmt nil (fmt-of (kadr r))) cs)))
            (if (and ok2 (ios-ok x)) (+ 1 c14 c13) (+ 1 c14 c13))))))
        (t
         (mv-let
          (ok2 cs r2)
          (fps :kios r)
          (declare (ignorable ok2 cs r2))
          (let
           ((c15 (fps-steps :kios r)))
           (let ((x (cons c cs))) (if (and ok2 (ios-ok x)) (+ 1 c15 c13) (+ 1 c15 c13))))))))))
    (:kios
     (cond
      ((equal tk (op ")")) (+ 1))
      ((equal tk (op ","))
       (mv-let
        (ok c r)
        (fps :io (kdr toks))
        (declare (ignorable ok c r))
        (let
         ((c16 (fps-steps :io (kdr toks))))
         (if
          (not (and ok (not (unit-pos-p c)) (< (len r) (len toks))))
          (+ 1 c16)
          (mv-let
           (ok2 cs r2)
           (fps :kios r)
           (declare (ignorable ok2 cs r2))
           (let ((c17 (fps-steps :kios r))) (if ok2 (+ 1 c17 c16) (+ 1 c17 c16))))))))
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
         (let ((c18 (fp-steps :expr (kdr (kdr toks))))) (if ok (+ 1 c18) (+ 1 c18))))))
      ((and (equal tk (kw "fmt")) (equal (kadr toks) (op "="))) (if (fmt-head-p (kaddr toks)) (+ 1) (+ 1)))
      ((and (equal tk (kw "advance")) (equal (kadr toks) (op "=")))
       (if (char-tok-p (kaddr toks)) (+ 1) (+ 1)))
      ((equal tk (op "*")) (+ 1))
      (t
       (mv-let
        (ok e r)
        (fp :expr toks)
        (declare (ignorable ok e r))
        (let ((c19 (fp-steps :expr toks))) (if ok (+ 1 c19) (+ 1 c19)))))))
    (:oitems
     (if
      (atom toks)
      (+ 1)
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c20 (fp-steps :expr toks)))
        (cond
         ((not (and ok (< (len r) (len toks)))) (+ 1 c20))
         ((atom r) (+ 1 c20))
         ((equal (kar r) (op ","))
          (mv-let
           (ok2 es r2)
           (fps :oitems (kdr r))
           (declare (ignorable ok2 es r2))
           (let ((c21 (fps-steps :oitems (kdr r)))) (if (and ok2 (consp es)) (+ 1 c21 c20) (+ 1 c21 c20)))))
         (t (+ 1 c20)))))))
    (:s-call
     (cond
      ((not (and (equal tk (kw "call")) (name-tok-p (kadr toks)))) (+ 1))
      ((equal (kaddr toks) (op "("))
       (mv-let
        (ok as r)
        (fp :args (kdr (kdr (kdr toks))))
        (declare (ignorable ok as r))
        (let ((c22 (fp-steps :args (kdr (kdr (kdr toks)))))) (if ok (+ 1 c22) (+ 1 c22)))))
      (t (+ 1))))
    (:s-print
     (if
      (and (equal tk (kw "print")) (fmt-head-p (kadr toks)))
      (mv-let
       (ok is r)
       (fps :items (kdr (kdr toks)))
       (declare (ignorable ok is r))
       (let ((c23 (fps-steps :items (kdr (kdr toks))))) (if ok (+ 1 c23) (+ 1 c23))))
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
         ((c24 (fp-steps :args (kdr (kdr toks)))))
         (cond
          ((not (and ok (no-kw-args as))) (+ 1 c24))
          ((equal (kar r) (op "="))
           (mv-let
            (ok2 e r2)
            (fp :expr (kdr r))
            (declare (ignorable ok2 e r2))
            (let ((c25 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c25 c24) (+ 1 c25 c24)))))
          ((equal (kar r) (op "("))
           (mv-let
            (ok2 g r2)
            (fp :arg (kdr r))
            (declare (ignorable ok2 g r2))
            (let
             ((c26 (fp-steps :arg (kdr r))))
             (if
              (and ok2 (substr-rng-p g) (equal (kar r2) (op ")")) (equal (kadr r2) (op "=")))
              (mv-let
               (ok3 e r3)
               (fp :expr (kdr (kdr r2)))
               (declare (ignorable ok3 e r3))
               (let ((c27 (fp-steps :expr (kdr (kdr r2))))) (if ok3 (+ 1 c27 c26 c24) (+ 1 c27 c26 c24))))
              (+ 1 c26 c24)))))
          ((equal (kar r) (op "%"))
           (mv-let
            (ok2 ps r2)
            (fp :parts r)
            (declare (ignorable ok2 ps r2))
            (let
             ((c28 (fp-steps :parts r)))
             (if
              (and ok2 (consp ps) (equal (kar r2) (op "=")))
              (mv-let
               (ok3 e r3)
               (fp :expr (kdr r2))
               (declare (ignorable ok3 e r3))
               (let ((c29 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c29 c28 c24) (+ 1 c29 c28 c24))))
              (+ 1 c28 c24)))))
          (t (+ 1 c24)))))
       (cond
        ((equal (kadr toks) (op "="))
         (mv-let
          (ok e r)
          (fp :expr (kdr (kdr toks)))
          (declare (ignorable ok e r))
          (let ((c30 (fp-steps :expr (kdr (kdr toks))))) (if ok (+ 1 c30) (+ 1 c30)))))
        ((equal (kadr toks) (op "%"))
         (mv-let
          (ok ps r)
          (fp :parts (kdr toks))
          (declare (ignorable ok ps r))
          (let
           ((c31 (fp-steps :parts (kdr toks))))
           (if
            (and ok (consp ps) (equal (kar r) (op "=")))
            (mv-let
             (ok2 e r2)
             (fp :expr (kdr r))
             (declare (ignorable ok2 e r2))
             (let ((c32 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c32 c31) (+ 1 c32 c31))))
            (+ 1 c31)))))
        (t (+ 1))))))
    (:s-type
     (cond
      ((not (equal tk (kw "type"))) (+ 1))
      ((and (equal (kadr toks) (op "(")) (name-tok-p (kaddr toks)) (equal (kadddr toks) (op ")")))
       (mv-let
        (ok d r)
        (fps :decl-rest (kdr (kdr (kdr (kdr toks)))))
        (declare (ignorable ok d r))
        (let ((c33 (fps-steps :decl-rest (kdr (kdr (kdr (kdr toks))))))) (if ok (+ 1 c33) (+ 1 c33)))))
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
        ((c34 (fp-steps :expr (kdr (kdr (kdr toks))))))
        (if (and ok (equal (kar r) (op ")"))) (+ 1 c34) (+ 1 c34))))
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
        (let ((c35 (fps-steps :ranges (kdr (kdr toks))))) (if ok (+ 1 c35) (+ 1 c35)))))
      (t (+ 1))))
    (:ranges
     (mv-let
      (ok s r)
      (fps :range toks)
      (declare (ignorable ok s r))
      (let
       ((c36 (fps-steps :range toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c36))
        ((equal (kar r) (op ")")) (+ 1 c36))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :ranges (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c37 (fps-steps :ranges (kdr r)))) (if ok2 (+ 1 c37 c36) (+ 1 c37 c36)))))
        (t (+ 1 c36))))))
    (:ixs
     (mv-let
      (ok s r)
      (fps :ix toks)
      (declare (ignorable ok s r))
      (let
       ((c38 (fps-steps :ix toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c38))
        ((equal (kar r) (op ")")) (+ 1 c38))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :ixs (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c39 (fps-steps :ixs (kdr r)))) (if ok2 (+ 1 c39 c38) (+ 1 c39 c38)))))
        (t (+ 1 c38))))))
    (:ix
     (if
      (and (name-tok-p tk) (equal (kadr toks) (op "=")))
      (mv-let
       (ok lo r)
       (fp :expr (kdr (kdr toks)))
       (declare (ignorable ok lo r))
       (let
        ((c40 (fp-steps :expr (kdr (kdr toks)))))
        (if
         (not (and ok (equal (kar r) (op ":"))))
         (+ 1 c40)
         (mv-let
          (ok2 hi r2)
          (fp :expr (kdr r))
          (declare (ignorable ok2 hi r2))
          (let
           ((c41 (fp-steps :expr (kdr r))))
           (cond
            ((not ok2) (+ 1 c41 c40))
            ((equal (kar r2) (op ":"))
             (mv-let
              (ok3 st r3)
              (fp :expr (kdr r2))
              (declare (ignorable ok3 st r3))
              (let ((c42 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c42 c41 c40) (+ 1 c42 c41 c40)))))
            (t (+ 1 c41 c40))))))))
      (+ 1)))
    (:range
     (if
      (equal tk (op ":"))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let ((c43 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c43) (+ 1 c43))))
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c44 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c44))
         ((not (equal (kar r) (op ":"))) (+ 1 c44))
         ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (+ 1 c44))
         (t
          (mv-let
           (ok2 b r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 b r2))
           (let ((c45 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c45 c44) (+ 1 c45 c44))))))))))
    (:s-unit
     (mv-let
      (ok pre r)
      (fps :prefix toks)
      (declare (ignorable ok pre r))
      (let
       ((c46 (fps-steps :prefix toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c46))
        ((equal (kar r) (kw "function"))
         (mv-let
          (ok2 fr r2)
          (fps :fn-rest r)
          (declare (ignorable ok2 fr r2))
          (let ((c47 (fps-steps :fn-rest r))) (if ok2 (+ 1 c47 c46) (+ 1 c47 c46)))))
        ((equal (kar r) (kw "subroutine"))
         (if
          (assoc-eq :ts pre)
          (+ 1 c46)
          (mv-let
           (ok2 sr r2)
           (fps :sub-rest r)
           (declare (ignorable ok2 sr r2))
           (let ((c48 (fps-steps :sub-rest r))) (if ok2 (+ 1 c48 c46) (+ 1 c48 c46))))))
        ((and (consp pre) (null (cdr pre)) (eq (kar (car pre)) :ts))
         (let*
          ((ts (kadr (car pre)))
           (c (and (eq (kar (kadr ts)) :len) (equal (kar r) (op ",")) (not (attr-kw-tok-p (kadr r))))))
          (mv-let
           (ok2 dr r2)
           (fps :decl-rest (if c (kdr r) r))
           (declare (ignorable ok2 dr r2))
           (let
            ((c49 (fps-steps :decl-rest (if c (kdr r) r))))
            (cond
             ((not ok2) (+ 1 c49 c46))
             ((not c) (+ 1 c49 c46))
             ((and (null (kar dr)) (null (kadr dr)) (not (attr-kw-tok-p (kar (kar (kaddr dr))))))
              (+ 1 c49 c46))
             (t (+ 1 c49 c46)))))))
        (t (+ 1 c46))))))
    (:fn-rest
     (if
      (and (equal tk (kw "function")) (name-tok-p (kadr toks)) (equal (kaddr toks) (op "(")))
      (mv-let
       (ok ds r)
       (fps :names (kdr (kdr (kdr toks))))
       (declare (ignorable ok ds r))
       (let
        ((c50 (fps-steps :names (kdr (kdr (kdr toks))))))
        (cond
         ((not ok) (+ 1 c50))
         ((and
           (equal (kar r) (kw "result"))
           (equal (kadr r) (op "("))
           (name-tok-p (kaddr r))
           (equal (kadddr r) (op ")")))
          (+ 1 c50))
         (t (+ 1 c50)))))
      (+ 1)))
    (:sub-rest
     (cond
      ((not (and (equal tk (kw "subroutine")) (name-tok-p (kadr toks)))) (+ 1))
      ((equal (kaddr toks) (op "("))
       (mv-let
        (ok ds r)
        (fps :names (kdr (kdr (kdr toks))))
        (declare (ignorable ok ds r))
        (let ((c51 (fps-steps :names (kdr (kdr (kdr toks)))))) (if ok (+ 1 c51) (+ 1 c51)))))
      (t (+ 1))))
    (:decl-rest
     (mv-let
      (ok as r)
      (fps :attrs toks)
      (declare (ignorable ok as r))
      (let
       ((c52 (fps-steps :attrs toks)))
       (if
        (not (and ok (<= (len r) (len toks))))
        (+ 1 c52)
        (let*
         ((dc (and (equal (kar r) (op ":")) (equal (kadr r) (op ":")))) (r1 (if dc (kdr (kdr r)) r)))
         (mv-let
          (ok2 es r2)
          (fps :ents r1)
          (declare (ignorable ok2 es r2))
          (let
           ((c53 (fps-steps :ents r1)))
           (if
            (and ok2 (consp es) (implies (or (consp as) (ents-init-p es)) dc))
            (+ 1 c53 c52)
            (+ 1 c53 c52)))))))))
    (:ts
     (cond
      ((not (tok-in tk *type-kws*)) (+ 1))
      ((equal tk (kw "double")) (if (equal (kadr toks) (kw "precision")) (+ 1) (+ 1)))
      ((equal (kadr toks) (op "("))
       (let*
        ((ch (equal tk (kw "character")))
         (kwp (and (equal (kaddr toks) (kw (if ch "len" "kind"))) (kw-head-p (kdr (kdr toks)))))
         (t1 (if kwp (kdr (kdr (kdr (kdr toks)))) (kdr (kdr toks)))))
        (if
         (and ch (equal (kar t1) (op "*")))
         (if (equal (kadr t1) (op ")")) (+ 1) (+ 1))
         (mv-let
          (ok e r)
          (fp :expr t1)
          (declare (ignorable ok e r))
          (let ((c54 (fp-steps :expr t1))) (if (and ok (equal (kar r) (op ")"))) (+ 1 c54) (+ 1 c54)))))))
      ((and (equal tk (kw "character")) (equal (kadr toks) (op "*")))
       (cond
        ((len-tok-p (kaddr toks)) (+ 1))
        ((equal (kaddr toks) (op "("))
         (let
          ((t1 (kdr (kdr (kdr toks)))))
          (if
           (equal (kar t1) (op "*"))
           (if (equal (kadr t1) (op ")")) (+ 1) (+ 1))
           (mv-let
            (ok e r)
            (fp :expr t1)
            (declare (ignorable ok e r))
            (let ((c55 (fp-steps :expr t1))) (if (and ok (equal (kar r) (op ")"))) (+ 1 c55) (+ 1 c55)))))))
        (t (+ 1))))
      (t (+ 1))))
    (:attrs
     (if
      (equal tk (op ","))
      (mv-let
       (ok a r)
       (fps :attr (kdr toks))
       (declare (ignorable ok a r))
       (let
        ((c56 (fps-steps :attr (kdr toks))))
        (if
         (not (and ok (<= (len r) (len (kdr toks)))))
         (+ 1 c56)
         (mv-let
          (ok2 as r2)
          (fps :attrs r)
          (declare (ignorable ok2 as r2))
          (let ((c57 (fps-steps :attrs r))) (if ok2 (+ 1 c57 c56) (+ 1 c57 c56)))))))
      (+ 1)))
    (:attr
     (cond
      ((equal tk (kw "parameter")) (+ 1))
      ((equal tk (kw "value")) (+ 1))
      ((and (equal tk (kw "intent")) (equal (kadr toks) (op "(")))
       (cond
        ((and
          (equal (kaddr toks) (kw "in"))
          (equal (kadddr toks) (kw "out"))
          (equal (kar (kdr (kdr (kdr (kdr toks))))) (op ")")))
         (+ 1))
        ((and (tok-in (kaddr toks) ' ("in" "out" "inout")) (equal (kadddr toks) (op ")"))) (+ 1))
        (t (+ 1))))
      ((and (equal tk (kw "dimension")) (equal (kadr toks) (op "(")))
       (mv-let
        (ok ss r)
        (fps :shapes (kdr (kdr toks)))
        (declare (ignorable ok ss r))
        (let ((c58 (fps-steps :shapes (kdr (kdr toks))))) (if ok (+ 1 c58) (+ 1 c58)))))
      (t (+ 1))))
    (:shapes
     (mv-let
      (ok ss r)
      (fps :shapes* toks)
      (declare (ignorable ok ss r))
      (let
       ((c59 (fps-steps :shapes* toks)))
       (if (and ok (consp ss) (shapes-same ss (shape-kind (car ss)))) (+ 1 c59) (+ 1 c59)))))
    (:shapes*
     (mv-let
      (ok s r)
      (fps :shape toks)
      (declare (ignorable ok s r))
      (let
       ((c60 (fps-steps :shape toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c60))
        ((equal (kar r) (op ")")) (+ 1 c60))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :shapes* (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c61 (fps-steps :shapes* (kdr r)))) (if ok2 (+ 1 c61 c60) (+ 1 c61 c60)))))
        (t (+ 1 c60))))))
    (:shape
     (if
      (equal tk (op ":"))
      (+ 1)
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c62 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c62))
         ((not (equal (kar r) (op ":"))) (+ 1 c62))
         ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (+ 1 c62))
         (t
          (mv-let
           (ok2 hi r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 hi r2))
           (let ((c63 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c63 c62) (+ 1 c63 c62))))))))))
    (:ents
     (mv-let
      (ok e r)
      (fps :ent toks)
      (declare (ignorable ok e r))
      (let
       ((c64 (fps-steps :ent toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c64))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 es r2)
          (fps :ents (kdr r))
          (declare (ignorable ok2 es r2))
          (let ((c65 (fps-steps :ents (kdr r)))) (if ok2 (+ 1 c65 c64) (+ 1 c65 c64)))))
        (t (+ 1 c64))))))
    (:ent
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok ss r)
        (fps :shapes (kdr (kdr toks)))
        (declare (ignorable ok ss r))
        (let
         ((c66 (fps-steps :shapes (kdr (kdr toks)))))
         (if
          (not (and ok (<= (len r) (len toks))))
          (+ 1 c66)
          (mv-let
           (ok2 i r2)
           (fps :init r)
           (declare (ignorable ok2 i r2))
           (let ((c67 (fps-steps :init r))) (if ok2 (+ 1 c67 c66) (+ 1 c67 c66))))))))
      (t
       (mv-let
        (ok2 i r2)
        (fps :init (kdr toks))
        (declare (ignorable ok2 i r2))
        (let ((c68 (fps-steps :init (kdr toks)))) (if ok2 (+ 1 c68) (+ 1 c68)))))))
    (:init
     (if
      (equal tk (op "="))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let ((c69 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c69) (+ 1 c69))))
      (+ 1)))
    (:names (if (equal tk (op ")")) (+ 1) (let ((c70 (fps-steps :names1 toks))) (+ 1 c70))))
    (:names1
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op ")")) (+ 1))
      ((equal (kadr toks) (op ","))
       (mv-let
        (ok ns r)
        (fps :names1 (kdr (kdr toks)))
        (declare (ignorable ok ns r))
        (let ((c71 (fps-steps :names1 (kdr (kdr toks))))) (if ok (+ 1 c71) (+ 1 c71)))))
      (t (+ 1))))
    (:onames
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op ","))
       (mv-let
        (ok ns r)
        (fps :onames (kdr (kdr toks)))
        (declare (ignorable ok ns r))
        (let ((c72 (fps-steps :onames (kdr (kdr toks))))) (if (and ok (consp ns)) (+ 1 c72) (+ 1 c72)))))
      (t (+ 1))))
    (:items
     (if
      (equal tk (op ","))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let
        ((c73 (fp-steps :expr (kdr toks))))
        (if
         (not (and ok (< (len r) (len toks))))
         (+ 1 c73)
         (mv-let
          (ok2 es r2)
          (fps :items r)
          (declare (ignorable ok2 es r2))
          (let ((c74 (fps-steps :items r))) (if ok2 (+ 1 c74 c73) (+ 1 c74 c73)))))))
      (+ 1)))
    (:ctl
     (if
      (atom toks)
      (+ 1)
      (let*
       ((c (equal tk (op ","))) (t1 (if c (kdr toks) toks)))
       (cond
        ((and (equal (kar t1) (kw "while")) (equal (kadr t1) (op "(")))
         (mv-let
          (ok e r)
          (fp :expr (kdr (kdr t1)))
          (declare (ignorable ok e r))
          (let
           ((c75 (fp-steps :expr (kdr (kdr t1)))))
           (if (and ok (equal (kar r) (op ")"))) (+ 1 c75) (+ 1 c75)))))
        ((and (equal (kar t1) (kw "concurrent")) (equal (kadr t1) (op "(")))
         (let
          ((t2 (kdr (kdr t1))))
          (mv-let
           (ok ts r)
           (if (tok-in (kar t2) *type-kws*) (fps :ts t2) (mv t nil t2))
           (declare (ignorable ok ts r))
           (let
            ((c76 (if (tok-in (kar t2) *type-kws*) (fps-steps :ts t2) 0)))
            (cond
             ((not (and ok (<= (len r) (len t2)))) (+ 1 c76))
             ((and
               ts
               (not (and (equal (kar ts) "integer") (equal (kar r) (op ":")) (equal (kadr r) (op ":")))))
              (+ 1 c76))
             (t
              (mv-let
               (ok2 ixs r2)
               (fps :ixs (if ts (kdr (kdr r)) r))
               (declare (ignorable ok2 ixs r2))
               (let
                ((c77 (fps-steps :ixs (if ts (kdr (kdr r)) r))))
                (if ok2 (+ 1 c77 c76) (+ 1 c77 c76))))))))))
        ((and (name-tok-p (kar t1)) (equal (kadr t1) (op "=")))
         (mv-let
          (ok e1 r)
          (fp :expr (kdr (kdr t1)))
          (declare (ignorable ok e1 r))
          (let
           ((c78 (fp-steps :expr (kdr (kdr t1)))))
           (if
            (not (and ok (equal (kar r) (op ","))))
            (+ 1 c78)
            (mv-let
             (ok2 e2 r2)
             (fp :expr (kdr r))
             (declare (ignorable ok2 e2 r2))
             (let
              ((c79 (fp-steps :expr (kdr r))))
              (cond
               ((not ok2) (+ 1 c79 c78))
               ((equal (kar r2) (op ","))
                (mv-let
                 (ok3 e3 r3)
                 (fp :expr (kdr r2))
                 (declare (ignorable ok3 e3 r3))
                 (let ((c80 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c80 c79 c78) (+ 1 c80 c79 c78)))))
               (t (+ 1 c79 c78)))))))))
        (t (+ 1))))))
    (:prefix
     (cond
      ((tok-in tk *prefix-kws*)
       (mv-let
        (ok ps r)
        (fps :prefix (kdr toks))
        (declare (ignorable ok ps r))
        (let ((c81 (fps-steps :prefix (kdr toks)))) (if ok (+ 1 c81) (+ 1 c81)))))
      ((tok-in tk *type-kws*)
       (mv-let
        (ok ts r)
        (fps :ts toks)
        (declare (ignorable ok ts r))
        (let
         ((c82 (fps-steps :ts toks)))
         (if
          (not (and ok (< (len r) (len toks))))
          (+ 1 c82)
          (mv-let
           (ok2 ps r2)
           (fps :prefix r)
           (declare (ignorable ok2 ps r2))
           (let ((c83 (fps-steps :prefix r))) (if ok2 (+ 1 c83 c82) (+ 1 c83 c82))))))))
      (t (+ 1))))
    (otherwise (+ 1)))))))

(defthm fps-steps-natp (natp (fps-steps nt toks)) :rule-classes :type-prescription)
