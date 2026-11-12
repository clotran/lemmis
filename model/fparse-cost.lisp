; fparse-cost: fp-cost, fparse.lisp's parser is linear in the tokens it reads.

(in-package "ACL2")

(include-book "fparse")

; ---- fp-cost: the parser is linear
;
; fp-steps counts the calls fp makes: fp's own recursion, each answer
; 1 plus the counts of the calls it made, each call let-bound under the
; tests that govern it. It is generated from fp by mksteps.bb (bb
; mksteps.bb fparse.lisp fp fp-steps) and pasted here. A successful parse
; makes at most 32 calls per token it consumes, plus fp-d nt; with
; fp-complete, a sentence of n tokens is read in at most 32n + 19 calls.

(in-theory (enable member-equal))
(defun
 fp-steps
 (nt toks)
 (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fp-rank nt)) :verify-guards nil))
 (let
  ((tk (kar toks)))
  (case
   nt
   ((:expr :equiv :or :l3 :add)
    (mv-let
     (ok a r)
     (fp (lev-sub nt) toks)
     (declare (ignorable ok a r))
     (let
      ((c1 (fp-steps (lev-sub nt) toks)))
      (if
       (not (and ok (<= (len r) (len toks))))
       (+ 1 c1)
       (mv-let
        (ok2 rest r2)
        (fp (lev-rest nt) r)
        (declare (ignorable ok2 rest r2))
        (let ((c2 (fp-steps (lev-rest nt) r))) (if ok2 (+ 1 c2 c1) (+ 1 c2 c1))))))))
   ((:expr* :equiv* :or* :l3* :l2* :add*)
    (if
     (and (consp toks) (member-equal tk (lev-ops nt)))
     (mv-let
      (ok a r)
      (fp (lev-sub nt) (cdr toks))
      (declare (ignorable ok a r))
      (let
       ((c3 (fp-steps (lev-sub nt) (cdr toks))))
       (if
        (not (and ok (<= (len r) (len (cdr toks)))))
        (+ 1 c3)
        (mv-let
         (ok2 rest r2)
         (fp nt r)
         (declare (ignorable ok2 rest r2))
         (let ((c4 (fp-steps nt r))) (if ok2 (+ 1 c4 c3) (+ 1 c4 c3)))))))
     (+ 1)))
   (:and
    (if
     (and (consp toks) (equal tk (op ".not.")))
     (mv-let
      (ok a r)
      (fp :l4 (cdr toks))
      (declare (ignorable ok a r))
      (let ((c5 (fp-steps :l4 (cdr toks)))) (if ok (+ 1 c5) (+ 1 c5))))
     (mv-let
      (ok a r)
      (fp :l4 toks)
      (declare (ignorable ok a r))
      (let ((c6 (fp-steps :l4 toks))) (if ok (+ 1 c6) (+ 1 c6))))))
   (:l4
    (mv-let
     (ok a r)
     (fp :l3 toks)
     (declare (ignorable ok a r))
     (let
      ((c7 (fp-steps :l3 toks)))
      (cond
       ((not (and ok (<= (len r) (len toks)))) (+ 1 c7))
       ((and (consp r) (member-equal (car r) *rel-ops*))
        (mv-let
         (ok2 b r2)
         (fp :l3 (cdr r))
         (declare (ignorable ok2 b r2))
         (let ((c8 (fp-steps :l3 (cdr r)))) (if ok2 (+ 1 c8 c7) (+ 1 c8 c7)))))
       (t (+ 1 c7))))))
   (:l2
    (let*
     ((sign (if (and (consp toks) (member-equal tk *add-ops*)) tk nil)) (t1 (if sign (cdr toks) toks)))
     (mv-let
      (ok a r)
      (fp :add t1)
      (declare (ignorable ok a r))
      (let
       ((c9 (fp-steps :add t1)))
       (if
        (not (and ok (<= (len r) (len t1))))
        (+ 1 c9)
        (mv-let
         (ok2 rest r2)
         (fp :l2* r)
         (declare (ignorable ok2 rest r2))
         (let ((c10 (fp-steps :l2* r))) (if ok2 (+ 1 c10 c9) (+ 1 c10 c9)))))))))
   (:mult
    (mv-let
     (ok a r)
     (fp :prim toks)
     (declare (ignorable ok a r))
     (let
      ((c11 (fp-steps :prim toks)))
      (cond
       ((not (and ok (<= (len r) (len toks)))) (+ 1 c11))
       ((and (consp r) (equal (car r) (op "**")))
        (mv-let
         (ok2 b r2)
         (fp :mult (cdr r))
         (declare (ignorable ok2 b r2))
         (let ((c12 (fp-steps :mult (cdr r)))) (if ok2 (+ 1 c12 c11) (+ 1 c12 c11)))))
       (t (+ 1 c11))))))
   (:prim
    (cond
     ((not (consp toks)) (+ 1))
     ((lit-tok-p tk) (+ 1))
     ((xname-tok-p tk)
      (mv-let
       (ok b r)
       (fp :base toks)
       (declare (ignorable ok b r))
       (let
        ((c13 (fp-steps :base toks)))
        (cond
         ((not (and ok (< (len r) (len toks)))) (+ 1 c13))
         ((and (consp r) (equal (car r) (op "%")) (member-eq (kar b) ' (:name :ref)))
          (mv-let
           (ok2 ps r2)
           (fp :parts r)
           (declare (ignorable ok2 ps r2))
           (let ((c14 (fp-steps :parts r))) (if ok2 (+ 1 c14 c13) (+ 1 c14 c13)))))
         (t (+ 1 c13))))))
     ((equal tk (op "("))
      (mv-let
       (ok e r)
       (fp :expr (cdr toks))
       (declare (ignorable ok e r))
       (let
        ((c15 (fp-steps :expr (cdr toks))))
        (cond
         ((not (and ok (consp r))) (+ 1 c15))
         ((equal (car r) (op ")")) (+ 1 c15))
         ((and (equal (car r) (op ",")) (cpart-p e) (<= (len r) (len (cdr toks))))
          (mv-let
           (ok2 e2 r2)
           (fp :expr (cdr r))
           (declare (ignorable ok2 e2 r2))
           (let
            ((c16 (fp-steps :expr (cdr r))))
            (if (and ok2 (cpart-p e2) (consp r2) (equal (car r2) (op ")"))) (+ 1 c16 c15) (+ 1 c16 c15)))))
         (t (+ 1 c15))))))
     ((equal tk (op "["))
      (mv-let
       (ok es r)
       (fp :elist (cdr toks))
       (declare (ignorable ok es r))
       (let ((c17 (fp-steps :elist (cdr toks)))) (if ok (+ 1 c17) (+ 1 c17)))))
     (t (+ 1))))
   (:base
    (cond
     ((not (and (consp toks) (xname-tok-p tk))) (+ 1))
     (t
      (if
       (and (consp (cdr toks)) (equal (cadr toks) (op "(")))
       (mv-let
        (ok as r)
        (fp :args (cddr toks))
        (declare (ignorable ok as r))
        (let
         ((c18 (fp-steps :args (cddr toks))))
         (cond
          ((not ok) (+ 1 c18))
          ((and (consp r) (equal (car r) (op "(")) (<= (len r) (len (cddr toks))))
           (mv-let
            (ok2 g r2)
            (fp :arg (cdr r))
            (declare (ignorable ok2 g r2))
            (let
             ((c19 (fp-steps :arg (cdr r))))
             (if
              (and ok2 (eq (kar g) :tri) (null (kadddr g)) (consp r2) (equal (car r2) (op ")")))
              (+ 1 c19 c18)
              (+ 1 c19 c18)))))
          (t (+ 1 c18)))))
       (+ 1)))))
   (:part
    (cond
     ((not (and (consp toks) (equal tk (op "%")) (consp (cdr toks)) (xname-tok-p (cadr toks)))) (+ 1))
     ((and (consp (cddr toks)) (equal (caddr toks) (op "(")))
      (mv-let
       (ok as r)
       (fp :args (cdddr toks))
       (declare (ignorable ok as r))
       (let ((c20 (fp-steps :args (cdddr toks)))) (if ok (+ 1 c20) (+ 1 c20)))))
     (t (+ 1))))
   (:parts
    (mv-let
     (ok a r)
     (fp :part toks)
     (declare (ignorable ok a r))
     (let
      ((c21 (fp-steps :part toks)))
      (cond
       ((not (and ok (< (len r) (len toks)))) (+ 1 c21))
       ((and (consp r) (equal (car r) (op "%")))
        (mv-let
         (ok2 ps r2)
         (fp :parts r)
         (declare (ignorable ok2 ps r2))
         (let ((c22 (fp-steps :parts r))) (if ok2 (+ 1 c22 c21) (+ 1 c22 c21)))))
       (t (+ 1 c21))))))
   ((:args :args*)
    (cond
     ((not (consp toks)) (+ 1))
     ((equal tk (op ")")) (+ 1))
     ((and (eq nt :args*) (not (equal tk (op ",")))) (+ 1))
     (t
      (let
       ((t1 (if (eq nt :args) toks (cdr toks))))
       (mv-let
        (ok a r)
        (fp :arg t1)
        (declare (ignorable ok a r))
        (let
         ((c23 (fp-steps :arg t1)))
         (if
          (not (and ok (<= (len r) (len t1))))
          (+ 1 c23)
          (mv-let
           (ok2 as r2)
           (fp :args* r)
           (declare (ignorable ok2 as r2))
           (let ((c24 (fp-steps :args* r))) (if ok2 (+ 1 c24 c23) (+ 1 c24 c23)))))))))))
   (:arg
    (cond
     ((not (consp toks)) (+ 1))
     ((kw-head-p toks)
      (mv-let
       (ok e r)
       (fp :expr (cddr toks))
       (declare (ignorable ok e r))
       (let ((c25 (fp-steps :expr (cddr toks)))) (if ok (+ 1 c25) (+ 1 c25)))))
     ((equal tk (op ":"))
      (mv-let
       (ok hs r)
       (fp :tri* (cdr toks))
       (declare (ignorable ok hs r))
       (let ((c26 (fp-steps :tri* (cdr toks)))) (if ok (+ 1 c26) (+ 1 c26)))))
     (t
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c27 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c27))
         ((and (consp r) (equal (car r) (op ":")))
          (mv-let
           (ok2 hs r2)
           (fp :tri* (cdr r))
           (declare (ignorable ok2 hs r2))
           (let ((c28 (fp-steps :tri* (cdr r)))) (if ok2 (+ 1 c28 c27) (+ 1 c28 c27)))))
         (t (+ 1 c27))))))))
   (:tri*
    (mv-let
     (ok hi r)
     (if
      (or (atom toks) (member-equal tk (list (op ":") (op ",") (op ")"))))
      (mv t nil toks)
      (fp :expr toks))
     (declare (ignorable ok hi r))
     (let
      ((c29
        (if (or (atom toks) (member-equal tk (list (op ":") (op ",") (op ")")))) 0 (fp-steps :expr toks))))
      (cond
       ((not (and ok (<= (len r) (len toks)))) (+ 1 c29))
       ((and (consp r) (equal (car r) (op ":")))
        (mv-let
         (ok2 st r2)
         (fp :expr (cdr r))
         (declare (ignorable ok2 st r2))
         (let ((c30 (fp-steps :expr (cdr r)))) (if ok2 (+ 1 c30 c29) (+ 1 c30 c29)))))
       (t (+ 1 c29))))))
   (:elist
    (mv-let
     (ok e r)
     (fp :expr toks)
     (declare (ignorable ok e r))
     (let
      ((c31 (fp-steps :expr toks)))
      (if
       (not (and ok (<= (len r) (len toks))))
       (+ 1 c31)
       (mv-let
        (ok2 es r2)
        (fp :elist* r)
        (declare (ignorable ok2 es r2))
        (let ((c32 (fp-steps :elist* r))) (if ok2 (+ 1 c32 c31) (+ 1 c32 c31))))))))
   (:elist*
    (cond
     ((not (consp toks)) (+ 1))
     ((equal tk (op "]")) (+ 1))
     ((not (equal tk (op ","))) (+ 1))
     (t
      (mv-let
       (ok e r)
       (fp :expr (cdr toks))
       (declare (ignorable ok e r))
       (let
        ((c33 (fp-steps :expr (cdr toks))))
        (if
         (not (and ok (<= (len r) (len (cdr toks)))))
         (+ 1 c33)
         (mv-let
          (ok2 es r2)
          (fp :elist* r)
          (declare (ignorable ok2 es r2))
          (let ((c34 (fp-steps :elist* r))) (if ok2 (+ 1 c34 c33) (+ 1 c34 c33))))))))))
   (otherwise (+ 1)))))

(in-theory (disable member-equal))

(defun fp-d (nt)
  (declare (xargs :guard t))
  (case nt (:base 0) (:part -63) (:parts -62) (:prim 1) (:mult 2) (:add 4) (:l2 6) (:l3 8) (:l4 9) (:and 10) (:or 12) (:equiv 14) (:expr 16)
    ((:arg :tri*) 17) (:args 19) (:elist 18) (otherwise 1)))

(defthm fp-steps-natp (natp (fp-steps nt toks)) :rule-classes :type-prescription)

; each induction step expands exactly the calls its conclusion is about,
; (fp nt toks) and (fp-steps nt toks): the calls inside them are the ones
; its hypotheses answer
(defun case-nts (clause)             ; the step's nts: its hypothesis (eql nt c) or (member nt (c ...))
  (declare (xargs :mode :program))
  (cond ((atom clause) nil)
        ((and (consp (car clause)) (eq (caar clause) (quote not)) (consp (cadar clause))
              (eq (cadr (cadar clause)) (quote nt)) (quotep (caddr (cadar clause))))
         (cond ((member-eq (car (cadar clause)) (quote (eql equal))) (list (caddr (cadar clause))))
               ((member-eq (car (cadar clause)) (quote (member-equal member-eql member-eq)))
                (loop$ for c in (unquote (caddr (cadar clause))) collect (list (quote quote) c)))
               (t (case-nts (cdr clause)))))
        (t (case-nts (cdr clause)))))

(defun cost-step-hint (id clause)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :pool-lst) (quote (1)))
       (equal (len (access clause-id id :case-lst)) 1)
       (equal (access clause-id id :primes) 0)
       (let ((cs (case-nts clause)))
         (list :expand (append (quote ((fp nt toks) (fp-steps nt toks)))
                               (loop$ for c in cs append (list (list (quote fp) c (quote toks)) (list (quote fp-steps) c (quote toks)))))))))

; a successful parse makes at most 32 calls per token it consumes, plus
; fp-d nt: every call of a successful run succeeds, on its own tokens
(defthm fp-cost
  (implies (mv-nth 0 (fp nt toks))
           (<= (+ (fp-steps nt toks) (* 32 (len (mv-nth 2 (fp nt toks)))))
               (+ (* 32 (len toks)) (fp-d nt))))
  :hints (("Goal" :induct (fp-steps nt toks) :in-theory (enable member-equal)) (cost-step-hint id clause)))
