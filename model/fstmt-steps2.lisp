; fstmt-steps2: fps-steps, the calls fstmt.lisp's parser makes, generated
; from fps (bb regen-steps.bb fstmt.lisp fps fps-steps fp): the second half
; of its case clauses here, the first in fstmt-steps.lisp; each fp call
; counted by fp-steps. fstmt-cost.lisp bounds it.

(in-package "ACL2")

(include-book "fstmt-complete")
(include-book "fstmt-steps")

(set-ignore-ok t)

(defconst *fps-steps-2*
 '((:ix
     (if
      (and (name-tok-p tk) (equal (kadr toks) (op "=")))
      (mv-let
       (ok lo r)
       (fp :expr (kdr (kdr toks)))
       (declare (ignorable ok lo r))
       (let
        ((c45 (fp-steps :expr (kdr (kdr toks)))))
        (if
         (not (and ok (equal (kar r) (op ":"))))
         (+ 1 c45)
         (mv-let
          (ok2 hi r2)
          (fp :expr (kdr r))
          (declare (ignorable ok2 hi r2))
          (let
           ((c46 (fp-steps :expr (kdr r))))
           (cond
            ((not ok2) (+ 1 c46 c45))
            ((equal (kar r2) (op ":"))
             (mv-let
              (ok3 st r3)
              (fp :expr (kdr r2))
              (declare (ignorable ok3 st r3))
              (let ((c47 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c47 c46 c45) (+ 1 c47 c46 c45)))))
            (t (+ 1 c46 c45))))))))
      (+ 1)))
    (:range
     (if
      (equal tk (op ":"))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let ((c48 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c48) (+ 1 c48))))
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c49 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c49))
         ((not (equal (kar r) (op ":"))) (+ 1 c49))
         ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (+ 1 c49))
         (t
          (mv-let
           (ok2 b r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 b r2))
           (let ((c50 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c50 c49) (+ 1 c50 c49))))))))))
    (:s-unit
     (mv-let
      (ok pre r)
      (fps :prefix toks)
      (declare (ignorable ok pre r))
      (let
       ((c51 (fps-steps :prefix toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c51))
        ((equal (kar r) (kw "function"))
         (mv-let
          (ok2 fr r2)
          (fps :fn-rest r)
          (declare (ignorable ok2 fr r2))
          (let ((c52 (fps-steps :fn-rest r))) (if ok2 (+ 1 c52 c51) (+ 1 c52 c51)))))
        ((equal (kar r) (kw "subroutine"))
         (if
          (assoc-eq :ts pre)
          (+ 1 c51)
          (mv-let
           (ok2 sr r2)
           (fps :sub-rest r)
           (declare (ignorable ok2 sr r2))
           (let ((c53 (fps-steps :sub-rest r))) (if ok2 (+ 1 c53 c51) (+ 1 c53 c51))))))
        ((and (consp pre) (null (cdr pre)) (eq (kar (car pre)) :ts))
         (let*
          ((ts (kadr (car pre)))
           (c (and (eq (kar (kadr ts)) :len) (equal (kar r) (op ",")) (not (attr-kw-tok-p (kadr r))))))
          (mv-let
           (ok2 dr r2)
           (fps :decl-rest (if c (kdr r) r))
           (declare (ignorable ok2 dr r2))
           (let
            ((c54 (fps-steps :decl-rest (if c (kdr r) r))))
            (cond
             ((not ok2) (+ 1 c54 c51))
             ((not c) (+ 1 c54 c51))
             ((and (null (kar dr)) (null (kadr dr)) (not (attr-kw-tok-p (kar (kar (kaddr dr))))))
              (+ 1 c54 c51))
             (t (+ 1 c54 c51)))))))
        (t (+ 1 c51))))))
    (:fn-rest
     (if
      (and (equal tk (kw "function")) (name-tok-p (kadr toks)) (equal (kaddr toks) (op "(")))
      (mv-let
       (ok ds r)
       (fps :names (kdr (kdr (kdr toks))))
       (declare (ignorable ok ds r))
       (let
        ((c55 (fps-steps :names (kdr (kdr (kdr toks))))))
        (cond
         ((not ok) (+ 1 c55))
         ((and
           (equal (kar r) (kw "result"))
           (equal (kadr r) (op "("))
           (name-tok-p (kaddr r))
           (equal (kadddr r) (op ")")))
          (+ 1 c55))
         (t (+ 1 c55)))))
      (+ 1)))
    (:sub-rest
     (cond
      ((not (and (equal tk (kw "subroutine")) (name-tok-p (kadr toks)))) (+ 1))
      ((equal (kaddr toks) (op "("))
       (mv-let
        (ok ds r)
        (fps :names (kdr (kdr (kdr toks))))
        (declare (ignorable ok ds r))
        (let ((c56 (fps-steps :names (kdr (kdr (kdr toks)))))) (if ok (+ 1 c56) (+ 1 c56)))))
      (t (+ 1))))
    (:decl-rest
     (mv-let
      (ok as r)
      (fps :attrs toks)
      (declare (ignorable ok as r))
      (let
       ((c57 (fps-steps :attrs toks)))
       (if
        (not (and ok (<= (len r) (len toks))))
        (+ 1 c57)
        (let*
         ((dc (and (equal (kar r) (op ":")) (equal (kadr r) (op ":")))) (r1 (if dc (kdr (kdr r)) r)))
         (mv-let
          (ok2 es r2)
          (fps :ents r1)
          (declare (ignorable ok2 es r2))
          (let
           ((c58 (fps-steps :ents r1)))
           (if
            (and ok2 (consp es) (implies (or (consp as) (ents-init-p es)) dc))
            (+ 1 c58 c57)
            (+ 1 c58 c57)))))))))
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
          (let ((c59 (fp-steps :expr t1))) (if (and ok (equal (kar r) (op ")"))) (+ 1 c59) (+ 1 c59)))))))
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
            (let ((c60 (fp-steps :expr t1))) (if (and ok (equal (kar r) (op ")"))) (+ 1 c60) (+ 1 c60)))))))
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
        ((c61 (fps-steps :attr (kdr toks))))
        (if
         (not (and ok (<= (len r) (len (kdr toks)))))
         (+ 1 c61)
         (mv-let
          (ok2 as r2)
          (fps :attrs r)
          (declare (ignorable ok2 as r2))
          (let ((c62 (fps-steps :attrs r))) (if ok2 (+ 1 c62 c61) (+ 1 c62 c61)))))))
      (+ 1)))
    (:attr
     (cond
      ((equal tk (kw "parameter")) (+ 1))
      ((equal tk (kw "value")) (+ 1))
      ((equal tk (kw "save")) (+ 1))
      ((equal tk (kw "allocatable")) (+ 1))
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
        (let ((c63 (fps-steps :shapes (kdr (kdr toks))))) (if ok (+ 1 c63) (+ 1 c63)))))
      (t (+ 1))))
    (:shapes
     (mv-let
      (ok ss r)
      (fps :shapes* toks)
      (declare (ignorable ok ss r))
      (let
       ((c64 (fps-steps :shapes* toks)))
       (if (and ok (consp ss) (shapes-same ss (shape-kind (car ss)))) (+ 1 c64) (+ 1 c64)))))
    (:shapes*
     (mv-let
      (ok s r)
      (fps :shape toks)
      (declare (ignorable ok s r))
      (let
       ((c65 (fps-steps :shape toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c65))
        ((equal (kar r) (op ")")) (+ 1 c65))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :shapes* (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c66 (fps-steps :shapes* (kdr r)))) (if ok2 (+ 1 c66 c65) (+ 1 c66 c65)))))
        (t (+ 1 c65))))))
    (:shape
     (if
      (equal tk (op ":"))
      (+ 1)
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c67 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c67))
         ((not (equal (kar r) (op ":"))) (+ 1 c67))
         ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (+ 1 c67))
         (t
          (mv-let
           (ok2 hi r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 hi r2))
           (let ((c68 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c68 c67) (+ 1 c68 c67))))))))))
    (:ents
     (mv-let
      (ok e r)
      (fps :ent toks)
      (declare (ignorable ok e r))
      (let
       ((c69 (fps-steps :ent toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c69))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 es r2)
          (fps :ents (kdr r))
          (declare (ignorable ok2 es r2))
          (let ((c70 (fps-steps :ents (kdr r)))) (if ok2 (+ 1 c70 c69) (+ 1 c70 c69)))))
        (t (+ 1 c69))))))
    (:ent
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok ss r)
        (fps :shapes (kdr (kdr toks)))
        (declare (ignorable ok ss r))
        (let
         ((c71 (fps-steps :shapes (kdr (kdr toks)))))
         (if
          (not (and ok (<= (len r) (len toks))))
          (+ 1 c71)
          (mv-let
           (ok2 i r2)
           (fps :init r)
           (declare (ignorable ok2 i r2))
           (let ((c72 (fps-steps :init r))) (if ok2 (+ 1 c72 c71) (+ 1 c72 c71))))))))
      (t
       (mv-let
        (ok2 i r2)
        (fps :init (kdr toks))
        (declare (ignorable ok2 i r2))
        (let ((c73 (fps-steps :init (kdr toks)))) (if ok2 (+ 1 c73) (+ 1 c73)))))))
    (:init
     (if
      (equal tk (op "="))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let ((c74 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c74) (+ 1 c74))))
      (+ 1)))
    (:names (if (equal tk (op ")")) (+ 1) (let ((c75 (fps-steps :names1 toks))) (+ 1 c75))))
    (:names1
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op ")")) (+ 1))
      ((equal (kadr toks) (op ","))
       (mv-let
        (ok ns r)
        (fps :names1 (kdr (kdr toks)))
        (declare (ignorable ok ns r))
        (let ((c76 (fps-steps :names1 (kdr (kdr toks))))) (if ok (+ 1 c76) (+ 1 c76)))))
      (t (+ 1))))
    (:onames
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op ","))
       (mv-let
        (ok ns r)
        (fps :onames (kdr (kdr toks)))
        (declare (ignorable ok ns r))
        (let ((c77 (fps-steps :onames (kdr (kdr toks))))) (if (and ok (consp ns)) (+ 1 c77) (+ 1 c77)))))
      (t (+ 1))))
    (:items
     (if
      (equal tk (op ","))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let
        ((c78 (fp-steps :expr (kdr toks))))
        (if
         (not (and ok (< (len r) (len toks))))
         (+ 1 c78)
         (mv-let
          (ok2 es r2)
          (fps :items r)
          (declare (ignorable ok2 es r2))
          (let ((c79 (fps-steps :items r))) (if ok2 (+ 1 c79 c78) (+ 1 c79 c78)))))))
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
           ((c80 (fp-steps :expr (kdr (kdr t1)))))
           (if (and ok (equal (kar r) (op ")"))) (+ 1 c80) (+ 1 c80)))))
        ((and (equal (kar t1) (kw "concurrent")) (equal (kadr t1) (op "(")))
         (let
          ((t2 (kdr (kdr t1))))
          (mv-let
           (ok ts r)
           (if (tok-in (kar t2) *type-kws*) (fps :ts t2) (mv t nil t2))
           (declare (ignorable ok ts r))
           (let
            ((c81 (if (tok-in (kar t2) *type-kws*) (fps-steps :ts t2) 0)))
            (cond
             ((not (and ok (<= (len r) (len t2)))) (+ 1 c81))
             ((and
               ts
               (not (and (equal (kar ts) "integer") (equal (kar r) (op ":")) (equal (kadr r) (op ":")))))
              (+ 1 c81))
             (t
              (mv-let
               (ok2 ixs r2)
               (fps :ixs (if ts (kdr (kdr r)) r))
               (declare (ignorable ok2 ixs r2))
               (let
                ((c82 (fps-steps :ixs (if ts (kdr (kdr r)) r))))
                (if ok2 (+ 1 c82 c81) (+ 1 c82 c81))))))))))
        ((and (name-tok-p (kar t1)) (equal (kadr t1) (op "=")))
         (mv-let
          (ok e1 r)
          (fp :expr (kdr (kdr t1)))
          (declare (ignorable ok e1 r))
          (let
           ((c83 (fp-steps :expr (kdr (kdr t1)))))
           (if
            (not (and ok (equal (kar r) (op ","))))
            (+ 1 c83)
            (mv-let
             (ok2 e2 r2)
             (fp :expr (kdr r))
             (declare (ignorable ok2 e2 r2))
             (let
              ((c84 (fp-steps :expr (kdr r))))
              (cond
               ((not ok2) (+ 1 c84 c83))
               ((equal (kar r2) (op ","))
                (mv-let
                 (ok3 e3 r3)
                 (fp :expr (kdr r2))
                 (declare (ignorable ok3 e3 r3))
                 (let ((c85 (fp-steps :expr (kdr r2)))) (if ok3 (+ 1 c85 c84 c83) (+ 1 c85 c84 c83)))))
               (t (+ 1 c84 c83)))))))))
        (t (+ 1))))))
    (:prefix
     (cond
      ((tok-in tk *prefix-kws*)
       (mv-let
        (ok ps r)
        (fps :prefix (kdr toks))
        (declare (ignorable ok ps r))
        (let ((c86 (fps-steps :prefix (kdr toks)))) (if ok (+ 1 c86) (+ 1 c86)))))
      ((tok-in tk *type-kws*)
       (mv-let
        (ok ts r)
        (fps :ts toks)
        (declare (ignorable ok ts r))
        (let
         ((c87 (fps-steps :ts toks)))
         (if
          (not (and ok (< (len r) (len toks))))
          (+ 1 c87)
          (mv-let
           (ok2 ps r2)
           (fps :prefix r)
           (declare (ignorable ok2 ps r2))
           (let ((c88 (fps-steps :prefix r))) (if ok2 (+ 1 c88 c87) (+ 1 c88 c87))))))))
      (t (+ 1))))
    (otherwise (+ 1))))

(encapsulate () (local (in-theory (enable stmt-nt tok-in)))
(make-event
 `(defun
 fps-steps
 (nt toks)
 (declare (xargs :guard t :measure (+ (* 16 (len toks)) (fps-rank nt)) :verify-guards nil))
 (let
  ((tk (kar toks)))
  (if
   (atom toks)
   (if (member-eq nt ' (:attrs :onames :items :ctl :prefix :init :oitems)) (+ 1) (+ 1))
   (case nt ,@*fps-steps-1* ,@*fps-steps-2*))))))

(defthm fps-steps-natp (natp (fps-steps nt toks)) :rule-classes :type-prescription)
