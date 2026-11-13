; fstmt-steps2: fps-steps, the calls fstmt.lisp's parser makes, generated
; from fps (bb regen-steps.bb fstmt.lisp fps fps-steps fp imp-specs): the second half
; of its case clauses here, the first in fstmt-steps.lisp; each fp call
; counted by fp-steps. fstmt-cost.lisp bounds it.

(in-package "ACL2")

(include-book "fstmt-complete")
(include-book "fstmt-steps")

(set-ignore-ok t)

; imp-specs, fps's IMPLICIT parser, counted: one step per letter-spec and
; per implicit-spec, each consuming at least one token
(defun imp-lets-steps (toks)
  (declare (xargs :guard t :measure (len toks) :verify-guards nil))
  (if (not (and (consp toks) (let-tok-p (car toks)))) 1
    (let* ((rng (and (equal (kadr toks) (op "-")) (let-tok-p (kaddr toks))))
           (r (if rng (kdr (kdr (kdr toks))) (cdr toks))))
      (if (equal (kar r) (op ",")) (+ 1 (imp-lets-steps (kdr r))) 1))))
(defun imp-specs-steps (toks)
  (declare (xargs :guard t :measure (len toks) :verify-guards nil))
  (mv-let (ts r) (imp-ts toks)
    (if (not (and ts (equal (kar r) (op "(")))) 1
      (mv-let (ok ls r2) (imp-lets (kdr r)) (declare (ignore ls))
        (if (and ok (equal (kar r2) (op ",")))
            (+ 1 (imp-lets-steps (kdr r)) (imp-specs-steps (kdr r2)))
          (+ 1 (imp-lets-steps (kdr r))))))))
(defthm imp-lets-cost
  (implies (mv-nth 0 (imp-lets toks))
           (<= (+ (imp-lets-steps toks) (len (mv-nth 2 (imp-lets toks)))) (len toks)))
  :rule-classes :linear :hints (("Goal" :induct (imp-lets-steps toks) :in-theory (enable imp-lets))))
(local (defthm len-cdr-imp (implies (consp x) (equal (len (cdr x)) (+ -1 (len x))))))
(defthm imp-specs-cost
  (implies (mv-nth 0 (imp-specs toks))
           (<= (+ (imp-specs-steps toks) (len (mv-nth 2 (imp-specs toks)))) (len toks)))
  :rule-classes :linear :hints (("Goal" :induct (imp-specs-steps toks) :expand ((imp-specs toks)))
                                  ("Subgoal *1/3"
                                   :use ((:instance imp-lets-cost (toks (cdr (mv-nth 1 (imp-ts toks))))) imp-ts-len))))

(defconst *fps-steps-2*
 '((:s-unit
     (mv-let
      (ok pre r)
      (fps :prefix toks)
      (declare (ignorable ok pre r))
      (let
       ((c53 (fps-steps :prefix toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c53))
        ((equal (kar r) (kw "function"))
         (mv-let
          (ok2 fr r2)
          (fps :fn-rest r)
          (declare (ignorable ok2 fr r2))
          (let ((c54 (fps-steps :fn-rest r))) (if ok2 (+ 1 c54 c53) (+ 1 c54 c53)))))
        ((equal (kar r) (kw "subroutine"))
         (if
          (assoc-eq :ts pre)
          (+ 1 c53)
          (mv-let
           (ok2 sr r2)
           (fps :sub-rest r)
           (declare (ignorable ok2 sr r2))
           (let ((c55 (fps-steps :sub-rest r))) (if ok2 (+ 1 c55 c53) (+ 1 c55 c53))))))
        ((and (consp pre) (null (cdr pre)) (eq (kar (car pre)) :ts))
         (let*
          ((ts (kadr (car pre)))
           (c (and (eq (kar (kadr ts)) :len) (equal (kar r) (op ",")) (not (attr-kw-tok-p (kadr r))))))
          (mv-let
           (ok2 dr r2)
           (fps :decl-rest (if c (kdr r) r))
           (declare (ignorable ok2 dr r2))
           (let
            ((c56 (fps-steps :decl-rest (if c (kdr r) r))))
            (cond
             ((not ok2) (+ 1 c56 c53))
             ((not c) (+ 1 c56 c53))
             ((and (null (kar dr)) (null (kadr dr)) (not (attr-kw-tok-p (kar (kar (kaddr dr))))))
              (+ 1 c56 c53))
             (t (+ 1 c56 c53)))))))
        (t (+ 1 c53))))))
    (:fn-rest
     (if
      (and (equal tk (kw "function")) (name-tok-p (kadr toks)) (equal (kaddr toks) (op "(")))
      (mv-let
       (ok ds r)
       (fps :names (kdr (kdr (kdr toks))))
       (declare (ignorable ok ds r))
       (let
        ((c57 (fps-steps :names (kdr (kdr (kdr toks))))))
        (cond
         ((not ok) (+ 1 c57))
         ((and
           (equal (kar r) (kw "result"))
           (equal (kadr r) (op "("))
           (name-tok-p (kaddr r))
           (equal (kadddr r) (op ")")))
          (+ 1 c57))
         (t (+ 1 c57)))))
      (+ 1)))
    (:sub-rest
     (cond
      ((not (and (equal tk (kw "subroutine")) (name-tok-p (kadr toks)))) (+ 1))
      ((equal (kaddr toks) (op "("))
       (mv-let
        (ok ds r)
        (fps :names (kdr (kdr (kdr toks))))
        (declare (ignorable ok ds r))
        (let ((c58 (fps-steps :names (kdr (kdr (kdr toks)))))) (if ok (+ 1 c58) (+ 1 c58)))))
      (t (+ 1))))
    (:decl-rest
     (mv-let
      (ok as r)
      (fps :attrs toks)
      (declare (ignorable ok as r))
      (let
       ((c59 (fps-steps :attrs toks)))
       (if
        (not (and ok (<= (len r) (len toks))))
        (+ 1 c59)
        (let*
         ((dc (and (equal (kar r) (op ":")) (equal (kadr r) (op ":")))) (r1 (if dc (kdr (kdr r)) r)))
         (mv-let
          (ok2 es r2)
          (fps :ents r1)
          (declare (ignorable ok2 es r2))
          (let
           ((c60 (fps-steps :ents r1)))
           (if
            (and ok2 (consp es) (implies (or (consp as) (ents-init-p es)) dc))
            (+ 1 c60 c59)
            (+ 1 c60 c59)))))))))
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
          (let ((c61 (fp-steps :expr t1))) (if (and ok (equal (kar r) (op ")"))) (+ 1 c61) (+ 1 c61)))))))
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
            (let ((c62 (fp-steps :expr t1))) (if (and ok (equal (kar r) (op ")"))) (+ 1 c62) (+ 1 c62)))))))
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
        ((c63 (fps-steps :attr (kdr toks))))
        (if
         (not (and ok (<= (len r) (len (kdr toks)))))
         (+ 1 c63)
         (mv-let
          (ok2 as r2)
          (fps :attrs r)
          (declare (ignorable ok2 as r2))
          (let ((c64 (fps-steps :attrs r))) (if ok2 (+ 1 c64 c63) (+ 1 c64 c63)))))))
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
        (let ((c65 (fps-steps :shapes (kdr (kdr toks))))) (if ok (+ 1 c65) (+ 1 c65)))))
      (t (+ 1))))
    (:shapes
     (mv-let
      (ok ss r)
      (fps :shapes* toks)
      (declare (ignorable ok ss r))
      (let
       ((c66 (fps-steps :shapes* toks)))
       (if (and ok (consp ss) (shapes-same ss (shape-kind (car ss)))) (+ 1 c66) (+ 1 c66)))))
    (:shapes*
     (mv-let
      (ok s r)
      (fps :shape toks)
      (declare (ignorable ok s r))
      (let
       ((c67 (fps-steps :shape toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c67))
        ((equal (kar r) (op ")")) (+ 1 c67))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 ss r2)
          (fps :shapes* (kdr r))
          (declare (ignorable ok2 ss r2))
          (let ((c68 (fps-steps :shapes* (kdr r)))) (if ok2 (+ 1 c68 c67) (+ 1 c68 c67)))))
        (t (+ 1 c67))))))
    (:shape
     (if
      (equal tk (op ":"))
      (+ 1)
      (mv-let
       (ok e r)
       (fp :expr toks)
       (declare (ignorable ok e r))
       (let
        ((c69 (fp-steps :expr toks)))
        (cond
         ((not (and ok (<= (len r) (len toks)))) (+ 1 c69))
         ((not (equal (kar r) (op ":"))) (+ 1 c69))
         ((or (equal (kadr r) (op ",")) (equal (kadr r) (op ")"))) (+ 1 c69))
         (t
          (mv-let
           (ok2 hi r2)
           (fp :expr (kdr r))
           (declare (ignorable ok2 hi r2))
           (let ((c70 (fp-steps :expr (kdr r)))) (if ok2 (+ 1 c70 c69) (+ 1 c70 c69))))))))))
    (:ents
     (mv-let
      (ok e r)
      (fps :ent toks)
      (declare (ignorable ok e r))
      (let
       ((c71 (fps-steps :ent toks)))
       (cond
        ((not (and ok (<= (len r) (len toks)))) (+ 1 c71))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 es r2)
          (fps :ents (kdr r))
          (declare (ignorable ok2 es r2))
          (let ((c72 (fps-steps :ents (kdr r)))) (if ok2 (+ 1 c72 c71) (+ 1 c72 c71)))))
        (t (+ 1 c71))))))
    (:ent
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op "("))
       (mv-let
        (ok ss r)
        (fps :shapes (kdr (kdr toks)))
        (declare (ignorable ok ss r))
        (let
         ((c73 (fps-steps :shapes (kdr (kdr toks)))))
         (cond
          ((not (and ok (<= (len r) (len toks)))) (+ 1 c73))
          ((and (equal (kar r) (op "*")) (len-tok-p (kadr r)))
           (mv-let
            (ok2 i r2)
            (fps :init (kdr (kdr r)))
            (declare (ignorable ok2 i r2))
            (let ((c74 (fps-steps :init (kdr (kdr r))))) (if ok2 (+ 1 c74 c73) (+ 1 c74 c73)))))
          (t
           (mv-let
            (ok2 i r2)
            (fps :init r)
            (declare (ignorable ok2 i r2))
            (let ((c75 (fps-steps :init r))) (if ok2 (+ 1 c75 c73) (+ 1 c75 c73)))))))))
      ((and (equal (kadr toks) (op "*")) (len-tok-p (kaddr toks)))
       (mv-let
        (ok2 i r2)
        (fps :init (kdr (kdr (kdr toks))))
        (declare (ignorable ok2 i r2))
        (let ((c76 (fps-steps :init (kdr (kdr (kdr toks)))))) (if ok2 (+ 1 c76) (+ 1 c76)))))
      (t
       (mv-let
        (ok2 i r2)
        (fps :init (kdr toks))
        (declare (ignorable ok2 i r2))
        (let ((c77 (fps-steps :init (kdr toks)))) (if ok2 (+ 1 c77) (+ 1 c77)))))))
    (:dsets
     (mv-let
      (ok os r)
      (fps :dobjs toks)
      (declare (ignorable ok os r))
      (let
       ((c78 (fps-steps :dobjs toks)))
       (if
        (not (and ok (< (len r) (len toks))))
        (+ 1 c78)
        (mv-let
         (ok2 vs r2)
         (fps :dvals r)
         (declare (ignorable ok2 vs r2))
         (let
          ((c79 (fps-steps :dvals r)))
          (cond
           ((not (and ok2 (< (len r2) (len r)))) (+ 1 c79 c78))
           ((atom r2) (+ 1 c79 c78))
           ((equal (kar r2) (op ","))
            (mv-let
             (ok3 ss r3)
             (fps :dsets (kdr r2))
             (declare (ignorable ok3 ss r3))
             (let ((c80 (fps-steps :dsets (kdr r2)))) (if ok3 (+ 1 c80 c79 c78) (+ 1 c80 c79 c78)))))
           (t
            (mv-let
             (ok3 ss r3)
             (fps :dsets r2)
             (declare (ignorable ok3 ss r3))
             (let ((c81 (fps-steps :dsets r2))) (if ok3 (+ 1 c81 c79 c78) (+ 1 c81 c79 c78))))))))))))
    (:dobjs
     (mv-let
      (ok o r)
      (fps :dobj toks)
      (declare (ignorable ok o r))
      (let
       ((c82 (fps-steps :dobj toks)))
       (cond
        ((not (and ok (< (len r) (len toks)))) (+ 1 c82))
        ((equal (kar r) (op "/")) (+ 1 c82))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 os r2)
          (fps :dobjs (kdr r))
          (declare (ignorable ok2 os r2))
          (let ((c83 (fps-steps :dobjs (kdr r)))) (if ok2 (+ 1 c83 c82) (+ 1 c83 c82)))))
        (t (+ 1 c82))))))
    (:dobj
     (if
      (equal tk (op "("))
      (mv-let
       (ok il r)
       (fp :ilist (kdr toks))
       (declare (ignorable ok il r))
       (let ((c84 (fp-steps :ilist (kdr toks)))) (if ok (+ 1 c84) (+ 1 c84))))
      (mv-let
       (ok p r)
       (fp :prim toks)
       (declare (ignorable ok p r))
       (let ((c85 (fp-steps :prim toks))) (if (and ok (dobj-p p)) (+ 1 c85) (+ 1 c85))))))
    (:dvals
     (mv-let
      (ok v r)
      (fps :dval toks)
      (declare (ignorable ok v r))
      (let
       ((c86 (fps-steps :dval toks)))
       (cond
        ((not (and ok (< (len r) (len toks)))) (+ 1 c86))
        ((equal (kar r) (op "/")) (+ 1 c86))
        ((equal (kar r) (op ","))
         (mv-let
          (ok2 vs r2)
          (fps :dvals (kdr r))
          (declare (ignorable ok2 vs r2))
          (let ((c87 (fps-steps :dvals (kdr r)))) (if ok2 (+ 1 c87 c86) (+ 1 c87 c86)))))
        (t (+ 1 c86))))))
    (:dval
     (if
      (member-equal tk *add-ops*)
      (mv-let
       (ok c r)
       (fp :prim (kdr toks))
       (declare (ignorable ok c r))
       (let ((c88 (fp-steps :prim (kdr toks)))) (if (and ok (dconst-p tk c)) (+ 1 c88) (+ 1 c88))))
      (mv-let
       (ok p r)
       (fp :prim toks)
       (declare (ignorable ok p r))
       (let
        ((c89 (fp-steps :prim toks)))
        (cond
         ((not ok) (+ 1 c89))
         ((equal (kar r) (op "*"))
          (cond
           ((not (drep-p p)) (+ 1 c89))
           ((member-equal (kadr r) *add-ops*)
            (mv-let
             (ok2 c r2)
             (fp :prim (kdr (kdr r)))
             (declare (ignorable ok2 c r2))
             (let
              ((c90 (fp-steps :prim (kdr (kdr r)))))
              (if (and ok2 (dconst-p (kadr r) c)) (+ 1 c90 c89) (+ 1 c90 c89)))))
           (t
            (mv-let
             (ok2 c r2)
             (fp :prim (kdr r))
             (declare (ignorable ok2 c r2))
             (let
              ((c91 (fp-steps :prim (kdr r))))
              (if (and ok2 (dconst-p nil c)) (+ 1 c91 c89) (+ 1 c91 c89)))))))
         ((dconst-p nil p) (+ 1 c89))
         (t (+ 1 c89)))))))
    (:init
     (if
      (equal tk (op "="))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let ((c92 (fp-steps :expr (kdr toks)))) (if ok (+ 1 c92) (+ 1 c92))))
      (+ 1)))
    (:names (if (equal tk (op ")")) (+ 1) (let ((c93 (fps-steps :names1 toks))) (+ 1 c93))))
    (:names1
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op ")")) (+ 1))
      ((equal (kadr toks) (op ","))
       (mv-let
        (ok ns r)
        (fps :names1 (kdr (kdr toks)))
        (declare (ignorable ok ns r))
        (let ((c94 (fps-steps :names1 (kdr (kdr toks))))) (if ok (+ 1 c94) (+ 1 c94)))))
      (t (+ 1))))
    (:onames
     (cond
      ((not (name-tok-p tk)) (+ 1))
      ((equal (kadr toks) (op ","))
       (mv-let
        (ok ns r)
        (fps :onames (kdr (kdr toks)))
        (declare (ignorable ok ns r))
        (let ((c95 (fps-steps :onames (kdr (kdr toks))))) (if (and ok (consp ns)) (+ 1 c95) (+ 1 c95)))))
      (t (+ 1))))
    (:items
     (if
      (equal tk (op ","))
      (mv-let
       (ok e r)
       (fp :expr (kdr toks))
       (declare (ignorable ok e r))
       (let
        ((c96 (fp-steps :expr (kdr toks))))
        (if
         (not (and ok (< (len r) (len toks))))
         (+ 1 c96)
         (mv-let
          (ok2 es r2)
          (fps :items r)
          (declare (ignorable ok2 es r2))
          (let ((c97 (fps-steps :items r))) (if ok2 (+ 1 c97 c96) (+ 1 c97 c96)))))))
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
           ((c98 (fp-steps :expr (kdr (kdr t1)))))
           (if (and ok (equal (kar r) (op ")"))) (+ 1 c98) (+ 1 c98)))))
        ((and (equal (kar t1) (kw "concurrent")) (equal (kadr t1) (op "(")))
         (let
          ((t2 (kdr (kdr t1))))
          (mv-let
           (ok ts r)
           (if (tok-in (kar t2) *type-kws*) (fps :ts t2) (mv t nil t2))
           (declare (ignorable ok ts r))
           (let
            ((c99 (if (tok-in (kar t2) *type-kws*) (fps-steps :ts t2) 0)))
            (cond
             ((not (and ok (<= (len r) (len t2)))) (+ 1 c99))
             ((and
               ts
               (not (and (equal (kar ts) "integer") (equal (kar r) (op ":")) (equal (kadr r) (op ":")))))
              (+ 1 c99))
             (t
              (mv-let
               (ok2 ixs r2)
               (fps :ixs (if ts (kdr (kdr r)) r))
               (declare (ignorable ok2 ixs r2))
               (let
                ((c100 (fps-steps :ixs (if ts (kdr (kdr r)) r))))
                (if ok2 (+ 1 c100 c99) (+ 1 c100 c99))))))))))
        ((and (name-tok-p (kar t1)) (equal (kadr t1) (op "=")))
         (mv-let
          (ok e1 r)
          (fp :expr (kdr (kdr t1)))
          (declare (ignorable ok e1 r))
          (let
           ((c101 (fp-steps :expr (kdr (kdr t1)))))
           (if
            (not (and ok (equal (kar r) (op ","))))
            (+ 1 c101)
            (mv-let
             (ok2 e2 r2)
             (fp :expr (kdr r))
             (declare (ignorable ok2 e2 r2))
             (let
              ((c102 (fp-steps :expr (kdr r))))
              (cond
               ((not ok2) (+ 1 c102 c101))
               ((equal (kar r2) (op ","))
                (mv-let
                 (ok3 e3 r3)
                 (fp :expr (kdr r2))
                 (declare (ignorable ok3 e3 r3))
                 (let
                  ((c103 (fp-steps :expr (kdr r2))))
                  (if ok3 (+ 1 c103 c102 c101) (+ 1 c103 c102 c101)))))
               (t (+ 1 c102 c101)))))))))
        (t (+ 1))))))
    (:prefix
     (cond
      ((tok-in tk *prefix-kws*)
       (mv-let
        (ok ps r)
        (fps :prefix (kdr toks))
        (declare (ignorable ok ps r))
        (let ((c104 (fps-steps :prefix (kdr toks)))) (if ok (+ 1 c104) (+ 1 c104)))))
      ((tok-in tk *type-kws*)
       (mv-let
        (ok ts r)
        (fps :ts toks)
        (declare (ignorable ok ts r))
        (let
         ((c105 (fps-steps :ts toks)))
         (if
          (not (and ok (< (len r) (len toks))))
          (+ 1 c105)
          (mv-let
           (ok2 ps r2)
           (fps :prefix r)
           (declare (ignorable ok2 ps r2))
           (let ((c106 (fps-steps :prefix r))) (if ok2 (+ 1 c106 c105) (+ 1 c106 c105))))))))
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
