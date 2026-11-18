; fdecl: a scoping unit's specification statements as its entities'
; attributes -- SAVE, DIMENSION, PARAMETER, COMMON, IMPLICIT, * char-length --
; applied to its declarations by fhelp's unit-spec.

(in-package "ACL2")

(include-book "fval")

(set-verify-guards-eagerness 0)

;; R859 SAVE statements (8.6.14) as each entity's SAVE attribute: with one in
;; the declarations, each declaration is split an entity at a time, a saved
;; one's with (:save) among its attributes; SAVE alone saves every entity
(defun save-all-p (ds) (declare (xargs :guard t)) (and (consp ds) (or (equal (car ds) '(:save nil nil)) (save-all-p (cdr ds)))))
(defun save-names (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (append (if (eq (kar (car ds)) :save) (true-list-fix (kaddr (car ds))) nil) (save-names (cdr ds)))))
(defun save-ents (d ents all ns)            ; d a :decl or :tdecl, one per entity
  (declare (xargs :guard t))
  (if (atom ents) nil
    (cons (list (kar d) (kadr d) (if (or all (member-equal (kar (car ents)) ns)) (cons '(:save) (true-list-fix (kaddr d))) (kaddr d))
                (kadddr d) (list (car ents)))
          (save-ents d (cdr ents) all ns))))
(defun save-decls (ds all ns)
  (declare (xargs :guard t))
  (cond ((atom ds) nil)
        ((eq (kar (car ds)) :save) (save-decls (cdr ds) all ns))
        ((member-eq (kar (car ds)) '(:decl :tdecl))
         (append (save-ents (car ds) (kar (kdr (kdr (kdr (kdr (car ds)))))) all ns) (save-decls (cdr ds) all ns)))
        (t (cons (car ds) (save-decls (cdr ds) all ns)))))
;; R851 DIMENSION statements (8.6.6) as each entity's array-spec: a declared
;; entity's declaration split an entity at a time; an undeclared one, in a
;; unit without IMPLICIT NONE, declared by its implicit type (8.7)
(defun implicit-ty (n)
  (declare (xargs :guard t))
  (if (and (stringp n) (consp (coerce n 'list)) (member (car (coerce n 'list)) '(#\i #\j #\k #\l #\m #\n))) :i :r))
;; R866 IMPLICIT statements (8.7): a name typed by the first spec whose
;; letters hold its first letter, else by 8.7p3 (I to N integer, else real)
(defun fchar (s) (declare (xargs :guard t)) (if (and (stringp s) (consp (coerce s (quote list)))) (char-code (car (coerce s (quote list)))) 0))
(defun let-in (c ls)
  (declare (xargs :guard t))
  (if (atom ls) nil
    (let* ((a (fchar (kadr (kar (car ls))))) (b (if (kadr (car ls)) (fchar (kadr (kadr (car ls)))) a)))
      (or (and (<= a (nfix c)) (<= (nfix c) b)) (let-in c (cdr ls))))))
(defun imp-rule (n rules)            ; the type-spec of an implicitly typed n
  (declare (xargs :guard t))
  (cond ((atom rules) (list (if (eq (implicit-ty n) :i) "integer" "real") nil))
        ((let-in (fchar n) (kadr (car rules))) (kar (car rules)))
        (t (imp-rule n (cdr rules)))))
(defun imp-rules (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (append (if (eq (kar (car ds)) :implicit) (true-list-fix (kadr (car ds))) nil) (imp-rules (cdr ds)))))
(defun unit-rules (u) (declare (xargs :guard t)) (imp-rules (kaddr (kaddr u))))
;; R803 entity-decl * char-length (7.4.4.2): each declaration split an entity
;; at a time, an entity with its own length declared CHARACTER * length; a
;; length on another type (8.2 allows it on CHARACTER only) a kind that is no
;; value (me-kind fails)
(defun clen-ts (ts e)
  (declare (xargs :guard t))
  (cond ((not (consp (kdr (kdr (kdr e))))) ts)
        ((equal (kar ts) "character") (list "character" (list :len (kadddr e))))
        (t (list (kar ts) (list nil :bad)))))
(defun clen-ents (d ents)
  (declare (xargs :guard t))
  (if (atom ents) nil
    (cons (list :decl (clen-ts (kadr d) (car ents)) (kaddr d) (kadddr d) (list (car ents))) (clen-ents d (cdr ents)))))
(defun clen-decls (ds)               ; IMPLICIT statements dropped (unit-rules reads them)
  (declare (xargs :guard t))
  (cond ((atom ds) nil)
        ((eq (kar (car ds)) :implicit) (clen-decls (cdr ds)))
        ((eq (kar (car ds)) :decl) (append (clen-ents (car ds) (kar (kdr (kdr (kdr (kdr (car ds))))))) (clen-decls (cdr ds))))
        (t (cons (car ds) (clen-decls (cdr ds))))))
;; R855 PARAMETER statements (8.6.11): in its place, each named constant's
;; declaration, the PARAMETER attribute (8.5.13) and its initialization joined
;; to its earlier type declaration's (then dropped), or by its implicit type
(defun decl-ent1 (d) (declare (xargs :guard t)) (kar (kar (kdr (kdr (kdr (kdr d)))))))   ; a split declaration's entity
(defun par-find (tk ds)
  (declare (xargs :guard t))
  (cond ((atom ds) nil) ((and (eq (kar (car ds)) :decl) (equal (kar (decl-ent1 (car ds))) tk)) (car ds)) (t (par-find tk (cdr ds)))))
(defun par-named (tk ds)             ; tk named by a PARAMETER statement of ds
  (declare (xargs :guard t))
  (and (consp ds) (or (and (eq (kar (car ds)) :parstmt) (member-equal tk (strip-cars (true-list-fix (kadr (car ds)))))) (par-named tk (cdr ds)))))
(defun par-new (es pre imp rules)
  (declare (xargs :guard t))
  (if (atom es) nil
    (let* ((e (car es)) (d (par-find (kar e) pre)) (o (decl-ent1 d)) (rest (par-new (cdr es) pre imp rules)))
      (cond (d (cons (list :decl (kadr d) (cons (list :parameter) (true-list-fix (kaddr d))) t (list (list* (kar o) (kadr o) (kaddr e) (kdr (kdr (kdr o)))))) rest))
            (imp rest)               ; under IMPLICIT NONE, undeclared
            (t (cons (list :decl (imp-rule (kadr (kar e)) rules) (list (list :parameter)) t (list e)) rest))))))
(defun par-decls (ds pre imp rules)  ; pre: the declarations before ds
  (declare (xargs :guard t))
  (cond ((atom ds) nil)
        ((eq (kar (car ds)) :parstmt) (append (par-new (kadr (car ds)) pre imp rules) (par-decls (cdr ds) (cons (car ds) pre) imp rules)))
        ((and (eq (kar (car ds)) :decl) (par-named (kar (decl-ent1 (car ds))) (cdr ds))) (par-decls (cdr ds) (cons (car ds) pre) imp rules))
        (t (cons (car ds) (par-decls (cdr ds) (cons (car ds) pre) imp rules)))))
;; R873 COMMON statements (8.10.2): each common-block object's declaration
;; (its own, by DIMENSION or the COMMON statement's array-spec, or implicit)
;; gets (:save) and (:common b i), b the block's name (nil: blank common), i
;; the object's place in the block's objects in this scoping unit; the i-th
;; object of b is then one variable in every unit when it has the same type,
;; kind and bounds there (fmean's me-ents checks); otherwise fhelp's
;; com-overlay associates it with the block's storage (an equivalence group).
(defun com-objs (is blk)             ; ((tk ss blk) ...) of a COMMON statement's items
  (declare (xargs :guard t))
  (cond ((atom is) nil)
        ((eq (kar (kadr (car is))) :blk)
         (com-objs (cdr is) (if (member-eq (kadr (kadr (car is))) '(:cat :sl)) nil (kadr (kadr (kadr (car is)))))))
        (t (cons (list (kar (kadr (car is))) (kadr (kadr (car is))) blk) (com-objs (cdr is) blk)))))
(defun com-all (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (append (if (eq (kar (car ds)) :common) (com-objs (kadr (car ds)) nil) nil) (com-all (cdr ds)))))
(defun com-number (os counts)        ; ((tk blk i) ...)
  (declare (xargs :guard t))
  (if (atom os) nil
    (let* ((b (kaddr (car os))) (i (nfix (cdr (assoc-equal b counts)))))
      (cons (list (kar (car os)) b i) (com-number (cdr os) (cons (cons b (+ 1 i)) counts))))))
(defun com-dims (os)                 ; the objects with an array-spec, as DIMENSION's entities
  (declare (xargs :guard t))
  (if (atom os) nil (append (if (kadr (car os)) (list (list (kar (car os)) (kadr (car os)) nil)) nil) (com-dims (cdr os)))))
(defun com-ents (d ents coms)
  (declare (xargs :guard t))
  (if (atom ents) nil
    (let ((c (assoc-equal (kar (car ents)) coms)))
      (cons (list (kar d) (kadr d) (if c (list* '(:save) (cons :common (cdr c)) (true-list-fix (kaddr d))) (kaddr d)) (kadddr d) (list (car ents)))
            (com-ents d (cdr ents) coms)))))
(defun com-decls (ds coms)
  (declare (xargs :guard t))
  (cond ((atom ds) nil)
        ((eq (kar (car ds)) :common) (com-decls (cdr ds) coms))
        ((member-eq (kar (car ds)) '(:decl :tdecl))
         (append (com-ents (car ds) (kar (kdr (kdr (kdr (kdr (car ds)))))) coms) (com-decls (cdr ds) coms)))
        (t (cons (car ds) (com-decls (cdr ds) coms)))))
(defun com-implicit (coms declared rules)
  (declare (xargs :guard t))
  (cond ((atom coms) nil)
        ((member-equal (kar (car coms)) declared) (com-implicit (cdr coms) declared rules))
        (t (cons (list :decl (imp-rule (kadr (kar (car coms))) rules) nil t (list (list (kar (car coms)) nil nil)))
                 (com-implicit (cdr coms) (cons (kar (car coms)) declared) rules)))))
(defun ckey (key n attrs)            ; a saved variable's key: its block's place, or its unit's and name
  (declare (xargs :guard t))
  (or (assoc-equal :common (true-list-fix attrs)) (list key n)))
(defun com-fits (f v)                ; a saved variable's value v of the declared f's type, kind and bounds
  (declare (xargs :guard t))
  (if (aval-p f) (and (aval-p v) (equal (list (a-ty f) (a-k f) (a-lbs f) (a-ubs f)) (list (a-ty v) (a-k v) (a-lbs v) (a-ubs v))))
    (and (not (aval-p v)) (equal (scal-ty f) (scal-ty v)) (equal (scal-k f) (scal-k v)))))
(defun dim-specs (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (append (cond ((eq (kar (car ds)) :dimstmt) (true-list-fix (kaddr (car ds))))
                                ((eq (kar (car ds)) :common) (com-dims (com-objs (kadr (car ds)) nil))) (t nil))
                          (dim-specs (cdr ds)))))
(defun dim-of (n dims) (declare (xargs :guard t)) (cond ((atom dims) nil) ((equal (kar (car dims)) n) (car dims)) (t (dim-of n (cdr dims)))))
(defun dim-ents (d ents dims)
  (declare (xargs :guard t))
  (if (atom ents) nil
    (let ((p (dim-of (kar (car ents)) dims)))
      (cons (list (kar d) (kadr d) (kaddr d) (kadddr d) (list (if p (list (kar (car ents)) (kadr p) (kaddr (car ents))) (car ents))))
            (dim-ents d (cdr ents) dims)))))
(defun dim-decls (ds dims)
  (declare (xargs :guard t))
  (cond ((atom ds) nil)
        ((eq (kar (car ds)) :dimstmt) (dim-decls (cdr ds) dims))
        ((member-eq (kar (car ds)) (quote (:decl :tdecl)))
         (append (dim-ents (car ds) (kar (kdr (kdr (kdr (kdr (car ds)))))) dims) (dim-decls (cdr ds) dims)))
        (t (cons (car ds) (dim-decls (cdr ds) dims)))))
(defun ent-names (es) (declare (xargs :guard t)) (if (atom es) nil (cons (kar (car es)) (ent-names (cdr es)))))
(defun decl-names (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil
    (append (if (member-eq (kar (car ds)) (quote (:decl :tdecl))) (ent-names (kar (kdr (kdr (kdr (kdr (car ds))))))) nil) (decl-names (cdr ds)))))
(defun dim-implicit (dims declared rules)
  (declare (xargs :guard t))
  (cond ((atom dims) nil)
        ((member-equal (kar (car dims)) declared) (dim-implicit (cdr dims) declared rules))
        (t (cons (list :decl (imp-rule (kadr (kar (car dims))) rules) nil t (list (car dims)))
                 (dim-implicit (cdr dims) declared rules)))))
