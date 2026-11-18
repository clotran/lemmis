; fequiv: storage association (19.5.3, 19.6.5, 19.6.6) for EQUIVALENCE
; (8.10.1): st-put, fval's st-put1 then the same storage's other variables.
;
; A value's storage sequence is its numeric storage units (19.5.3.2), each
; (ty k raw): an integer, real or logical scalar one unit, a complex two
; (:r k re) (:r k im), an array its elements' in array element order. An
; equivalence group (frun's me-equiv) is an alist (loc . start), start the
; unit where that variable's storage begins; st-saves keeps it under each
; member's key (:eqv loc). Writing one member rewrites every other from the
; units they share: a unit of another type or kind than the member's element
; makes that element undefined (19.6.6 (1)); a complex takes its two parts
; from two default real units (19.6.5 (1)). Subset (me-equiv checks it):
; integer, real, logical and complex objects all of default kind, or all
; of one type and kind, or all character (a character's unit one character); no
; substring or derived type; a main program's.
; ponytail: a DO CONCURRENT trace logs the write, not its associates'.

(in-package "ACL2")

(include-book "fval")
(set-verify-guards-eagerness 0)   ; as fval

(defun eqv-char-units (cs) (declare (xargs :guard t)) (if (atom cs) nil (cons (list :c 1 (car cs)) (eqv-char-units (cdr cs)))))
(defun eqv-elt-units (ty k e)        ; one element's units: a character of length k, k units of one character each
  (declare (xargs :guard t))
  (if (eq ty :c)
      (if (stringp e) (eqv-char-units (coerce e 'list)) (make-list (nfix k) :initial-element (list :c 1 e)))
  (if (eq ty :z)
      (if (consp e) (list (list :r k (car e)) (list :r k (cdr e))) (list (list :r k e) (list :r k e)))   ; e :u or :pd
    (list (list ty k e)))))
(defun eqv-elts-units (ty k es)
  (declare (xargs :guard t))
  (if (atom es) nil (append (eqv-elt-units ty k (car es)) (eqv-elts-units ty k (cdr es)))))
(defun eqv-units (v)                 ; v's storage sequence
  (declare (xargs :guard t))
  (if (aval-p v) (eqv-elts-units (a-ty v) (a-k v) (a-es v)) (eqv-elt-units (scal-ty v) (scal-k v) (raw v))))

(defun eqv-unit (ty k u)             ; a unit's raw as an element of type ty k, else :u
  (declare (xargs :guard t))
  (if (and (eq (kar u) ty) (equal (kadr u) k)) (kaddr u) :u))
(defun eqv-chars (n us)              ; n characters from the units us, :u (or :pd) if one is not a character
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp n) nil
    (let ((c (eqv-unit :c 1 (kar us))) (r (eqv-chars (1- n) (kdr us))))
      (cond ((characterp c) (if (listp r) (cons c r) r))
            ((and (eq c :pd) (or (eq r :pd) (equal n 1))) :pd)
            (t :u)))))
(defun eqv-elt (ty k us)             ; (mv raw rest): an element of type ty k from the units us
  (declare (xargs :guard t))
  (if (eq ty :c)
      (let ((cs (eqv-chars k us))) (mv (if (listp cs) (coerce cs 'string) cs) (nthcdr (nfix k) us)))
  (if (eq ty :z)
      (let ((a (eqv-unit :r k (kar us))) (b (eqv-unit :r k (kadr us))))
        (mv (cond ((and (eq a :pd) (eq b :pd)) :pd)
                  ((or (member-eq a '(:u :pd)) (member-eq b '(:u :pd))) :u)
                  (t (cons a b)))
            (kdr (kdr us))))
    (mv (eqv-unit ty k (kar us)) (kdr us)))))
(defun eqv-elts (ty k n us)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp n) nil (mv-let (e r) (eqv-elt ty k us) (cons e (eqv-elts ty k (1- n) r)))))
(defun eqv-rebuild (w us)            ; w's variable's value from the units us
  (declare (xargs :guard t))
  (if (aval-p w) (mk-arr (a-ty w) (a-k w) (a-lbs w) (a-ubs w) (eqv-elts (a-ty w) (a-k w) (len (a-es w)) us))
    (mv-let (e r) (eqv-elt (scal-ty w) (scal-k w) us) (declare (ignore r)) (wrap (scal-ty w) (scal-k w) e))))

(defun eqv-splice (us p vs o)        ; the units us, from unit p, with those of vs (from unit o) in place
  (declare (xargs :guard t))
  (if (atom us) nil
    (cons (let ((j (- (ifix p) (ifix o)))) (if (and (<= 0 j) (< j (len vs))) (nth-safe j vs) (car us)))
          (eqv-splice (cdr us) (+ 1 (ifix p)) vs o))))
(defun eqv-sync (ms loc o vs store)  ; the group's members but loc, their units at o now vs
  (declare (xargs :guard t))
  (if (atom ms) store
    (let ((l (kar (car ms))))
      (eqv-sync (cdr ms) loc o vs
                (if (equal l loc) store
                  (let ((w (cdr (alk l store)))) (aput l (eqv-rebuild w (eqv-splice (eqv-units w) (kdr (car ms)) vs o)) store)))))))

(defun st-put (loc v st)             ; loc's value v, and its associates' (fval's st-put1 alone)
  (declare (xargs :guard t))
  (let* ((st (st-put1 loc v st)) (g (cdr (alk (list :eqv loc) (st-saves st)))))
    (if (consp g)
        (mk-st (eqv-sync g loc (cdr (alk loc g)) (eqv-units v) (st-store st)) (st-next st) (st-out st) (st-dovars st) (st-saves st))
      st)))
