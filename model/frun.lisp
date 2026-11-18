; frun: a whole program's meaning, from the text: the modules elaborated in
; order, then the main program (fmean.lisp's evaluation); fortran-run.

(in-package "ACL2")

(include-book "fmean")

(set-verify-guards-eagerness 0)

; ---- a program: the modules elaborated in order, then the main program

(defun ext-frame (units)             ; the external procedures (R503)
  (declare (xargs :guard t))
  (if (atom units) nil
    (if (eq (kar (car units)) :proc)
        (cons (cons (tok-name (hd-name (unit-hd (car units)))) (list :proc (car units) :ext)) (ext-frame (cdr units)))
      (ext-frame (cdr units)))))

(defun me-modules (units mods modenvs gframe st fuel)   ; (mv err mods modenvs st)
  (declare (xargs :guard t :measure (len units) :verify-guards nil))
  (cond ((atom units) (mv nil mods modenvs st))
        ((not (eq (kar (car units)) :module)) (me-modules (cdr units) mods modenvs gframe st fuel))
        (t (let* ((u (car units)) (m (tok-name (hd-name (unit-hd u)))) (spec (unit-spec u))
                  (ufr (use-frames (kar spec) mods)) (env0 (append ufr (list gframe)))
                  (pfr (proc-frame (kadr (unit-int u)) (list :mod m))))
             (mv-let (e fr copies st) (me-decls (kaddr spec) env0 st (list (list mods modenvs gframe) nil) fuel pfr nil m nil)
               (declare (ignore copies))
               (if e (mv e nil nil st)
                 (me-modules (cdr units) (cons (cons m fr) mods) (cons (cons m (cons fr env0)) modenvs) gframe st fuel)))))))
(in-theory (disable me-modules))

; R840 DATA (8.6.7): a main program's DATA statements give its variables
; their initial values before its first statement. Each set's values, a
; repeat r * c as r copies of c, go in order to its objects: a scalar, an
; array element, or a whole array's elements in array element order
; (9.5.3.2), each as by intrinsic assignment. Not yet in the model: a
; data-implied-do, a substring or structure component object (:data).
(defun unit-datas (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (append (if (eq (kar (car ds)) :data) (true-list-fix (kadr (car ds))) nil) (unit-datas (cdr ds)))))
(defun no-datas (ds) (declare (xargs :guard t)) (if (atom ds) nil (if (member-eq (kar (car ds)) '(:data :equiv)) (no-datas (cdr ds)) (cons (car ds) (no-datas (cdr ds))))))
(defun take-n (n xs) (declare (xargs :guard t)) (if (or (zp n) (atom xs)) nil (cons (car xs) (take-n (1- n) (cdr xs)))))
(defun drop-n (n xs) (declare (xargs :guard t)) (if (or (zp n) (atom xs)) xs (drop-n (1- n) (cdr xs))))
(defun data-vals (vs env st cx fuel)   ; (mv err exprs st): the values, repeats expanded
  (declare (xargs :guard t :measure (len vs) :verify-guards nil))
  (if (atom vs) (mv nil nil st)
    (let ((v (car vs)))
      (mv-let (n st) (if (kar v) (me-ev :expr (prim-expr nil (kar v)) env st cx fuel) (mv (vi 4 1) st))
        (cond ((errp n) (mv n nil st))
              ((not (and (ival-scalar n) (<= 0 (v-num n)))) (mv (err :data) nil st))   ; C882: a nonnegative repeat
              (t (mv-let (e es st) (data-vals (cdr vs) env st cx fuel)
                   (mv e (append (repeat-v (v-num n) (prim-expr (kadr v) (kaddr v))) es) st))))))))
(defun data-each (es ty k env st cx fuel)   ; (mv err raws st): each value converted to the type
  (declare (xargs :guard t :measure (len es) :verify-guards nil))
  (if (atom es) (mv nil nil st)
    (mv-let (v st) (me-ev :expr (car es) env st cx fuel)
      (let ((c (if (errp v) v (conv1 ty k v))))
        (if (errp c) (mv c nil st)
          (mv-let (e rs st) (data-each (cdr es) ty k env st cx fuel) (mv e (cons (raw c) rs) st)))))))
(defun data-obj1 (o es env st cx fuel)   ; (mv err es st): one object (:name, :ref), the values left
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (b suf d) (env-lookup (tok-name (kadr o)) env)
    (declare (ignore suf d))
    (cond
     ((atom es) (mv (err :data) nil st))                ; fewer values than objects (8.6.7p4)
     ((and (eq (kar o) :name) (eq (kar b) :var))
      (let* ((loc (kadr b)) (old (st-get loc st)))
        (if (aval-p old)
            (let ((n (len (a-es old))))
              (if (< (len es) n) (mv (err :data) nil st)
                (mv-let (e rs st) (data-each (take-n n es) (a-ty old) (a-k old) env st cx fuel)
                  (if e (mv e nil st)
                    (mv nil (drop-n n es) (st-put loc (mk-arr (a-ty old) (a-k old) (a-lbs old) (a-ubs old) rs) st))))))
          (mv-let (v st) (me-ev :expr (car es) env st cx fuel)
            (let ((c (assign-val old v)))
              (if (errp c) (mv c nil st) (mv nil (cdr es) (st-put loc c st))))))))
     ((eq (kar o) :ref)                                  ; an element: as its assignment statement
      (mv-let (s st) (me-blk (list (list :act (list :assign (kadr o) t (kaddr o) (car es)))) env st cx fuel)
        (if (eq s :normal) (mv nil (cdr es) st) (mv (if (errp s) s (err :data)) nil st))))
     (t (mv (err :data) nil st)))))
; R843 data-implied-do (8.6.7): its objects for each value of its variable (a construct entity, 7.8), in
; order, each (:ev env obj): the env with the variable bound; flattened before the values are given out.
(mutual-recursion
(defun data-flat (os env st cx fuel)   ; (mv err list st)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (cond ((not (posp fuel)) (mv (err :fuel) nil st))
        ((atom os) (mv nil nil st))
        (t (mv-let (e1 l1 st)
             (if (eq (kar (car os)) :ido)
                 (let ((il (cdar os)))
                   (mv-let (k st) (if (ido-ts il) (me-kind (ido-ts il) env st cx (1- fuel)) (mv nil st))
                     (if (errp k) (mv k nil st)
                       (mv-let (ds st) (me-conc-lims (list (ido-ix il)) k env st cx (1- fuel))
                         (if (errp ds) (mv ds nil st) (data-trips (ido-vals il) (car ds) env st cx (1- fuel)))))))
               (mv nil (list (list :ev env (if (eq (kar (car os)) :e) (lone-prim (kadr (car os))) (car os)))) st))
             (if e1 (mv e1 nil st)
               (mv-let (e2 l2 st) (data-flat (cdr os) env st cx (1- fuel))
                 (mv e2 (append l1 l2) st)))))))
(defun data-trips (vals d env st cx fuel)   ; (mv err list st): d = (name kind indices)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (cond ((not (posp fuel)) (mv (err :fuel) nil st))
        ((atom (kaddr d)) (mv nil nil st))
        (t (mv-let (fr locs st) (conc-frame (list (kar d)) (list (kadr d)) (list (car (kaddr d))) st)
             (declare (ignore locs))
             (mv-let (e1 l1 st) (data-flat vals (cons fr env) st cx (1- fuel))
               (if e1 (mv e1 nil st)
                 (mv-let (e2 l2 st) (data-trips vals (list (kar d) (kadr d) (cdr (kaddr d))) env st cx (1- fuel))
                   (mv e2 (append l1 l2) st)))))))))
(defun data-objs (os es env st cx fuel)   ; (mv err es st): the values left
  (declare (xargs :guard t :measure (len os) :verify-guards nil   ; the measure only, the body kept closed
                  :hints (("Goal" :in-theory (union-theories (quote ((:definition len) (:definition o-p) (:definition o<) (:definition o-finp) (:type-prescription len) (:definition not) (:definition natp) (:type-prescription len))) (theory (quote minimal-theory)))))))
  (if (atom os) (mv nil es st)
    (mv-let (e es st) (if (eq (kar (car os)) :ev) (data-obj1 (caddr (car os)) es (cadr (car os)) st cx fuel)
                        (data-obj1 (car os) es env st cx fuel))
      (if e (mv e nil st) (data-objs (cdr os) es env st cx fuel)))))
(defun me-data (sets env st cx fuel)  ; (mv err st)
  (declare (xargs :guard t :measure (len sets) :verify-guards nil
                  :hints (("Goal" :in-theory (union-theories (quote ((:definition len) (:definition o-p) (:definition o<) (:definition o-finp) (:type-prescription len) (:definition not) (:definition natp) (:type-prescription len))) (theory (quote minimal-theory)))))))
  (if (atom sets) (mv nil st)
    (mv-let (e es st) (data-vals (kadr (car sets)) env st cx fuel)
      (if e (mv e st)
        (mv-let (e fos st) (data-flat (kar (car sets)) env st cx fuel)
          (if e (mv e st)
        (mv-let (e es st) (data-objs fos es env st cx fuel)
          (cond (e (mv e st)) (es (mv (err :data) st))       ; more values than objects
                (t (me-data (cdr sets) env st cx fuel))))))))))

;; R870 EQUIVALENCE (8.10.1): a main program's sets, its variables declared,
;; give fequiv.lisp's groups. Each object's storage starts at a unit, an
;; array element's at its offset in array element order (9.5.3.2) times its
;; units; the objects of a set start together (8.10.1.2), sets with a
;; variable in common are one group. Outside the subset, an :error :equiv:
;; a type other than integer, real, logical, complex, character; kinds not
;; all default unless one type and kind (C8110; a character's kind its
;; length); objects that cannot share storage so; an object initialized.
(defun eqv-subs (as env st cx fuel)  ; (mv err idx st): an element's subscripts' values
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count as)))
  (if (atom as) (mv nil nil st)
    (mv-let (v st) (me-ev :expr (kadr (car as)) env st cx fuel)
      (if (not (ival-scalar v)) (mv (err :equiv) nil st)
        (mv-let (e idx st) (eqv-subs (cdr as) env st cx fuel) (mv e (cons (v-num v) idx) st))))))
(defun eqv-tk (v) (declare (xargs :guard t)) (if (aval-p v) (list (a-ty v) (a-k v)) (list (scal-ty v) (scal-k v))))
(defun eqv-item (a fr env st cx fuel)  ; (mv err (loc . unit) st)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((p (lone-prim (kadr a))) (b (cdr (alk (tok-name (kadr p)) fr))) (loc (kadr b)) (v (st-get loc st)))
    (cond ((not (and (eq (kar b) :var) (eq (kaddr b) :rw) (member-eq (car (eqv-tk v)) '(:i :r :l :z :c)))) (mv (err :equiv) nil st))
          ((eq (kar p) :name) (mv nil (cons loc 0) st))
          ((not (aval-p v)) (mv (err :equiv) nil st))
          (t (mv-let (e idx st) (eqv-subs (kaddr p) env st cx fuel)
               (let ((off (and (not e) (arr-offset idx (a-lbs v) (a-ubs v)))))
                 (if (natp off) (mv nil (cons loc (* off (if (eq (a-ty v) :z) 2 1))) st) (mv (err :equiv) nil st))))))))
(defun eqv-union (a b)               ; (mv ok alist): a's (loc . start)s with b's, a loc at one start
  (declare (xargs :guard t))
  (if (atom a) (mv t b)
    (let ((c (alk (kar (car a)) b)))
      (cond ((null c) (eqv-union (cdr a) (cons (car a) b)))
            ((equal (cdr c) (kdr (car a))) (eqv-union (cdr a) b))
            (t (mv nil nil))))))
(defun eqv-shift (s d) (declare (xargs :guard t)) (if (atom s) nil (cons (cons (kar (car s)) (+ (ifix d) (ifix (kdr (car s))))) (eqv-shift (cdr s) d))))
(defun eqv-common (s g) (declare (xargs :guard t)) (cond ((atom s) nil) ((alk (kar (car s)) g) (car s)) (t (eqv-common (cdr s) g))))
(defun eqv-merge (s gs)              ; (mv ok groups): s joined to the groups it meets
  (declare (xargs :guard t :measure (len gs)))
  (if (atom gs) (mv t (list s))
    (let ((c (eqv-common s (car gs))))
      (if (null c) (mv-let (ok r) (eqv-merge s (cdr gs)) (mv ok (cons (car gs) r)))
        (mv-let (ok u) (eqv-union (eqv-shift s (- (ifix (cdr (alk (car c) (car gs)))) (ifix (cdr c)))) (car gs))
          (if ok (eqv-merge u (cdr gs)) (mv nil nil)))))))
(defun eqv-set (as fr env st cx fuel s tks)  ; (mv err s tks st): a set's (loc . start)s, its objects' (ty k)s
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count as)))
  (if (atom as) (mv nil s tks st)
    (mv-let (e it st) (eqv-item (car as) fr env st cx fuel)
      (if e (mv e nil nil st)
        (mv-let (ok s2) (eqv-union (list (cons (car it) (- (cdr it)))) s)
          (if ok (eqv-set (cdr as) fr env st cx fuel s2 (cons (eqv-tk (st-get (car it) st)) tks)) (mv (err :equiv) nil nil st)))))))
(defun eqv-kinds-ok (tks)            ; C8110: numeric or logical all of default kind, or one type and kind
  (declare (xargs :guard t))
  (or (and (subsetp-equal (strip-cars-safe tks) '(:i :r :l :z)) (subsetp-equal (strip-cadrs-safe tks) '(4)))
      (and (consp tks) (subsetp-equal tks (list (car tks))))))
(defun eqv-all-undef (us) (declare (xargs :guard t)) (if (atom us) t (and (eq (kaddr (car us)) :u) (eqv-all-undef (cdr us)))))
(defun eqv-install (g ms st)         ; each member's key (:eqv loc) to the group g, its storage undefined
  (declare (xargs :guard t))
  (cond ((atom ms) st)
        ((not (eqv-all-undef (eqv-units (st-get (kar (car ms)) st)))) (err :equiv))
        (t (eqv-install g (cdr ms) (st-save (list :eqv (kar (car ms))) g st)))))
(defun eqv-installs (gs st)
  (declare (xargs :guard t))
  (cond ((atom gs) st) ((errp st) st) (t (eqv-installs (cdr gs) (eqv-install (car gs) (car gs) st)))))
(defun me-equiv (sets fr env st cx fuel gs)  ; (mv err st)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count sets)))
  (if (atom sets)
      (let ((st2 (eqv-installs gs st))) (if (errp st2) (mv st2 st) (mv nil st2)))
    (mv-let (e s tks st) (eqv-set (car sets) fr env st cx fuel nil nil)
      (if e (mv e st)
        (mv-let (ok gs) (eqv-merge s gs)
          (if (and ok (eqv-kinds-ok tks)) (me-equiv (cdr sets) fr env st cx fuel gs) (mv (err :equiv) st)))))))
(defun unit-equivs (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (append (if (eq (kar (car ds)) :equiv) (true-list-fix (kadr (car ds))) nil) (unit-equivs (cdr ds)))))

(defun lone-prims (as) (declare (xargs :guard t)) (if (atom as) nil (cons (lone-prim (kadr (car as))) (lone-prims (cdr as)))))
(defun eqv-names (ss)                ; an EQUIVALENCE's objects' names
  (declare (xargs :guard t))
  (if (atom ss) nil (append (prim-names (lone-prims (car ss))) (eqv-names (cdr ss)))))
(defun spec-names (ds)               ; the names only a main's DATA or EQUIVALENCE may give (8.7)
  (declare (xargs :guard t))
  (cond ((atom ds) nil)
        ((eq (kar (car ds)) :data) (append (data-names (kadr (car ds))) (spec-names (cdr ds))))
        ((eq (kar (car ds)) :equiv) (append (eqv-names (kadr (car ds))) (spec-names (cdr ds))))
        (t (spec-names (cdr ds)))))
(defun find-main (units)
  (declare (xargs :guard t))
  (if (atom units) nil (if (eq (kar (car units)) :main) (car units) (find-main (cdr units)))))

;; R1111 BLOCK DATA / DATA in an external procedure (8.6.7, 16.2.5): its DATA objects are saved, and
;; defined once before the program's first statement: each such procedure's declarations are elaborated,
;; its DATA applied, and the unit marked (fmean's me-call then skips the DATA). Every DATA object must be declared.
(defun me-proc-datas (units g gframe st fuel)   ; (mv err st)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom units) (mv nil st)
    (let* ((u (car units)) (spec (and (eq (kar u) :proc) (unit-spec u))))
      (if (not (and spec (has-data (kaddr spec))))
          (me-proc-datas (cdr units) g gframe st fuel)
        (let* ((cx (list g nil (unit-formats u))) (ufr (use-frames (kar spec) (car g))) (env0 (append ufr (list gframe)))
               (pfr (proc-frame (kadr (unit-int u)) :host)))
          (mv-let (e fr copies st) (me-decls (no-datas (kaddr spec)) env0 st cx fuel pfr nil (unit-key u) nil)
            (declare (ignore copies))
            (if e (mv e st)
              (if (not (subsetp-equal (data-names (unit-datas (kaddr spec))) (strip-cars (alist-fix fr)))) (mv (err :data) st)
                (mv-let (e st) (me-data (unit-datas (kaddr spec)) (cons fr env0) st cx fuel)
                  (if e (mv e st)
                    (mv-let (loc st) (st-new (vi 4 0) st)
                      (me-proc-datas (cdr units) g gframe (st-save (data-marker (unit-key u)) loc st) fuel)))))))))))) 
(defun me-program (units in fuel)    ; (mv status lines): in the input's records
  (declare (xargs :guard t :verify-guards nil))
  (let ((gframe (ext-frame units)) (st (mk-st8 nil 0 nil nil nil nil (cons in nil) nil)) (main (find-main units)))
    (mv-let (e mods modenvs st) (me-modules units nil nil gframe st fuel)
      (cond (e (mv e (close-lines (reverse (true-list-fix (st-out st))))))
            ((not main) (mv (err :syntax) nil))
            (t (mv-let (e st) (me-proc-datas units (list mods modenvs gframe) gframe st fuel)
                 (if e (mv e (close-lines (reverse (true-list-fix (st-out st)))))
                 (let* ((g (list mods modenvs gframe)) (cx (list g nil (unit-formats main))) (spec (unit-spec main))
                      (ufr (use-frames (kar spec) mods)) (env0 (append ufr (list gframe)))
                      (pfr (proc-frame (kadr (unit-int main)) :host)))
                 (mv-let (e fr copies st) (me-decls (no-datas (kaddr spec)) env0 st cx fuel pfr nil (unit-key main) nil)
                   (declare (ignore copies))
                   (if e (mv e (close-lines (reverse (true-list-fix (st-out st)))))
                     (mv-let (fr st) (if (kadr spec) (mv fr st)          ; IMPLICIT NONE, or implicit typing (8.7)
                                       (implicit-vars (append (used-names (unit-exec main)) (spec-names (kaddr spec))) fr env0 st (unit-rules main)))
                       (mv-let (s st) (mv-let (e st) (mv-let (e st) (me-equiv (unit-equivs (kaddr spec)) fr (cons fr env0) st cx fuel nil)
                                                       (if e (mv e st) (me-data (unit-datas (kaddr spec)) (cons fr env0) st cx fuel)))
                                        (mv-let (sfr exec) (sfun-frame (unit-exec main) fr st (unit-rules main) (kadr spec))
                                          (if e (mv e st) (me-blk exec (if sfr (list* sfr fr env0) (cons fr env0)) st cx fuel))))
                         (mv (cond ((equal s (err :stop)) :stop) ((eq s :normal) :normal)
                                   ((errp s) s) ((goto-p s) (err :label)) (t (err :syntax)))
                             (close-lines (reverse (true-list-fix (st-out st)))))))))))))))))
(in-theory (disable me-program))

; ---- the text to its answer

; F77 12.8.2.3: an io-implied-do output item "( list , v = a , b [, c] )" is written as the
; array constructor [ ( list , v = a , b [, c] ) ], whose values come in order each trip
; (the same ac-implied-do); the token rewrite is before the one fps read, so fps-sound covers it.
(defun paren-end (toks d)             ; the tokens through the ")" closing depth d, or nil
  (declare (xargs :guard t :measure (len toks)))
  (cond ((atom toks) nil)
        ((equal (car toks) (op "(")) (let ((r (paren-end (cdr toks) (1+ d)))) (and r (1+ r))))
        ((equal (car toks) (op ")")) (if (= d 1) 1 (let ((r (paren-end (cdr toks) (1- d)))) (and r (1+ r)))))
        (t (let ((r (paren-end (cdr toks) d))) (and r (1+ r))))))
(defun eq-at-1 (toks d)               ; a "=" at paren depth 1 before the close
  (declare (xargs :guard t :measure (len toks)))
  (cond ((atom toks) nil)
        ((equal (car toks) (op "(")) (eq-at-1 (cdr toks) (1+ d)))
        ((equal (car toks) (op ")")) (and (< 1 d) (eq-at-1 (cdr toks) (1- d))))
        ((equal (car toks) (op "=")) (or (= d 1) (eq-at-1 (cdr toks) d)))
        (t (eq-at-1 (cdr toks) d))))
(defthm len-nthcdr-lt
  (implies (and (posp n) (<= n (len x))) (< (len (nthcdr n x)) (len x)))
  :hints (("Goal" :induct (nthcdr n x))) :rule-classes :linear)
(defun io-items (toks start d rd)     ; start: at an item start; d: paren depth; rd: a READ's, rdido_([ ... ]) (fmean me-ritems)
  (declare (xargs :guard t :measure (len toks)))
  (let ((n (and start (equal (car toks) (op "(")) (paren-end toks 0))))
    (cond ((atom toks) nil)
          ((and n (posp n) (<= n (len toks)) (eq-at-1 (take n toks) 0)
                (or (= n (len toks)) (equal (nth n toks) (op ","))))
           (append (if rd (list (kw "rdido_") (op "(") (op "[")) (list (op "["))) (take n toks) (if rd (list (op "]") (op ")")) (list (op "]")))
                   (io-items (nthcdr n toks) nil d rd)))
          (t (cons (car toks)
                   (io-items (cdr toks) (and (= d 0) (equal (car toks) (op ",")))  
                             (cond ((equal (car toks) (op "(")) (1+ d)) ((equal (car toks) (op ")")) (if (< 0 d) (1- d) 0)) (t d)) rd))))))
;; F77 15.8.4 alternate return (see fhelp altret-p): * dummies, *label actuals, RETURN e
(defun alt-subst (toks prev d k hdr)  ; at paren depth 1 after ( or , : a * (SUBROUTINE) or *label (CALL) is a name
  (declare (xargs :guard t :verify-guards nil :measure (len toks)))
  (if (atom toks) nil
    (let ((tk (car toks)))
      (cond ((and (equal tk (op "*")) (equal d 1) (or (equal prev (op "(")) (equal prev (op ","))))
             (cond ((and (eq hdr :call) (consp (cdr toks)) (label-int-p (cadr toks)))
                    (let ((nm (kw (concatenate 'string "altlab_" (cadr (cadr toks))))))
                      (cons nm (alt-subst (cddr toks) nm d k hdr))))
                   ((eq hdr :sub)
                    (let ((nm (kw (concatenate 'string "altstar_" (coerce (explode-nonnegative-integer k 10 nil) 'string)))))
                      (cons nm (alt-subst (cdr toks) nm d (1+ k) hdr))))
                   (t toks)))
            (t (cons tk (alt-subst (cdr toks) tk (cond ((equal tk (op "(")) (1+ d)) ((equal tk (op ")")) (if (< 0 d) (1- d) 0)) (t d)) k hdr)))))))
(defun alt-sugar (toks)
  (declare (xargs :guard t :verify-guards nil :measure (len toks)))
  (cond ((and (equal (car toks) (kw "return")) (consp (cdr toks)))
         (append (list (kw "call") (kw "altret_") (op "(")) (cdr toks) (list (op ")"))))
        ((and (equal (car toks) (kw "if")) (equal (cadr toks) (op "(")))
         (let ((n (paren-end (cdr toks) 0)))
           (if (and (natp n) (< (1+ n) (len toks)))
               (append (take (1+ n) toks) (alt-sugar (nthcdr (1+ n) toks)))
             toks)))
        ((equal (car toks) (kw "call")) (alt-subst toks nil 0 1 :call))
        ((equal (car toks) (kw "subroutine")) (alt-subst toks nil 0 1 :sub))
        (t toks)))
;; F77 12.2.4 FMT= a character variable, by token sugar (see fmean fv-name): in READ/WRITE ( ... ), a name that is
;; the second positional control item or follows FMT= becomes the format token (:char <control-A> name)
(defun fv-tok (nm) (list :char (concatenate 'string (coerce (list (code-char 1)) 'string) nm)))
(defun fmt-var-sub (toks pp prev d commas)   ; toks from just after the "(" (d: paren depth, 1 inside the control list)
  (declare (xargs :guard t :verify-guards nil :measure (len toks)))
  (if (atom toks) nil
    (let ((tk (car toks)))
      (if (and (equal d 1) (eq (kar tk) :name) (stringp (kadr tk)) (consp (cdr toks))
               (member-equal (cadr toks) (list (op ",") (op ")")))
               (or (and (equal prev (op ",")) (equal commas 1)) (and (equal prev (op "=")) (equal pp (kw "fmt")))))
          (cons (fv-tok (kadr tk)) (fmt-var-sub (cdr toks) prev tk d commas))
        (cons tk (fmt-var-sub (cdr toks) prev tk (cond ((equal tk (op "(")) (1+ d)) ((equal tk (op ")")) (if (< 0 d) (1- d) 0)) (t d))
                              (if (and (equal d 1) (equal tk (op ","))) (1+ commas) commas)))))))
;; F77 12.10.4 REWIND / BACKSPACE / ENDFILE (END FILE) u, or ( [UNIT =] u ), as CALL rewind_ ( u ) etc. (fmean pos-op)
(defun pos-sugar (toks)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((k (cond ((member-equal (car toks) (list (kw "rewind") (kw "backspace") (kw "endfile"))) 1)
                  ((and (equal (car toks) (kw "end")) (equal (cadr toks) (kw "file"))) 2)
                  (t nil)))
         (nm (if (eql k 2) "endfile" (kadr (car toks))))
         (r (nthcdr (nfix k) toks))
         (pr (and (equal (car r) (op "(")) (equal (paren-end r 0) (len r))))
         (r (if pr (butlast (cdr r) 1) r)))
    (if (and k (stringp nm) (consp r) (or pr (not (member-equal (op "=") r))))   ; ( [UNIT=] u, ERR=, IOSTAT= ): fmean fc-args
        (append (list (kw "call") (kw (concatenate 'string nm "_")) (op "(")) r (list (op ")")))
      toks)))
;; F77 12.10.1-3 OPEN, CLOSE, INQUIRE ( specs ) as CALL open_ ( specs ) etc.: each spec an actual argument,
;; keyword = expression (fmean fc-args), so FILE=, RECL=, ERR= take any expression
(defun file-sugar (toks)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (member-equal (car toks) (list (kw "open") (kw "close") (kw "inquire"))) (stringp (kadr (car toks)))
           (equal (cadr toks) (op "(")) (equal (paren-end (cdr toks) 0) (len (cdr toks))))
      (list* (kw "call") (kw (concatenate 'string (kadr (car toks)) "_")) (cdr toks))
    toks))
;; F77 12.9.5 unformatted READ/WRITE ( u [, END = l] ) and END= with a * or label format, by token sugar (fmean
;; ef-fmt): the format becomes the token (:char <control-C> l <control-C> f), f U, *, L and the label, or C and the literal's text.
;; Only a positional unit first; otherwise (and with FMT=) the tokens are left as they are.
(defun ctl-split (toks d cur)        ; the control list's items at paren depth 0, each a token list
  (declare (xargs :guard t :verify-guards nil :measure (len toks)))
  (cond ((atom toks) (list (reverse cur)))
        ((and (eql d 0) (equal (car toks) (op ","))) (cons (reverse cur) (ctl-split (cdr toks) d nil)))
        (t (ctl-split (cdr toks) (cond ((equal (car toks) (op "(")) (1+ (nfix d))) ((equal (car toks) (op ")")) (nfix (1- (nfix d)))) (t d)) (cons (car toks) cur)))))
(defun ctl-join (its) (declare (xargs :guard t :verify-guards nil)) (if (atom its) nil (append (car its) (if (consp (cdr its)) (cons (op ",") (ctl-join (cdr its))) nil))))
(defun kw-item-p (it) (declare (xargs :guard t)) (and (eq (kar (kar it)) :name) (equal (kadr it) (op "="))))
(defun kw-item (nm its) (declare (xargs :guard t)) (cond ((atom its) nil) ((and (kw-item-p (car its)) (equal (kar (car its)) (kw nm))) (car its)) (t (kw-item nm (cdr its)))))
;; F77 12.8.3 REC= and 12.7.1 ERR= the same way, UNIT= and FMT= written with keywords too: the unit becomes
;; rec_ ( u , r ) (fmean rec-args), ERR='s label the format token's second part, (:char ^C end ^C err ^C f)
(defun ctl-lab (it) (declare (xargs :guard t)) (if it (if (and (label-int-p (kaddr it)) (null (cdddr it))) (cadr (kaddr it)) nil) ""))
(defun ctl-sugar (toks)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((its (ctl-split toks 0 nil)) (upos (not (kw-item-p (car its))))
         (u (if upos (car its) (cddr (kw-item "unit" its))))
         (r1 (if upos (cdr its) its))
         (fpos (and upos (consp r1) (not (kw-item-p (car r1)))))
         (f (if fpos (car r1) (cddr (kw-item "fmt" r1))))
         (en (kw-item "end" r1)) (er (kw-item "err" r1)) (rc (kw-item "rec" r1))
         (rest (if fpos (cdr r1) r1))
         (rest (remove-equal (kw-item "unit" rest) (remove-equal (kw-item "fmt" rest) (remove-equal en (remove-equal er (remove-equal rc rest))))))
         (desc (cond ((null f) "U") ((equal f (list (op "*"))) "*")
                     ((and (consp f) (null (cdr f)) (label-int-p (car f))) (concatenate 'string "L" (cadr (car f))))
                     ((and (consp f) (null (cdr f)) (char-tok-p (car f))) (concatenate 'string "C" (cadr (car f)))) (t nil)))
         (el (ctl-lab en)) (erl (ctl-lab er)) (c3 (coerce (list (code-char 3)) 'string)))
    (if (or (null u) (and f (null en) (null er) (null rc)) (null desc) (not (stringp el)) (not (stringp erl)) (and rc (null (cddr rc)))) toks
      (ctl-join (list* (if rc (append (list (kw "rec_") (op "(")) u (list (op ",")) (cddr rc) (list (op ")"))) u)
                       (list (list :char (concatenate 'string c3 el c3 erl c3 desc))) rest)))))
(defun io-sugar (toks0)                ; WRITE ( ios ) items; BLOCK DATA [name] as a subroutine
  (declare (xargs :guard t))
  (let ((toks (file-sugar (pos-sugar (alt-sugar toks0)))))
  (if (and (equal (car toks) (kw "block")) (equal (cadr toks) (kw "data")) (atom (cdddr toks)))   ; R1116 (F77 16.2.5): its DATA is me-proc-datas'
      (list (kw "subroutine") (kw (if (and (consp (cddr toks)) (stringp (kadr (caddr toks)))) (concatenate 'string "blockdata_" (kadr (caddr toks))) "blockdata_")))
  (if (and (member-equal (car toks) (list (kw "write") (kw "read"))) (equal (cadr toks) (op "(")))
      (let ((n (paren-end (cdr toks) 0)))
        (if (and n (<= (1+ n) (len toks)))
            (append (list (car toks) (op "(")) (fmt-var-sub (append (ctl-sugar (take (- n 2) (cddr toks))) (list (op ")"))) nil (op "(") 1 0)
                    (io-items (nthcdr (1+ n) toks) t 0 (equal (car toks) (kw "read"))))
          toks))
    toks))))

;; F77 15.7 ENTRY, by statement-list sugar before parsing (like alt-sugar): each ENTRY e(args) becomes its own
;; unit: the header with e and args, the unit's specification statements, then the statements after the ENTRY.
;; ponytail: copies share no locals with the original unit (FCVS keeps shared state in COMMON), and the
;; entry's result takes the header's type prefix; add SAVEd-local sharing if a test needs it.
(defun entry-split (st)              ; ENTRY statement -> (name . rest), else nil
  (declare (xargs :guard t))
  (let* ((s (kadr (car st))) (e (and (consp st) (equal (kar (car st)) :name) (stringp s)
          (cond ((and (equal s "entry") (consp (cdr st)) (equal (kar (cadr st)) :name) (stringp (kadr (cadr st)))) (cons (kadr (cadr st)) (cddr st)))
                ((and (< 5 (length s)) (equal (subseq s 0 5) "entry")) (cons (subseq s 5 (length s)) (cdr st)))))))
    (and e (or (null (cdr e)) (and (equal (cadr e) (op "(")) (true-listp (cdr e)) (equal (car (last (cdr e))) (op ")")) (not (member-equal (op "=") (cdr e))))) e)))
(defun spec-stmt-p (st)
  (declare (xargs :guard t))
  (and (consp st) (equal (kar (car st)) :name)
       (member-equal (kadr (car st)) '("integer" "real" "double" "complex" "logical" "character" "dimension" "common" "equivalence" "external" "intrinsic" "implicit" "parameter" "save")) t))
(defun drop-entries (ss) (declare (xargs :guard t)) (if (atom ss) nil (if (entry-split (car ss)) (drop-entries (cdr ss)) (cons (car ss) (drop-entries (cdr ss))))))
(defun drop-specs (ss) (declare (xargs :guard t)) (if (atom ss) nil (if (spec-stmt-p (car ss)) (drop-specs (cdr ss)) (cons (car ss) (drop-specs (cdr ss))))))
(defun keep-specs (ss) (declare (xargs :guard t)) (if (atom ss) nil (if (spec-stmt-p (car ss)) (cons (car ss) (keep-specs (cdr ss))) (keep-specs (cdr ss)))))
(defun take-to-function (hdr) (declare (xargs :guard t)) (if (or (atom hdr) (equal (car hdr) (kw "function"))) nil (cons (car hdr) (take-to-function (cdr hdr)))))
(defun entry-hdr (hdr e)             ; hdr's kind (type prefix kept) with the entry's name and arguments
  (declare (xargs :guard t))
  (if (equal (car hdr) (kw "subroutine")) (list* (kw "subroutine") (kw (car e)) (cdr e))
    (append (take-to-function hdr) (list (kw "function") (kw (car e))) (cdr e))))
(defun entry-units (hdr spec body)   ; one unit per ENTRY in body (body ends with the END)
  (declare (xargs :guard t))
  (if (atom body) nil
    (let ((e (entry-split (car body))))
      (if e (append (list (entry-hdr hdr e)) spec (drop-specs (drop-entries (cdr body))) (entry-units hdr spec (cdr body)))
        (entry-units hdr spec (cdr body))))))
(defun entry-unit (us)               ; us: the unit's statements through its END
  (declare (xargs :guard t))
  (let ((hdr (car us)) (body (cdr us)))
    (if (and (or (equal (car hdr) (kw "subroutine")) (member-equal (kw "function") hdr))
             (not (equal (drop-entries body) body)))
        (append (list hdr) (drop-entries body) (entry-units hdr (keep-specs body) body))
      us)))
(defun entry-sugar1 (ss cur)
  (declare (xargs :guard t :verify-guards nil :measure (len ss)))
  (cond ((atom ss) (reverse cur))
        ((equal (car ss) (list (kw "end"))) (append (entry-unit (reverse (cons (car ss) cur))) (entry-sugar1 (cdr ss) nil)))
        (t (entry-sugar1 (cdr ss) (cons (car ss) cur)))))
;; F77 3.4: a label on a specification statement (12 INTEGER X, 22 DATA ...) names nothing a statement can
;; use, so it is dropped before parsing (FM200).
(defun unlabel-specs (ss)           ; a label is a statement of its own, ((:lab d)), before the statement
  (declare (xargs :guard t))
  (cond ((atom ss) nil)
        ((and (consp (car ss)) (label-tok-p (caar ss)) (null (cdar ss)) (consp (cdr ss))
              (or (spec-stmt-p (cadr ss)) (and (consp (cadr ss)) (equal (kar (caadr ss)) :name) (equal (kadr (caadr ss)) "data"))))
         (unlabel-specs (cdr ss)))
        (t (cons (car ss) (unlabel-specs (cdr ss))))))
(defun entry-sugar (ss) (declare (xargs :guard t :verify-guards nil)) (entry-sugar1 (unlabel-specs ss) nil))

(defun parse-stmts (ss)              ; each statement parsed whole, or nil
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ss) (mv t nil)
    (mv-let (ok s r) (fps :stmt (io-sugar (car ss)))
      (if (not (and ok (null r))) (mv nil (car ss))
        (mv-let (ok2 rest) (parse-stmts (cdr ss)) (if ok2 (mv t (cons s rest)) (mv nil rest)))))))

(defun fortran-parse (text fixed)    ; (mv ok units-or-the-bad-statement); fixed: fixed source form
  (declare (xargs :guard (stringp text) :verify-guards nil))
  (mv-let (ok ss) (parse-stmts (entry-sugar (if fixed (flex-fixed text) (flex text))))
    (if (not ok) (mv nil ss)
      (mv-let (ok2 us r) (fpu :program (ldo-sugar ss nil nil))
        (if (and ok2 (null r)) (mv t us) (mv nil (kar r)))))))

(defun fortran-run-in (text fixed in fuel)  ; (list status lines), or (list (:error :parse) stmt); in the input's records (strings)
  (declare (xargs :guard (stringp text) :verify-guards nil))
  (mv-let (ok us) (fortran-parse text fixed)
    (if (not ok) (list (err :parse) us)
      (mv-let (s lines) (me-program us in fuel) (list s lines)))))
(defun fortran-run-form (text fixed fuel) (declare (xargs :guard (stringp text) :verify-guards nil)) (fortran-run-in text fixed nil fuel))
(defun fortran-run (text fuel) (declare (xargs :guard (stringp text) :verify-guards nil)) (fortran-run-form text nil fuel))

; what fortran-parse accepts is a program of the grammar: each statement
; one fps read whole (fps-sound), the units fpu read from them (fpu-sound)
(defthm parse-stmts-sound
  (implies (mv-nth 0 (parse-stmts ss)) (stmts-p (mv-nth 1 (parse-stmts ss))))
  :hints (("Goal" :induct (parse-stmts ss) :in-theory (disable io-sugar))
          ("Subgoal *1/2" :use ((:instance fps-sound (nt :stmt) (toks (io-sugar (car ss))))) :in-theory (disable fps-sound io-sugar))))

; a label DO rewritten keeps every statement one of the grammar
(defthm ldo-sugar-stmts
  (implies (stmts-p ss) (stmts-p (ldo-sugar ss stack term)))
  :hints (("Goal" :induct (ldo-sugar ss stack term) :in-theory (enable fgs))))

(defthm fortran-parse-sound
  (implies (mv-nth 0 (fortran-parse text fixed)) (fgu :program (mv-nth 1 (fortran-parse text fixed))))
  :hints (("Goal" :use ((:instance fpu-sound (nt :program)
                                     (toks (ldo-sugar (mv-nth 1 (parse-stmts (entry-sugar (if fixed (flex-fixed text) (flex text))))) nil nil))))
           :in-theory (disable fpu-sound flex flex-fixed parse-stmts ldo-sugar fpu entry-sugar))))
