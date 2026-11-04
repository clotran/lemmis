; fio: data transfer on the unit * (12.6, 13): a format specification
; read into edit descriptors (13.3), records written under it (13.4, 13.7,
; 13.8) or list-directed (13.10.4), and records read, formatted (13.7) or
; list-directed (13.10.3). The input is the run's records, given with the
; program (st-in: the records not yet finished, and the position in the
; first one when a nonadvancing READ left it there); the output, the
; state's lines, newest first, the newest (:open buf pos) while a
; nonadvancing WRITE leaves its record open (12.3.4.2).
;
; What the standard leaves to the processor, the model takes from
; gfortran and flang (SUBSET.md): rounding to nearest, ties to even
; (13.7.2.3.8); the optional zero before a decimal point written when the
; field has room (13.7.2.3.1, LZ 13.8.5); B, O and Z of a negative integer
; its two's complement bits in the kind's width (13.7.2.4: the internal
; value's bits); SS the default sign mode (12.5.6.18); a real under G0
; stops with :pd (13.7.5.2.3p3).

(in-package "ACL2")

(include-book "fhelp")

(set-verify-guards-eagerness 0)

(defun wrap-all (ty k es) (if (atom es) nil (cons (wrap ty k (car es)) (wrap-all ty k (cdr es)))))
(defun cx-formats (cx) (kaddr cx))
(defun fd-repeat (n xs) (if (zp n) nil (append xs (fd-repeat (1- n) xs))))
(defun flog10-fix (v e k)            ; e adjusted until 10^e <= v < 10^(e+1), at most k steps
  (declare (xargs :measure (nfix k)))
  (cond ((or (zp k) (not (rationalp v)) (not (integerp e))) e)
        ((< v (expt 10 e)) (flog10-fix v (- e 1) (1- k)))
        ((<= (expt 10 (+ e 1)) v) (flog10-fix v (+ e 1) (1- k)))
        (t e)))
(defun flog10 (v)                    ; floor(log10 v), v a positive rational
  (if (and (rationalp v) (< 0 v)) (flog10-fix v (floor (* (flog2 v) 30103) 100000) 8) 0))
(in-theory (disable flog10))

; ---- the format specification (13.2, 13.3), read into items:
;   (:str cs)  a character string edit descriptor (13.9)
;   (:x n) (:t n) (:tl n) (:tr n)  position editing (13.8.1)
;   (:slash) (:colon)  13.8.2, 13.8.3
;   (:p k)     kP, the scale factor (13.8.6)
;   (:sign m)  S, SP, SS (13.8.4), m :s :sp :ss
;   (:blank m) BN, BZ (13.8.7), m :bn :bz
;   (:i w m) (:b w m) (:o w m) (:z w m)  13.7.2.2, 13.7.2.4 (m nil when absent)
;   (:f w d)   13.7.2.3.2
;   (:e w d e) (:d w d e) (:es w d e) (:en w d e)  13.7.2.3.3-5 (e nil when absent)
;   (:g w d e) 13.7.5 (d nil when absent)
;   (:a w) (:l w)  13.7.4, 13.7.3 (w nil when absent)
;   (:group r items)  r( ... ) (13.4)
;   (:rep r items)    r and one descriptor, Iw repeated: no group
; Blanks mean nothing outside a string (13.3p3); a letter's case nothing.

(defun fd-digits (cs acc)            ; (mv value rest), digits read
  (if (and (consp cs) (characterp (car cs)) (digit-char-p (car cs)))
      (fd-digits (cdr cs) (+ (* 10 (nfix acc)) (nfix (- (char-code (car cs)) 48))))
    (mv acc cs)))
(defthm fd-digits-len (<= (len (mv-nth 1 (fd-digits cs acc))) (len cs)) :rule-classes :linear)
(defun fd-str (cs q acc)             ; a string's characters after its quote q: (mv chars rest)
  (cond ((atom cs) (mv (reverse acc) nil))
        ((equal (car cs) q) (if (and (consp (cdr cs)) (equal (cadr cs) q)) (fd-str (cddr cs) q (cons q acc)) (mv (reverse acc) (cdr cs))))
        (t (fd-str (cdr cs) q (cons (car cs) acc)))))
(defthm fd-str-len (<= (len (mv-nth 1 (fd-str cs q acc))) (len cs)) :rule-classes :linear)
(defun fd-up (c) (if (and (characterp c) (standard-char-p c)) (char-upcase c) c))
(defun fd-blanks (cs) (if (and (consp cs) (member (car cs) '(#\Space #\Tab))) (fd-blanks (cdr cs)) cs))
(defthm fd-blanks-len (<= (len (fd-blanks cs)) (len cs)) :rule-classes :linear)
(defun fd-num (cs)                   ; (mv n-or-nil rest): digits, blanks among them ignored
  (let ((cs (fd-blanks cs)))
    (if (and (consp cs) (characterp (car cs)) (digit-char-p (car cs)))
        (mv-let (n r) (fd-digits cs 0) (mv n r))
      (mv nil cs))))
(defthm fd-num-len (<= (len (mv-nth 1 (fd-num cs))) (len cs)) :rule-classes :linear)

; a data edit descriptor's w[.d][Ee] after its letter: (mv w d e rest)
(defun fd-wde (cs)
  (mv-let (w r) (fd-num cs)
    (let ((r (fd-blanks r)))
      (mv-let (d r) (if (eql (kar r) #\.) (fd-num (cdr r)) (mv nil r))
        (let ((r (fd-blanks r)))
          (if (and (eql (fd-up (kar r)) #\E) (mv-let (e r2) (fd-num (cdr r)) (declare (ignore r2)) e))
              (mv-let (e r2) (fd-num (cdr r)) (mv w d e r2))
            (mv w d nil r)))))))
(defthm fd-wde-len (<= (len (mv-nth 3 (fd-wde cs))) (len cs)) :rule-classes :linear
  :hints (("Goal" :in-theory (disable fd-num fd-blanks))))

; one descriptor named by its letters at cs, n its repeat or the number
; before it (nil when none): (mv item rest), item nil when there is none
(defun fd-one (cs n neg)
  (let* ((c (fd-up (kar cs))) (c2 (fd-up (kadr cs))) (sn (if neg (- (nfix n)) (nfix n))))
    (cond ((eql c #\P) (mv (list :p sn) (cdr cs)))
          ((eql c #\X) (mv (list :x (or n 1)) (cdr cs)))
          ((eql c #\T) (let ((k (cond ((eql c2 #\L) :tl) ((eql c2 #\R) :tr) (t :t))))
                         (mv-let (m r) (fd-num (if (eq k :t) (cdr cs) (cddr cs))) (mv (list k (nfix m)) r))))
          ((and (eql c #\S) (eql c2 #\P)) (mv (list :sign :sp) (cddr cs)))
          ((and (eql c #\S) (eql c2 #\S)) (mv (list :sign :ss) (cddr cs)))
          ((eql c #\S) (mv (list :sign :s) (cdr cs)))
          ((and (eql c #\B) (eql c2 #\N)) (mv (list :blank :bn) (cddr cs)))
          ((and (eql c #\B) (eql c2 #\Z)) (mv (list :blank :bz) (cddr cs)))
          ((and (eql c #\E) (member c2 '(#\S #\N)))
           (mv-let (w d e r) (fd-wde (cddr cs)) (mv (list (if (eql c2 #\S) :es :en) w (nfix d) e) r)))
          ((member c '(#\I #\B #\O #\Z #\F #\E #\D #\G #\A #\L))
           (mv-let (w d e r) (fd-wde (cdr cs))
             (mv (case c (#\I (list :i w d)) (#\B (list :b w d)) (#\O (list :o w d)) (#\Z (list :z w d))
                   (#\F (list :f w (nfix d))) (#\E (list :e w (nfix d) e)) (#\D (list :d w (nfix d) e)) (#\G (list :g w d e))
                   (#\A (list :a w)) (otherwise (list :l w)))
                 r)))
          (t (mv nil cs)))))
(defthm fd-one-len (<= (len (mv-nth 1 (fd-one cs n neg))) (len cs)) :rule-classes :linear
  :hints (("Goal" :in-theory (disable fd-wde fd-num))))

; (fd-group and fd-item-1 are fd-items' own cases, written as macros so
; that the recursion stays one function)
(defmacro fd-group (r n cs)
  `(if (< (len (cdr ,r)) (len ,cs))
       (mv-let (gs r2) (fd-items (cdr ,r))
         (if (< (len r2) (len ,cs))
             (mv-let (is r3) (fd-items r2) (mv (cons (list :group (or ,n 1) gs) is) r3))
           (mv nil nil)))
     (mv nil nil)))
(defmacro fd-item-1 (r n neg cs)
  `(mv-let (it r2) (fd-one ,r ,n ,neg)
     (if (and it (< (len r2) (len ,cs)))
         (mv-let (is r3) (fd-items r2)
           (mv (if (and ,n (< 1 ,n) (not (member-eq (car it) '(:p :x)))) (cons (list :rep ,n (list it)) is) (cons it is)) r3))
       (mv nil nil))))

; the items to the ")" closing the group: (mv items rest)
(defun fd-items (cs)
  (declare (xargs :measure (len cs) :hints (("Goal" :in-theory (disable fd-one fd-num fd-blanks fd-str fd-digits)))))
  (if (atom cs) (mv nil nil)
    (let ((c (car cs)))
      (cond ((member c '(#\Space #\Tab #\,)) (fd-items (cdr cs)))
            ((eql c #\)) (mv nil (cdr cs)))
            ((eql c #\/) (mv-let (is r) (fd-items (cdr cs)) (mv (cons (list :slash) is) r)))
            ((eql c #\:) (mv-let (is r) (fd-items (cdr cs)) (mv (cons (list :colon) is) r)))
            ((or (eql c #\') (eql c #\"))
             (mv-let (s r) (fd-str (cdr cs) c nil)
               (if (< (len r) (len cs)) (mv-let (is r2) (fd-items r) (mv (cons (list :str s) is) r2)) (mv nil nil))))
            (t (let* ((neg (eql c #\-)) (cs1 (if (or neg (eql c #\+)) (cdr cs) cs)))
                 (mv-let (n r) (fd-num cs1)
                   (let ((r (fd-blanks r)))
                     (cond ((eql (kar r) #\() (fd-group r n cs))
                           ((eql (kar r) #\/) (mv-let (is r2) (fd-items (cdr r))
                                                (mv (cons (list :rep (or n 1) (list (list :slash))) is) r2)))
                           (t (fd-item-1 r n neg cs)))))))))))
(in-theory (disable fd-items))

(defun parse-format (s)              ; a format-specification's text, "(" ... ")"
  (let ((cs (if (stringp s) (coerce s 'list) nil)))
    (mv-let (is r) (fd-items (cdr (member #\( cs))) (declare (ignore r)) is)))
(defun fd-expand (is)                ; groups unrolled: the descriptors in order
  (declare (xargs :measure (acl2-count is)))
  (cond ((atom is) nil)
        ((member-eq (kar (car is)) '(:group :rep))
         (append (fd-repeat (nfix (kadr (car is))) (fd-expand (kaddr (car is)))) (fd-expand (cdr is))))
        (t (cons (car is) (fd-expand (cdr is))))))
; reversion (13.4p8): to the group the last right parenthesis but the
; format's own closes, with its repeat factor; with none, to the start
(defun fd-last-group (is) (cond ((atom is) nil) ((fd-last-group (cdr is))) ((eq (kar (car is)) :group) is) (t nil)))
(defun fd-rev (is) (let ((g (fd-last-group is))) (fd-expand (if g g is))))
(defun fd-data-p (it) (and (member-eq (kar it) '(:i :b :o :z :f :e :d :es :en :g :a :l)) t))
(defun fd-has-data (ds) (if (atom ds) nil (or (fd-data-p (car ds)) (fd-has-data (cdr ds)))))

; ---- output editing: a value's characters under one data edit descriptor;
; md = (p sign): the scale factor and the sign mode

(defun fd-pad (cs w)                 ; right-justified in w, or w asterisks; w zero, the minimal width (13.7.2.1)
  (if (eql w 0) cs (if (<= (len cs) (nfix w)) (append (make-list (- (nfix w) (len cs)) :initial-element #\Space) cs)
    (make-list (nfix w) :initial-element #\*))))
(defun fd-fit (cs w)                 ; the optional zero before the point dropped when cs does not fit (13.7.2.3.1)
  (let* ((sg (and (member (kar cs) '(#\- #\+)) t)) (b (if sg (cdr cs) cs)))
    (if (and w (not (eql w 0)) (< (nfix w) (len cs)) (eql (kar b) #\0) (eql (kadr b) #\.))
        (fd-pad (append (if sg (list (car cs)) nil) (cdr b)) w)
      (fd-pad cs w))))
(defun nat-chars (n) (explode-nonnegative-integer (nfix n) 10 nil))
(defun zeros-to (cs m) (if (< (len cs) (nfix m)) (append (make-list (- (nfix m) (len cs)) :initial-element #\0) cs) cs))
(defun md-plus (neg md) (cond (neg (list #\-)) ((eq (kadr md) :sp) (list #\+)) (t nil)))
(defun fd-int (n w m md)             ; Iw.m (13.7.2.2)
  (let ((ds (if (and m (equal n 0) (equal m 0)) nil (zeros-to (nat-chars (abs (ifix n))) m))))
    (fd-pad (append (md-plus (< (ifix n) 0) md) ds) w)))
(defun base-chars (n b acc) (explode-nonnegative-integer (nfix n) b acc))   ; n's digits in base b, upper case
(defun fd-boz (n k b w m)            ; Bw.m, Ow.m, Zw.m (13.7.2.4): the bits of kind k, two's complement
  (let* ((n (ifix n)) (u (if (< n 0) (+ n (expt 2 (* 8 (nfix k)))) n))
         (ds (if (and m (equal u 0) (equal m 0)) nil (zeros-to (if (= u 0) (list #\0) (base-chars u b nil)) m))))
    (fd-pad ds w)))
; to nearest, ties to even: the I/O rounding mode is the processor's
; (13.7.2.3.8); gfortran and flang round the exact value so
(defun round-near (q) (if (rationalp q) (round q 1) 0))
(defun fd-fixed (q d)                ; the digits of |q| to d places, and the point
  (let* ((n (round-near (* (abs q) (expt 10 d)))) (ds (zeros-to (nat-chars n) (+ 1 d)))
         (ip (take (- (len ds) d) ds)) (fp (nthcdr (- (len ds) d) ds)))
    (append ip (cons #\. fp))))
(defun fd-special (x w)              ; an infinity or a NaN (13.7.2.3.1)
  (fd-pad (coerce (cond ((eq x :nan) "NaN") ((eq x :pinf) "Infinity") (t "-Infinity")) 'list) w))
(defun fd-real-f (x w d md)          ; kPFw.d: the value times 10^k (13.8.6)
  (if (not (fl-fin-p x)) (fd-special x w)
    (fd-fit (append (md-plus (fl-neg-p x) md) (fd-fixed (* (fl-val x) (expt 10 (ifix (car md)))) (nfix d))) w)))
(defun fd-exp (x e c)                ; the exponent part: c+zz, +zzz, or Ee digits; nil when it does not fit
  (let ((ds (nat-chars (abs x))) (sg (if (< x 0) #\- #\+)))
    (cond (e (and (<= (len ds) (nfix e)) (list* #\E sg (zeros-to ds e))))
          ((<= (abs x) 99) (list* c sg (zeros-to ds 2)))
          ((<= (abs x) 999) (cons sg ds))
          (t nil))))
; v > 0 to sig significant digits: (mv n ee), n < 10^sig and v ~ n 10^(ee-sig)
(defun fd-sig (v sig)
  (let* ((ee (+ 1 (flog10 v))) (n (round-near (* v (expt 10 (- sig ee))))))
    (if (<= (expt 10 sig) n) (mv (round-near (* v (expt 10 (- sig (+ 1 ee))))) (+ 1 ee)) (mv n ee))))
(defun fd-split (n sig ip)           ; n's sig digits, ip of them before the point
  (let ((ds (zeros-to (nat-chars n) sig))) (append (take ip ds) (cons #\. (nthcdr ip ds)))))
(defun fd-real-e (x w d e md style)  ; kPEw.dEe, ESw.dEe, ENw.dEe (13.7.2.3.3-5)
  (if (not (fl-fin-p x)) (fd-special x w)
    (let* ((v (abs (fl-val x))) (d (nfix d)) (k (if (member-eq style '(:e :d)) (ifix (car md)) 0)))
      (mv-let (mant ex)
        (case style
          (:es (mv-let (n ee) (if (= v 0) (mv 0 1) (fd-sig v (+ d 1))) (mv (fd-split n (+ d 1) 1) (- ee 1))))
          (:en (if (= v 0) (mv (fd-split 0 (+ d 1) 1) 0)
                 (let ((ee0 (+ 1 (flog10 v))))           ; the exponent's multiple of 3, then the digits
                   (let* ((x3 (* 3 (floor (- ee0 1) 3))) (ip (- ee0 x3)))
                     (mv-let (n ee) (fd-sig v (+ d ip))
                       (if (equal ee ee0) (mv (fd-split n (+ d ip) ip) x3)
                         (let* ((x3 (* 3 (floor (- ee 1) 3))) (ip (- ee x3)))
                           (mv-let (n ee) (fd-sig v (+ d ip)) (declare (ignore ee)) (mv (fd-split n (+ d ip) ip) x3)))))))))
          (otherwise (let ((sig (if (<= k 0) (+ d k) (+ d 1))))
                       (mv-let (n ee) (if (= v 0) (mv 0 k) (fd-sig v (nfix sig)))
                         (mv (if (<= k 0) (append (list #\0 #\.) (make-list (- k) :initial-element #\0) (zeros-to (nat-chars n) sig))
                               (fd-split n sig k))
                             (- ee k))))))
        (let ((xp (fd-exp ex e (if (eq style :d) #\D #\E))))
          (if (not xp) (make-list (nfix w) :initial-element #\*)
            (fd-fit (append (md-plus (fl-neg-p x) md) mant xp) w)))))))
(in-theory (disable fd-real-e))
(defun fd-real-g (x w d e md)        ; Gw.dEe for a real (13.7.5.2.3)
  (cond ((not (fl-fin-p x)) (fd-special x w))
        ((or (null d) (eql w 0)) :pd)            ; G0, Gw: the processor's d (and w)
        ((eql d 0) (fd-real-e x w 0 e md :e))
        (t (let ((v (abs (fl-val x))))
             (mv-let (n s) (if (= v 0) (mv 0 1) (fd-sig v d))
               (declare (ignore n))
               (if (or (< s 0) (< d s)) (fd-real-e x w d e md :e)
                 (let ((nb (if (and e (< 0 e)) (+ e 2) 4)))
                   (append (fd-real-f x (- (nfix w) nb) (- d s) (cons 0 (cdr md)))
                           (make-list nb :initial-element #\Space)))))))))
(defun fd-chars (v) (c-chars v))
(defun fd-a (cs w) (if w (if (<= (len cs) (nfix w)) (fd-pad cs w) (take (nfix w) cs)) cs))
(defun fd-data (it v md)             ; the characters, :pd, or an error: a value of a type the descriptor does not edit (13.7.1)
  (let ((w (kadr it)))
    (cond ((pd-p v) :pd)
          ((and (eq (kar v) :u)) (err :undefined))
          ((ival-p v) (case (kar it) ((:i :g) (fd-int (v-num v) w (if (eq (kar it) :i) (kaddr it) nil) md))
                        (:b (fd-boz (v-num v) (v-kind v) 2 w (kaddr it))) (:o (fd-boz (v-num v) (v-kind v) 8 w (kaddr it)))
                        (:z (fd-boz (v-num v) (v-kind v) 16 w (kaddr it))) (otherwise (err :type))))
          ((rval-p v) (case (kar it) (:f (fd-real-f (v-num v) w (kaddr it) md))
                        ((:e :d :es :en) (fd-real-e (v-num v) w (kaddr it) (kadddr it) md (kar it)))
                        (:g (fd-real-g (v-num v) w (kaddr it) (kadddr it) md)) (otherwise (err :type))))
          ((lval-p v) (if (member-eq (kar it) '(:l :g)) (fd-pad (list (if (v-num v) #\T #\F)) (if (eql w 0) 1 w)) (err :type)))
          ((eq (kar v) :c) (if (member-eq (kar it) '(:a :g)) (fd-a (fd-chars v) (if (eql w 0) nil w)) (err :type)))
          (t (err :type)))))
(in-theory (disable fd-data))

; ---- output: records under a format. A record being written is (buf pos
; lim): its characters, the position of the next (0-based), and the left
; tab limit (13.8.1.2); a character placed at pos replaces what is there,
; positions skipped and never filled are blanks (13.8.1.1p4)
(defun rec-put (cs rec)
  (let* ((buf (true-list-fix (kar rec))) (pos (nfix (kadr rec)))
         (pre (if (< (len buf) pos) (append buf (make-list (- pos (len buf)) :initial-element #\Space)) (take pos buf))))
    (list (append pre (true-list-fix cs) (nthcdr (+ pos (len cs)) buf)) (+ pos (len cs)) (kaddr rec))))
(defun rec-move (it rec)             ; T, TL, TR, X
  (let ((pos (nfix (kadr rec))) (lim (nfix (kaddr rec))) (n (nfix (kadr it))))
    (list (kar rec) (case (kar it) (:t (+ lim (max 0 (- n 1)))) (:tl (max lim (- pos n))) (otherwise (+ pos n))) lim)))
(defun rec-line (rec) (list (concatenate 'string "~F" (lx-str (true-list-fix (kar rec))))))
(defun new-rec () (list nil 0 0))

; one pass over descriptors ds: (mv vals rec recs md stop), recs the
; records ended, newest first; stop t when format control terminates
; (13.4p9: a data edit descriptor or a colon with no item left), an error,
; or nil at the format's end
(defun fo-pass (ds vals rec recs md)
  (if (atom ds) (mv vals rec recs md nil)
    (let ((it (car ds)))
      (case (kar it)
        (:str (fo-pass (cdr ds) vals (rec-put (kadr it) rec) recs md))
        ((:x :t :tl :tr) (fo-pass (cdr ds) vals (rec-move it rec) recs md))
        (:slash (fo-pass (cdr ds) vals (new-rec) (cons (rec-line rec) recs) md))
        (:colon (if (atom vals) (mv vals rec recs md t) (fo-pass (cdr ds) vals rec recs md)))
        (:p (fo-pass (cdr ds) vals rec recs (list (kadr it) (kadr md))))
        (:sign (fo-pass (cdr ds) vals rec recs (list (kar md) (kadr it))))
        (:blank (fo-pass (cdr ds) vals rec recs md))
        (otherwise
         (cond ((atom vals) (mv vals rec recs md t))
               (t (let ((cs (fd-data it (car vals) md)))
                    (cond ((errp cs) (mv vals rec recs md cs))
                          ((eq cs :pd) (mv vals rec recs md (err :pd)))
                          (t (fo-pass (cdr ds) (cdr vals) (rec-put cs rec) recs md)))))))))))
(in-theory (disable fo-pass))
; passes until the items are done; the reversion each time the format
; ends with items left, onto a new record (13.4p8); (mv err rec recs)
(defun fo-run (ds rev vals rec recs md k)
  (declare (xargs :measure (nfix k) :hints (("Goal" :in-theory (disable fo-pass)))))   ; k alone decreases
  (mv-let (vs rec recs md stop) (fo-pass ds vals rec recs md)
    (cond ((errp stop) (mv stop rec recs))
          ((or stop (atom vs)) (mv nil rec recs))
          ((or (zp k) (not (fd-has-data rev))) (mv (err :format) rec recs))   ; items left, and no data edit descriptor to take them
          (t (fo-run rev rev vs (new-rec) (cons (rec-line rec) recs) md (1- k))))))
(defun flat-vals (vs)                ; the output list's scalars, arrays in element order (9.5.3.2)
  (if (atom vs) nil
    (append (if (aval-p (car vs)) (wrap-all (a-ty (car vs)) (a-k (car vs)) (a-es (car vs))) (list (car vs)))
            (flat-vals (cdr vs)))))

(defun words (cs acc)                ; the blank-separated words of cs, as strings
  (cond ((atom cs) (if acc (list (lx-str (reverse acc))) nil))
        ((eql (car cs) #\Space) (if acc (cons (lx-str (reverse acc)) (words (cdr cs) nil)) (words (cdr cs) nil)))
        (t (words (cdr cs) (cons (car cs) acc)))))
(defun open-p (line) (eq (kar line) :open))
(defun close-lines (ls)              ; the run's lines, an open record ended
  (if (atom ls) nil (cons (if (open-p (car ls)) (rec-line (cdr (car ls))) (car ls)) (close-lines (cdr ls)))))
(defun st-print-all (lines st) (if (atom lines) st (st-print-all (cdr lines) (st-print (car lines) st))))

; a WRITE or PRINT of values vs on the unit *: fmt :star (list-directed,
; its own records, 13.10.4) or a format's text; adv nil for nonadvancing
; (12.6.2.4). A record left open is continued, its left tab limit where it
; stood (13.8.1.2). (mv status st)
(defun io-write (fmt vs adv st)
  (let* ((out (st-out st)) (op (open-p (kar out))) (rest (if op (cdr out) out)))
    (if (eq fmt :star)
        (mv :normal (st-out-set (cons (append (if op (words (true-list-fix (kadr (car out))) nil) nil) (render vs)) rest) st))
      (let* ((is (parse-format fmt)) (vals (flat-vals vs))
             (rec (if op (let ((o (cdr (car out)))) (list (kar o) (kadr o) (kadr o))) (new-rec))))
        (mv-let (e rec recs) (fo-run (fd-expand is) (fd-rev is) vals rec nil (list 0 :s) (+ 1 (len vals)))
          (if e (mv e st)
            (mv :normal (st-out-set (cons (if adv (rec-line rec) (cons :open rec)) (append recs rest)) st))))))))

; ---- input: st-in is (records . pos): pos nil before a READ begins the
; first record, else the position in it a nonadvancing READ left (12.3.4.2)
(defun in-recs (in) (true-list-fix (kar in)))
(defun in-chars (in) (let ((r (kar (in-recs in)))) (if (stringp r) (coerce r 'list) nil)))
(defun in-pos (in) (nfix (kdr in)))
(defun in-start (in)                 ; the record a READ begins with, or the end of the file (12.11.3)
  (cond ((natp (kdr in)) in) ((consp (in-recs in)) (cons (in-recs in) 0)) (t (err :end))))
(defun in-next (in)                  ; the next record (13.8.2)
  (if (consp (cdr (in-recs in))) (cons (cdr (in-recs in)) 0) (err :end)))
(defun in-done (in adv)              ; after the READ: the record finished unless nonadvancing
  (if adv (cons (cdr (in-recs in)) nil) in))

; a numeric input field's characters (13.7.2.1): blanks dropped (BN) or
; zeros (BZ), then [sign] digits [. digits] [exponent]
(defun fi-blanks (cs bz) (cond ((atom cs) nil) ((eql (car cs) #\Space) (if bz (cons #\0 (fi-blanks (cdr cs) bz)) (fi-blanks (cdr cs) bz)))
                               (t (cons (car cs) (fi-blanks (cdr cs) bz)))))
(defun fi-sign (cs) (cond ((eql (kar cs) #\-) (mv -1 (cdr cs))) ((eql (kar cs) #\+) (mv 1 (cdr cs))) (t (mv 1 cs))))
(defun fi-digs (cs n acc)            ; (mv value count rest)
  (if (and (consp cs) (characterp (car cs)) (digit-char-p (car cs)))
      (fi-digs (cdr cs) (+ 1 (nfix n)) (+ (* 10 (nfix acc)) (digit-char-p (car cs))))
    (mv acc (nfix n) cs)))
(defun fi-int (cs)                   ; [sign] digits, all of cs: the integer, or nil
  (mv-let (sg r) (fi-sign cs)
    (mv-let (v n r) (fi-digs r 0 0)
      (cond ((atom cs) 0) ((and (< 0 n) (atom r)) (* sg v)) (t nil)))))
(defun fi-base (cs b acc)            ; B, O, Z digits (13.7.2.4)
  (if (atom cs) acc
    (let ((d (and (characterp (car cs)) (digit-char-p (car cs) b))))
      (and d (fi-base (cdr cs) b (+ (* b (nfix acc)) d))))))
; a real's field: (mv sign q) q its rational value, or q nil when it is
; not one; d places implied when no point is written, the scale factor p
; when no exponent is (13.7.2.3.2, 13.8.6)
(defun fi-real (cs d p)
  (mv-let (sg r) (fi-sign cs)
    (mv-let (iv in r) (fi-digs r 0 0)
      (mv-let (dot r) (if (eql (kar r) #\.) (mv t (cdr r)) (mv nil r))
        (mv-let (fv fn r) (if dot (fi-digs r 0 0) (mv 0 0 r))
          (let* ((c (fd-up (kar r))) (r (if (member c '(#\E #\D #\Q)) (cdr r) r)) (hasx (or (member c '(#\E #\D #\Q #\+ #\-)))))
            (mv-let (xs r) (fi-sign r)
              (mv-let (xv xn r) (fi-digs r 0 0)
                (let ((m (if dot (+ iv (/ fv (expt 10 fn))) (/ iv (expt 10 (nfix d))))))
                  (cond ((atom cs) (mv 1 0))
                        ((or (consp r) (= 0 (+ in fn)) (and hasx (= xn 0))) (mv sg nil))
                        (hasx (mv sg (* m (expt 10 (* xs xv)))))
                        (t (mv sg (* m (expt 10 (- (ifix p))))))))))))))))
(defun fi-real-val (k sg q)          ; to kind k: nearest, ties to even (13.7.2.3.8), -0 kept
  (if (and (= q 0) (< sg 0)) :nzero (fl-round k (* sg q))))
(defun fi-logical (cs)               ; [blanks] [.] T or F, then anything (13.7.3)
  (let* ((cs (fd-blanks cs)) (cs (if (eql (kar cs) #\.) (cdr cs) cs)) (c (fd-up (kar cs))))
    (cond ((eql c #\T) t) ((eql c #\F) nil) (t :bad))))

; a value of type ty, kind k, from field cs under descriptor it (md = (p
; blank)): a raw value, or an error
(defun fi-field (it cs ty k md)
  (let* ((bz (eq (kadr md) :bz)) (d (kar it)))
    (cond ((eq ty :i)
           (let* ((cs (fi-blanks cs bz))
                  (n (case d ((:i :g) (fi-int cs)) (:b (fi-base cs 2 0)) (:o (fi-base cs 8 0)) (:z (fi-base cs 16 0)) (otherwise :type))))
             (cond ((eq n :type) (err :type)) ((not (integerp n)) (err :input))
                   ((member-eq d '(:b :o :z)) (let ((n (if (<= (expt 2 (+ -1 (* 8 (nfix k)))) n) (- n (expt 2 (* 8 (nfix k)))) n)))
                                                (if (in-kind k n) n (err :input))))
                   ((in-kind k n) n) (t (err :input)))))
          ((eq ty :r)
           (if (not (member-eq d '(:f :e :d :es :en :g))) (err :type)
             (mv-let (sg q) (fi-real (fi-blanks cs bz) (kaddr it) (kar md))
               (if q (fi-real-val k sg q) (err :input)))))
          ((eq ty :l) (if (not (member-eq d '(:l :g))) (err :type) (let ((b (fi-logical cs))) (if (eq b :bad) (err :input) b))))
          (t (err :type)))))
(in-theory (disable fi-field))

; formatted input: the reader rs = (:fmt ds rev md lim taken), taken the
; data edit descriptors this pass has used; one descriptor at a time
(defun fi-take1 (rs in ty k fuel)    ; the next value: (mv raw rs in)
  (declare (xargs :measure (nfix fuel) :hints (("Goal" :in-theory (disable in-next rec-move fi-field fd-has-data in-chars)))))
  (let ((ds (kadr rs)) (rev (kaddr rs)) (md (kadddr rs)) (lim (nfix (kar (cddddr rs)))) (tk (nfix (kadr (cddddr rs)))))
    (cond ((zp fuel) (mv (err :format) rs in))
          ((atom ds)                  ; the format's end with an item left: reversion, a new record
           (if (or (= tk 0) (not (fd-has-data rev))) (mv (err :format) rs in)
             (let ((in (in-next in))) (if (errp in) (mv in rs in) (fi-take1 (list :fmt rev rev md 0 0) in ty k (1- fuel))))))
          (t (let* ((it (car ds)) (rs1 (list :fmt (cdr ds) rev md lim tk)) (pos (in-pos in)))
               (case (kar it)
                 ((:x :t :tl :tr) (fi-take1 rs1 (cons (in-recs in) (kadr (rec-move it (list nil pos lim)))) ty k (1- fuel)))
                 (:slash (let ((in (in-next in))) (if (errp in) (mv in rs in) (fi-take1 (list :fmt (cdr ds) rev md 0 tk) in ty k (1- fuel)))))
                 (:p (fi-take1 (list :fmt (cdr ds) rev (list (kadr it) (kadr md)) lim tk) in ty k (1- fuel)))
                 (:blank (fi-take1 (list :fmt (cdr ds) rev (list (kar md) (kadr it)) lim tk) in ty k (1- fuel)))
                 ((:sign :colon) (fi-take1 rs1 in ty k (1- fuel)))
                 (:str (mv (err :format) rs in))           ; no character string edit descriptor on input (13.9p1)
                 (otherwise
                  (let* ((w (nfix (kadr it))) (cs (in-chars in))
                         (fld (append (take (min w (max 0 (- (len cs) pos))) (nthcdr pos cs))   ; PAD=YES: blanks past the end (12.5.6.15)
                                      (make-list (- w (min w (max 0 (- (len cs) pos)))) :initial-element #\Space)))
                         (v (if (and (member-eq (kar it) '(:a)) t) (err :type) (fi-field it fld ty k md))))
                    (if (or (eql (kadr it) 0) (null (kadr it))) (mv (err :format) rs in)   ; w shall not be zero on input
                      (mv v (list :fmt (cdr ds) rev md lim (+ 1 tk)) (cons (in-recs in) (+ pos w))))))))))))
(in-theory (disable fi-take1))
; after the last item, the descriptors up to the next data edit
; descriptor, colon or the format's end still act (13.4p9)
(defun fi-finish (ds in)
  (cond ((atom ds) in)
        ((member-eq (kar (car ds)) '(:slash)) (let ((in (in-next in))) (if (errp in) in (fi-finish (cdr ds) in))))
        ((or (fd-data-p (car ds)) (eq (kar (car ds)) :colon)) in)
        (t (fi-finish (cdr ds) in))))

; list-directed input (13.10.3): the reader rs = (:list sep rep val
; done): sep a value just ended without its comma yet seen; rep val a
; repeat r*c with r left; done after a slash
(defun li-blanks (in fuel)           ; past blanks and ends of record: (mv in), or the end of the file
  (declare (xargs :measure (nfix fuel)))
  (let* ((cs (in-chars in)) (pos (in-pos in)))
    (cond ((zp fuel) (err :end))
          ((< pos (len cs)) (if (member (nth pos cs) '(#\Space #\Tab)) (li-blanks (cons (in-recs in) (+ 1 pos)) (1- fuel)) in))
          (t (let ((in (in-next in))) (if (errp in) in (li-blanks in (1- fuel))))))))
(defun li-word (cs pos acc)          ; the characters to a separator: (mv chars pos)
  (declare (xargs :measure (nfix (- (len cs) (nfix pos)))))
  (if (or (not (natp pos)) (<= (len cs) pos) (member (nth pos cs) '(#\Space #\Tab #\, #\/))) (mv (reverse acc) pos)
    (li-word cs (+ 1 pos) (cons (nth pos cs) acc))))
(defun li-conv (cs ty k)             ; a value's characters as ty k: a raw value, or an error
  (cond ((eq ty :i) (let ((n (fi-int cs))) (if (and (integerp n) (in-kind k n)) n (err :input))))
        ((eq ty :r) (mv-let (sg q) (fi-real cs 0 0) (if (and q (consp cs)) (fi-real-val k sg q) (err :input))))
        ((eq ty :l) (let ((b (fi-logical cs))) (if (eq b :bad) (err :input) b)))
        (t (err :type))))
(defun li-split-rep (cs)             ; r*c: (mv r c), r nil when no repeat
  (let ((m (member #\* cs)))
    (if (and m (fi-int (take (- (len cs) (len m)) cs)) (< 0 (fi-int (take (- (len cs) (len m)) cs)))
             (consp (take (- (len cs) (len m)) cs)))
        (mv (fi-int (take (- (len cs) (len m)) cs)) (cdr m))
      (mv nil cs))))
(defun li-get (rs in ty k)           ; the next value, :null for a null value (13.10.3.2): (mv raw rs in)
  (let ((rep (nfix (kaddr rs))) (val (kadddr rs)))
    (cond ((kar (cddddr rs)) (mv :null rs in))
          ((< 0 rep) (mv (if (eq val :null) :null (li-conv val ty k)) (list :list t (- rep 1) val nil) in))
          (t (let ((in (li-blanks in 100000)))
               (if (errp in) (mv in rs in)
                 (let* ((cs (in-chars in)) (pos (in-pos in)) (c (nth pos cs)))
                   (cond ((eql c #\/) (mv :null (list :list nil 0 nil t) in))
                         ((eql c #\,)
                          (mv :null (list :list nil 0 nil nil) (cons (in-recs in) (+ 1 pos))))
                         (t (mv-let (w p2) (li-word cs pos nil)
                              (mv-let (r c) (li-split-rep w)
                                (let ((in (cons (in-recs in) p2)))
                                  (cond ((null r) (mv (li-conv w ty k) (list :list t 0 nil nil) in))
                                        (t (let ((val (if (consp c) c :null)))
                                             (mv (if (eq val :null) :null (li-conv val ty k)) (list :list t (- r 1) val nil) in))))))))))))))))
(defun li-take1 (rs in ty k)         ; a value's separator first: blanks and at most one comma (13.10.2)
  (if (and (kadr rs) (not (kar (cddddr rs))) (zp (kaddr rs)))
      (let ((in2 (li-blanks in 100000)))
        (if (and (not (errp in2)) (eql (nth (in-pos in2) (in-chars in2)) #\,))
            (li-get (list :list nil 0 nil nil) (cons (in-recs in2) (+ 1 (in-pos in2))) ty k)
          (li-get rs in ty k)))
    (li-get rs in ty k)))

; the reader a READ begins with: (mv rs in), or an error
(defun rd-begin (fmt in)
  (let ((in (in-start in)))
    (cond ((errp in) (mv in in))
          ((eq fmt :star) (mv (list :list nil 0 nil nil) in))
          (t (let ((is (parse-format fmt)))
               (mv (list :fmt (fd-expand is) (fd-rev is) (list 0 :bn) (in-pos in) 0) in))))))
(defun rd-take (rs in n ty k)        ; n values of type ty, kind k: (mv raws-or-err rs in)
  (declare (xargs :measure (nfix n) :hints (("Goal" :in-theory (disable li-take1 fi-take1)))))
  (if (zp n) (mv nil rs in)
    (mv-let (v rs in) (if (eq (kar rs) :list) (li-take1 rs in ty k)
                        (fi-take1 rs in ty k (* 4 (+ 2 (len (kadr rs))) (+ 2 (len (kaddr rs))))))
      (if (errp v) (mv v rs in)
        (mv-let (vs rs in) (rd-take rs in (1- n) ty k)
          (if (errp vs) (mv vs rs in) (mv (cons v vs) rs in)))))))
(defun rd-end (rs in adv)            ; the READ's end: (mv err in)
  (let ((in (if (eq (kar rs) :fmt) (fi-finish (kadr rs) in) in)))
    (if (errp in) (mv in in) (mv nil (in-done in adv)))))
(defun merge-null (new old)          ; a null value leaves the item's element as it was (13.10.3.2)
  (if (atom new) nil (cons (if (eq (car new) :null) (car old) (car new)) (merge-null (cdr new) (cdr old)))))

; a format specifier's text: :star, a FORMAT statement's by its label, or
; a character literal's (12.6.2.2); an error when the label has none
(defun io-fmt (f cx)
  (cond ((eq f :star) :star)
        ((stringp f) (let ((fm (cdr (assoc-equal f (alist-fix (cx-formats cx)))))) (if (stringp fm) fm (err :label))))
        (t (if (stringp (kadr f)) (kadr f) (err :format)))))
(defun io-spec (k ios) (cond ((atom ios) nil) ((eq (kar (car ios)) k) (car ios)) (t (io-spec k (cdr ios)))))
(defun fi-up (cs) (if (atom cs) nil (cons (fd-up (car cs)) (fi-up (cdr cs)))))
(defun rtrim-blanks (rcs) (if (and (consp rcs) (eql (car rcs) #\Space)) (rtrim-blanks (cdr rcs)) rcs))   ; reversed
(defun io-adv (ios)                  ; ADVANCE=: YES or NO, any case, trailing blanks ignored (12.6.2.1p4)
  (let ((a (io-spec :adv ios)))
    (if (not a) t
      (let ((s (rtrim-blanks (reverse (fi-up (coerce (if (stringp (kadr (kadr a))) (kadr (kadr a)) "") 'list))))))
        (cond ((equal s (coerce "SEY" 'list)) t) ((equal s (coerce "ON" 'list)) nil) (t (err :advance)))))))
