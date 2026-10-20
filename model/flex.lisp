; flex: free source form (J3/24-007 6.3.2) to statements of tokens, the
; tokens fgram.lisp's grammar is written over. Not proved: it is checked
; by running the oracle programs through it (check-fsem.bb) beside
; gfortran and flang.
;
;   6.3.2.2  blanks separate tokens, never appear in one; the keyword
;            pairs of Table 6.2 whose blank is optional (ENDDO, ELSEIF ...)
;            are split into their two names
;   6.3.2.3  "!" begins a comment, outside a character context
;   6.3.2.4  "&" last on a line continues the statement on the next
;            noncomment line, after its first "&" if it begins with one
;   6.3.2.5  a line's end or ";" ends a statement
;   3.2/6.2  names (R603) are lower-cased: Fortran's letters are case
;            insensitive outside character contexts (6.1.2)
;
; Subset: a token is not split across lines and a character context is
; not continued (6.3.2.4p3, p4); no labels (6.3.2.6). A character the
; subset does not have gives (:bad c), which no statement accepts.
;
; A real literal (R714) is (:real m x e k): its significand's text m, the
; exponent letter x ("e", "d" or nil), the exponent's text e, the kind k.

(in-package "ACL2")

(include-book "fgram")

(defun lx-letter-p (c) (declare (xargs :guard t)) (and (characterp c) (alpha-char-p c)))
(defun lx-digit-p (c) (declare (xargs :guard t)) (and (characterp c) (digit-char-p c) t))
(defun lx-alnum-p (c) (declare (xargs :guard t)) (or (lx-letter-p c) (lx-digit-p c) (eql c #\_)))
(defun lx-blank-p (c) (declare (xargs :guard t)) (or (eql c #\Space) (eql c #\Tab) (eql c #\Return)))

(defun lx-down (cs)
  (declare (xargs :guard t))
  (if (atom cs) nil
    (cons (if (and (characterp (car cs)) (standard-char-p (car cs))) (char-downcase (car cs)) (car cs))
          (lx-down (cdr cs)))))

(defun lx-alnums (cs)               ; (mv chars rest)
  (declare (xargs :guard t))
  (if (and (consp cs) (lx-alnum-p (car cs)))
      (mv-let (a r) (lx-alnums (cdr cs)) (mv (cons (car cs) a) r))
    (mv nil cs)))
(defun lx-digits (cs)
  (declare (xargs :guard t))
  (if (and (consp cs) (lx-digit-p (car cs)))
      (mv-let (a r) (lx-digits (cdr cs)) (mv (cons (car cs) a) r))
    (mv nil cs)))
(defun lx-letters (cs)
  (declare (xargs :guard t))
  (if (and (consp cs) (lx-letter-p (car cs)))
      (mv-let (a r) (lx-letters (cdr cs)) (mv (cons (car cs) a) r))
    (mv nil cs)))
(defthm lx-alnums-len (<= (len (mv-nth 1 (lx-alnums cs))) (len cs)) :rule-classes :linear)
(defthm lx-digits-len (<= (len (mv-nth 1 (lx-digits cs))) (len cs)) :rule-classes :linear)
(defthm lx-letters-len (<= (len (mv-nth 1 (lx-letters cs))) (len cs)) :rule-classes :linear)

(defthm lx-len-cdr (implies (consp x) (equal (len (cdr x)) (+ -1 (len x)))))

(defun lx-str (cs) (declare (xargs :guard t)) (coerce (make-character-list cs) 'string))

; Table 6.2: the subset's keyword pairs written as one word
(defconst *lx-pairs*
  '(("enddo" "end" "do") ("endif" "end" "if") ("elseif" "else" "if") ("endprogram" "end" "program")
    ("endmodule" "end" "module") ("endfunction" "end" "function") ("endsubroutine" "end" "subroutine")
    ("endselect" "end" "select") ("selectcase" "select" "case")))

; a kind-param after "_" (R708, R709): digits or a name
(defun lx-kind (cs)                 ; (mv kind rest)
  (declare (xargs :guard t))
  (if (and (consp cs) (eql (car cs) #\_) (consp (cdr cs)) (lx-alnum-p (cadr cs)))
      (mv-let (a r) (lx-alnums (cdr cs)) (mv (lx-str (lx-down a)) r))
    (mv nil cs)))
(defthm lx-kind-len (<= (len (mv-nth 1 (lx-kind cs))) (len cs)) :rule-classes :linear)

; a real literal's exponent part (R714, R716, R717): E or D, then a
; signed-digit-string
(defun lx-exp (cs)                  ; (mv letter exponent rest), letter nil when none
  (declare (xargs :guard t))
  (if (and (consp cs) (member (car cs) '(#\e #\E #\d #\D)) (consp (cdr cs)))
      (let* ((sg (and (member (cadr cs) '(#\+ #\-)) (cadr cs)))
             (r (if sg (cddr cs) (cdr cs))))
        (if (and (consp r) (lx-digit-p (car r)))
            (mv-let (d r2) (lx-digits r)
              (mv (if (member (car cs) '(#\e #\E)) "e" "d") (lx-str (if sg (cons sg d) d)) r2))
          (mv nil nil cs)))
    (mv nil nil cs)))
(defthm lx-exp-len (<= (len (mv-nth 2 (lx-exp cs))) (len cs)) :rule-classes :linear)

; after "digits.": a letter begins an operator or a logical constant
; ("1.eq.2") when letters and a "." follow and spell one (6.2.6)
(defun lx-dotword-p (cs)
  (declare (xargs :guard t))
  (mv-let (w r) (lx-letters cs)
    (and (consp w) (consp r) (eql (car r) #\.)
         (let ((s (lx-str (lx-down w))))
           (or (member-equal s '("true" "false"))
               (member-equal (concatenate 'string "." s ".") *fops*)))
         t)))

; a real literal from its significand text m: the exponent, then the kind
(defun lx-real (m cs)               ; (mv token rest)
  (declare (xargs :guard t))
  (mv-let (x e r) (lx-exp cs)
    (mv-let (k r2) (lx-kind r)
      (mv (list :real m x e k) r2))))
(defthm lx-real-len (<= (len (mv-nth 1 (lx-real m cs))) (len cs)) :rule-classes :linear)

; a character literal's body after its quote q, a doubled q one q (R724)
(defun lx-quoted (q cs)             ; (mv ok chars rest)
  (declare (xargs :guard t))
  (cond ((or (atom cs) (eql (car cs) #\Newline)) (mv nil nil cs))
        ((equal (car cs) q)
         (if (and (consp (cdr cs)) (equal (cadr cs) q))
             (mv-let (ok a r) (lx-quoted q (cddr cs)) (mv ok (cons q a) r))
           (mv t nil (cdr cs))))
        (t (mv-let (ok a r) (lx-quoted q (cdr cs)) (mv ok (cons (car cs) a) r)))))
(defthm lx-quoted-len (<= (len (mv-nth 2 (lx-quoted q cs))) (len cs)) :rule-classes :linear)

(defun lx-skip-line (cs)            ; past the next newline
  (declare (xargs :guard t))
  (cond ((atom cs) nil) ((eql (car cs) #\Newline) (cdr cs)) (t (lx-skip-line (cdr cs)))))
(defthm lx-skip-line-len (<= (len (lx-skip-line cs)) (len cs)) :rule-classes :linear)

; after a continuation "&": the rest of its line blank or a comment, then
; the next noncomment line, past its leading "&" if it has one (6.3.2.4p2)
(defun lx-blanks (cs)
  (declare (xargs :guard t))
  (if (and (consp cs) (lx-blank-p (car cs))) (lx-blanks (cdr cs)) cs))
(defthm lx-blanks-len (<= (len (lx-blanks cs)) (len cs)) :rule-classes :linear)

(defun lx-cont-next (cs)            ; (mv ok rest), cs at the start of a line
  (declare (xargs :guard t :measure (len cs)))
  (let ((cs (lx-blanks cs)))
    (cond ((atom cs) (mv nil cs))
          ((or (eql (car cs) #\Newline) (eql (car cs) #\!)) (lx-cont-next (lx-skip-line cs)))
          ((eql (car cs) #\&) (mv t (cdr cs)))
          (t (mv t cs)))))
(defthm lx-cont-next-len (<= (len (mv-nth 1 (lx-cont-next cs))) (len cs)) :rule-classes :linear
  :hints (("Goal" :induct (lx-cont-next cs))))

(defun lx-cont (cs)                 ; cs just after the "&"
  (declare (xargs :guard t))
  (let ((cs (lx-blanks cs)))
    (cond ((atom cs) (mv nil cs))
          ((or (eql (car cs) #\Newline) (eql (car cs) #\!)) (lx-cont-next (lx-skip-line cs)))
          (t (mv nil cs)))))
(defthm lx-cont-len (<= (len (mv-nth 1 (lx-cont cs))) (len cs)) :rule-classes :linear)

; "::" is two ":" tokens: the separator of R801 and R1409, and two colons
; of a triplet a(::2) (R922), are the same characters
(defconst *lx-two* '("**" "==" "/=" "<=" ">=" "//"))
(defconst *lx-one* '(#\+ #\- #\* #\/ #\< #\> #\( #\) #\, #\= #\: #\[ #\] #\%))

(defthm lx-digits-strict
  (implies (and (consp cs) (lx-digit-p (car cs))) (< (len (mv-nth 1 (lx-digits cs))) (len cs)))
  :rule-classes :linear)

; a number: an integer literal, or a real one (R708, R714)
(defun lx-number (cs)               ; (mv token rest), cs at a digit or at "." and a digit
  (declare (xargs :guard t))
  (if (and (consp cs) (lx-digit-p (car cs)))
      (mv-let (d r) (lx-digits cs)
        (cond
         ; digits "." [digits]: a real, unless an operator follows the digits
         ((and (consp r) (eql (car r) #\.) (not (lx-dotword-p (cdr r))))
          (mv-let (f r1) (lx-digits (cdr r))
            (lx-real (lx-str (append d (cons #\. f))) r1)))
         ; digits exponent: a real (R714's second form)
         ((mv-let (x e r1) (lx-exp r) (declare (ignore e r1)) x)
          (lx-real (lx-str d) r))
         (t (mv-let (k r2) (lx-kind r) (mv (list :int (lx-str d) k) r2)))))
    ; "." digits: a real (R715's second form)
    (mv-let (f r1) (lx-digits (kdr cs))
      (lx-real (lx-str (cons #\. f)) r1))))
(defthm lx-number-len
  (implies (consp cs) (< (len (mv-nth 1 (lx-number cs))) (len cs)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable lx-dotword-p lx-exp lx-real lx-kind lx-str lx-digits))))
(in-theory (disable lx-number))

; the tokens, with :eos where a statement ends
(defun lx-toks (cs)
  (declare (xargs :guard t :measure (len cs)))
  (if (atom cs) nil
    (let ((c (car cs)))
      (cond
       ((lx-blank-p c) (lx-toks (cdr cs)))
       ((or (eql c #\Newline) (eql c #\;)) (cons :eos (lx-toks (cdr cs))))
       ((eql c #\!) (cons :eos (lx-toks (lx-skip-line cs))))
       ((eql c #\&) (mv-let (ok r) (lx-cont (cdr cs))
                      (if ok (lx-toks r) (list (list :bad "&")))))
       ((lx-letter-p c)
        (mv-let (a r) (lx-alnums cs)
          (let* ((s (lx-str (lx-down a))) (pair (assoc-equal s *lx-pairs*)))
            (if pair
                (list* (list :name (cadr pair)) (list :name (caddr pair)) (lx-toks r))
              (cons (list :name s) (lx-toks r))))))
       ((or (lx-digit-p c) (and (eql c #\.) (consp (cdr cs)) (lx-digit-p (cadr cs))))
        (mv-let (tok r) (lx-number cs) (cons tok (lx-toks r))))
       ((eql c #\.)
        (mv-let (w r) (lx-letters (cdr cs))
          (let ((s (lx-str (lx-down w))))
            (if (and (consp w) (consp r) (eql (car r) #\.))
                (if (member-equal s '("true" "false"))
                    (mv-let (k r2) (lx-kind (cdr r))
                      (cons (list :log (equal s "true") k) (lx-toks r2)))
                  (let ((o (concatenate 'string "." s ".")))
                    (if (member-equal o *fops*) (cons (list :op o) (lx-toks (cdr r)))
                      (list (list :bad o)))))
              (list (list :bad "."))))))
       ((or (eql c #\') (eql c #\"))
        (mv-let (ok a r) (lx-quoted c (cdr cs))
          (if ok (cons (list :char (lx-str a)) (lx-toks r)) (list (list :bad "quote")))))
       ((and (consp (cdr cs)) (member-equal (lx-str (list c (cadr cs))) *lx-two*))
        (cons (list :op (lx-str (list c (cadr cs)))) (lx-toks (cddr cs))))
       ((member c *lx-one*) (cons (list :op (lx-str (list c))) (lx-toks (cdr cs))))
       (t (list (list :bad (lx-str (list c)))))))))

; the statements: the tokens between :eos marks, the empty ones dropped
(defun lx-stmts (ts cur)
  (declare (xargs :guard (true-listp cur)))
  (cond ((atom ts) (if cur (list (reverse cur)) nil))
        ((eq (car ts) :eos) (if cur (cons (reverse cur) (lx-stmts (cdr ts) nil)) (lx-stmts (cdr ts) nil)))
        (t (lx-stmts (cdr ts) (cons (car ts) cur)))))

(defun flex (s)
  (declare (xargs :guard (stringp s)))
  (lx-stmts (lx-toks (coerce s 'list)) nil))

(assert-event (equal (flex (concatenate 'string "x = a .AND. B ! hi" (string #\Newline) "  enddo; y(1:3) = 42_int64 + &"
                                        (string #\Newline) "  & 'it''s'"))
                     '(((:name "x") (:op "=") (:name "a") (:op ".and.") (:name "b"))
                       ((:name "end") (:name "do"))
                       ((:name "y") (:op "(") (:int "1" nil) (:op ":") (:int "3" nil) (:op ")") (:op "=")
                        (:int "42" "int64") (:op "+") (:char "it's")))))
(assert-event (equal (flex "if (1.eq.2) print *, .true._1")
                     '(((:name "if") (:op "(") (:int "1" nil) (:op ".eq.") (:int "2" nil) (:op ")")
                        (:name "print") (:op "*") (:op ",") (:log t "1")))))
; real literals (R714): the significand's forms, E and D, a kind, and the
; digits before an operator still an integer
(assert-event (equal (flex "x = 1.5 + .5e-3 + 2.d0 + 3e4_8 + 1.0_real64 + 1.e5")
                     '(((:name "x") (:op "=") (:real "1.5" nil nil nil) (:op "+") (:real ".5" "e" "-3" nil)
                        (:op "+") (:real "2." "d" "0" nil) (:op "+") (:real "3" "e" "4" "8")
                        (:op "+") (:real "1.0" nil nil "real64") (:op "+") (:real "1." "e" "5" nil)))))
(assert-event (equal (flex "if (1.eq.2.and.3.<4) x = 1")
                     '(((:name "if") (:op "(") (:int "1" nil) (:op ".eq.") (:int "2" nil) (:op ".and.")
                        (:real "3." nil nil nil) (:op "<") (:int "4" nil) (:op ")") (:name "x") (:op "=") (:int "1" nil)))))
