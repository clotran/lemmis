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
; not continued (6.3.2.4p3, p4). A character the
; subset does not have gives (:bad c), which no statement accepts.
; A statement's label is a statement of its own, ((:lab l)); a FORMAT
; statement's specification one token, (:fmt text).
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
    ("endselect" "end" "select") ("selectcase" "select" "case") ("goto" "go" "to")))

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

; ---- a FORMAT statement's specification, kept as text (13.2): its
; edit descriptors are not tokens of the expression grammar. From "(" to
; the matching ")", a character constant's text kept whole.
(defun lx-fmt-raw (cs depth q)       ; (mv chars rest), q the open quote or nil
  (declare (xargs :guard t :measure (len cs)))
  (cond ((or (atom cs) (eql (car cs) #\Newline)) (mv nil cs))
        (q (mv-let (a r) (lx-fmt-raw (cdr cs) depth (if (equal (car cs) q) nil q)) (mv (cons (car cs) a) r)))
        ((or (eql (car cs) #\') (eql (car cs) #\")) (mv-let (a r) (lx-fmt-raw (cdr cs) depth (car cs)) (mv (cons (car cs) a) r)))
        ((eql (car cs) #\() (mv-let (a r) (lx-fmt-raw (cdr cs) (+ 1 (nfix depth)) nil) (mv (cons (car cs) a) r)))
        ((eql (car cs) #\))
         (if (<= (nfix depth) 1) (mv (list #\)) (cdr cs))
           (mv-let (a r) (lx-fmt-raw (cdr cs) (+ -1 (nfix depth)) nil) (mv (cons (car cs) a) r))))
        (t (mv-let (a r) (lx-fmt-raw (cdr cs) depth nil) (mv (cons (car cs) a) r)))))
(defthm lx-fmt-raw-len (<= (len (mv-nth 1 (lx-fmt-raw cs depth q))) (len cs)) :rule-classes :linear)

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
            (cond (pair (list* (list :name (cadr pair)) (list :name (caddr pair)) (lx-toks r)))
                  ((and (equal s "format") (eql (kar (lx-blanks r)) #\())
                   (mv-let (f r2) (lx-fmt-raw (lx-blanks r) 0 nil)
                     (list* (list :name s) (list :fmt (lx-str f)) (lx-toks r2))))
                  (t (cons (list :name s) (lx-toks r)))))))
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
; a statement's label (6.3.2.5): the digits before it, its own statement
(defun lx-label (st)
  (declare (xargs :guard t))
  (if (and (consp st) (consp (cdr st)) (consp (car st)) (eq (car (car st)) :int) (null (kaddr (car st))))
      (list (list (list :lab (kadr (car st)))) (cdr st))
    (list st)))
(defun lx-stmts (ts cur)
  (declare (xargs :guard (true-listp cur)))
  (cond ((atom ts) (if cur (lx-label (reverse cur)) nil))
        ((eq (car ts) :eos) (if cur (append (lx-label (reverse cur)) (lx-stmts (cdr ts) nil)) (lx-stmts (cdr ts) nil)))
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

; ---- fixed source form (6.3.3): a "C", "c", "*" or "!" in column 1, or
; a blank line, is a comment; columns 1-5 hold a statement's label, a
; character other than blank or zero in column 6 continues the line
; before, the statement is in columns 7-72. Blanks mean nothing outside
; a character context (6.3.3.2), so a statement's text is read without
; them and given to lx-toks with a blank after its keyword: "GOTO40040"
; is go to 40040, "DO10I=1,10" do 10 i=1,10 (6.3.3.1).

(defun ff-lines (cs line)            ; the lines, each a list of characters
  (declare (xargs :guard (true-listp line)))
  (cond ((atom cs) (if line (list (reverse line)) nil))
        ((eql (kar cs) #\Newline) (cons (reverse line) (ff-lines (kdr cs) nil)))
        (t (ff-lines (kdr cs) (cons (kar cs) line)))))
(defun ff-take (n cs) (declare (xargs :guard (natp n))) (if (or (zp n) (atom cs)) nil (cons (kar cs) (ff-take (1- n) (kdr cs)))))
(defun ff-drop (n cs) (declare (xargs :guard (natp n))) (if (or (zp n) (atom cs)) cs (ff-drop (1- n) (kdr cs))))
(defun ff-blank-p (cs) (declare (xargs :guard t)) (if (atom cs) t (and (lx-blank-p (kar cs)) (ff-blank-p (kdr cs)))))
(defun ff-no-blanks (cs) (declare (xargs :guard t)) (if (atom cs) nil (if (lx-blank-p (kar cs)) (ff-no-blanks (kdr cs)) (cons (kar cs) (ff-no-blanks (kdr cs))))))
(defun ff-comment-p (l)
  (declare (xargs :guard t))
  (or (ff-blank-p l) (member (kar l) '(#\C #\c #\* #\!))))
(defun ff-cont-p (l)
  (declare (xargs :guard t))
  (let ((c (kar (ff-drop 5 l)))) (and (characterp c) (not (eql c #\Space)) (not (eql c #\0)))))

; the statements: (label-chars . text-chars), continuations joined
(defun ff-join (ls acc)
  (declare (xargs :guard (true-listp acc)))
  (cond ((atom ls) (reverse acc))
        ((ff-comment-p (kar ls)) (ff-join (kdr ls) acc))
        ((and (ff-cont-p (kar ls)) (consp acc))
         (ff-join (kdr ls) (cons (cons (kar (kar acc)) (append (true-list-fix (kdr (kar acc))) (ff-take 66 (ff-drop 6 (kar ls))))) (kdr acc))))
        (t (ff-join (kdr ls) (cons (cons (ff-no-blanks (ff-take 5 (kar ls))) (ff-take 66 (ff-drop 6 (kar ls)))) acc)))))

; the text without blanks, lower case, outside character contexts
(defun ff-squeeze (cs q)
  (declare (xargs :guard t))
  (cond ((atom cs) nil)
        (q (cons (kar cs) (ff-squeeze (kdr cs) (if (equal (kar cs) q) nil q))))
        ((or (eql (kar cs) #\') (eql (kar cs) #\")) (cons (kar cs) (ff-squeeze (kdr cs) (kar cs))))
        ((lx-blank-p (kar cs)) (ff-squeeze (kdr cs) nil))
        (t (cons (if (and (characterp (kar cs)) (standard-char-p (kar cs))) (char-downcase (kar cs)) (kar cs))
                 (ff-squeeze (kdr cs) nil)))))

(defun ff-prefix-p (p cs) (declare (xargs :guard t)) (if (atom p) t (and (consp cs) (equal (kar p) (kar cs)) (ff-prefix-p (kdr p) (kdr cs)))))

; an "=" outside parentheses and character contexts, not a relation's
(defun ff-top-eq (cs depth q prev)   ; the text after it, or nil
  (declare (xargs :guard t :measure (len cs)))
  (cond ((atom cs) nil)
        (q (ff-top-eq (kdr cs) depth (if (equal (kar cs) q) nil q) (kar cs)))
        ((or (eql (kar cs) #\') (eql (kar cs) #\")) (ff-top-eq (kdr cs) depth (kar cs) (kar cs)))
        ((eql (kar cs) #\() (ff-top-eq (kdr cs) (+ 1 (nfix depth)) nil (kar cs)))
        ((eql (kar cs) #\)) (ff-top-eq (kdr cs) (+ -1 (nfix depth)) nil (kar cs)))
        ((and (eql (kar cs) #\=) (zp (nfix depth)) (not (member prev '(#\< #\> #\/ #\=))) (not (eql (kadr cs) #\=)) (not (eql (kadr cs) #\>)))
         (cons #\Space (kdr cs)))
        (t (ff-top-eq (kdr cs) depth nil (kar cs)))))
(defun ff-top-comma-p (cs depth q)
  (declare (xargs :guard t :measure (len cs)))
  (cond ((atom cs) nil)
        (q (ff-top-comma-p (kdr cs) depth (if (equal (kar cs) q) nil q)))
        ((or (eql (kar cs) #\') (eql (kar cs) #\")) (ff-top-comma-p (kdr cs) depth (kar cs)))
        ((eql (kar cs) #\() (ff-top-comma-p (kdr cs) (+ 1 (nfix depth)) nil))
        ((eql (kar cs) #\)) (ff-top-comma-p (kdr cs) (+ -1 (nfix depth)) nil))
        ((and (eql (kar cs) #\,) (zp (nfix depth))) t)
        (t (ff-top-comma-p (kdr cs) depth nil))))
(defun ff-close (cs depth q n)       ; how many characters to the ")" closing an open "("
  (declare (xargs :guard (natp n) :measure (len cs)))
  (cond ((atom cs) nil)
        (q (ff-close (kdr cs) depth (if (equal (kar cs) q) nil q) (+ 1 n)))
        ((or (eql (kar cs) #\') (eql (kar cs) #\")) (ff-close (kdr cs) depth (kar cs) (+ 1 n)))
        ((eql (kar cs) #\() (ff-close (kdr cs) (+ 1 (nfix depth)) nil (+ 1 n)))
        ((eql (kar cs) #\)) (if (<= (nfix depth) 1) (+ 1 n) (ff-close (kdr cs) (+ -1 (nfix depth)) nil (+ 1 n))))
        (t (ff-close (kdr cs) depth nil (+ 1 n)))))
(defun ff-labels-p (cs) (declare (xargs :guard t))   ; digits and commas: an arithmetic IF's labels
  (and (consp cs) (if (atom cs) t (and (or (lx-digit-p (kar cs)) (eql (kar cs) #\,)) (or (atom (kdr cs)) (ff-labels-p (kdr cs)))))))

(defconst *ff-keywords*              ; a statement's first word, longest first where one begins another
  '("doubleprecision" "implicitnone" "endprogram" "endsubroutine" "endfunction" "endmodule" "subroutine" "dimension"
    "continue" "function" "implicit" "integer" "logical" "program" "contains" "elseif" "endif" "enddo" "return"
    "format" "write" "print" "read" "character" "real" "call" "stop" "else" "then" "end" "data" "common"))
(defun ff-kw (cs ks)                 ; the keyword cs begins with
  (declare (xargs :guard t))
  (cond ((atom ks) nil)
        ((and (stringp (kar ks)) (ff-prefix-p (coerce (kar ks) 'list) cs)) (kar ks))
        (t (ff-kw cs (kdr ks)))))
(defconst *ff-spaced*                ; a keyword written as two words in free form
  '(("doubleprecision" . "double precision") ("implicitnone" . "implicit none") ("endprogram" . "end program")
    ("endsubroutine" . "end subroutine") ("endfunction" . "end function") ("endmodule" . "end module")
    ("elseif" . "else if") ("endif" . "end if") ("enddo" . "end do")))

; a squeezed statement's free-form text
(defun ff-stmt (cs)
  (declare (xargs :guard t :measure (len cs)))
  (cond
   ((ff-prefix-p '(#\i #\f #\() cs)
    (let ((n (ff-close (kdr (kdr (kdr cs))) 1 nil 0)))   ; just after IF's "("
      (if (not (natp n)) cs
        (let* ((head (ff-take (+ 3 n) cs)) (rest (ff-drop (+ 3 n) cs)))
          (cond ((eql (kar rest) #\=) cs)                      ; an assignment to an array IF
                ((ff-labels-p rest) (append head (cons #\Space rest)))
                ((< (len rest) (len cs)) (append head (cons #\Space (ff-stmt rest))))
                (t cs))))))
   ((and (ff-top-eq cs 0 nil nil) (ff-prefix-p '(#\d #\o) cs) (ff-top-comma-p (ff-top-eq cs 0 nil nil) 0 nil))
    ; DO [label] [,] v = e, e: the label's digits, then the rest
    (let ((r (kdr (kdr cs))))
      (mv-let (d r2) (lx-digits r)
        (append (list #\d #\o #\Space) d (list #\Space) r2))))
   ((ff-top-eq cs 0 nil nil) cs)                              ; an assignment
   ((ff-prefix-p '(#\g #\o #\t #\o) cs) (append (coerce "go to " 'list) (ff-drop 4 cs)))
   (t (let ((k (ff-kw cs *ff-keywords*)))
        (if (not k) cs
          (let ((sp (kdr (assoc-equal k *ff-spaced*))))
            (append (coerce (if sp sp k) 'list) (cons #\Space (ff-drop (len (coerce k 'list)) cs)))))))))

(defun ff-stmts (ss)                 ; each statement's tokens, its label's statement first
  (declare (xargs :guard t))
  (if (atom ss) nil
    (let* ((lab (kar (kar ss))) (toks (lx-toks (ff-stmt (ff-squeeze (kdr (kar ss)) nil))))
           (rest (ff-stmts (kdr ss))))
      (append (if (and (consp lab) (digit-string-p (lx-str lab))) (list (list (list :lab (lx-str lab)))) nil)
              (if (consp toks) (list (remove-equal :eos toks)) nil)
              rest))))

(defun flex-fixed (s)
  (declare (xargs :guard (stringp s)))
  (ff-stmts (ff-join (ff-lines (coerce s 'list) nil) nil)))

(assert-event (equal (flex-fixed (concatenate 'string
                                  "C A COMMENT" (string #\Newline)
                                  "      PROGRAM FM002" (string #\Newline)
                                  "   41 CONTINUE                                                          00860002" (string #\Newline)
                                  "      IF (ICZERO) 30040,40,30040" (string #\Newline)
                                  "      GO TO 40040" (string #\Newline)
                                  "      IF (N .LE. (5)) GOTO 10" (string #\Newline)
                                  "      DO 10 I = 1, N" (string #\Newline)
                                  "      IVON01 = IVON01" (string #\Newline)
                                  "     1   + 1" (string #\Newline)
                                  "90002 FORMAT (\" \",4X,I5,7X,\"PASS\")"))
                     '(((:name "program") (:name "fm002")) ((:lab "41")) ((:name "continue"))
                       ((:name "if") (:op "(") (:name "iczero") (:op ")") (:int "30040" nil) (:op ",") (:int "40" nil) (:op ",") (:int "30040" nil))
                       ((:name "go") (:name "to") (:int "40040" nil))
                       ((:name "if") (:op "(") (:name "n") (:op ".le.") (:op "(") (:int "5" nil) (:op ")") (:op ")") (:name "go") (:name "to") (:int "10" nil))
                       ((:name "do") (:int "10" nil) (:name "i") (:op "=") (:int "1" nil) (:op ",") (:name "n"))
                       ((:name "ivon01") (:op "=") (:name "ivon01") (:op "+") (:int "1" nil))
                       ((:lab "90002")) ((:name "format") (:fmt "(\" \",4x,i5,7x,\"PASS\")")))))
