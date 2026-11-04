; fmean-cost: the cost of fmean.lisp's runtime data operations, and tests
; of the meaning: DO CONCURRENT's rules, I/O.

(in-package "ACL2")

(include-book "frun")

(set-verify-guards-eagerness 0)

; ---- cost: the runtime's data operations
;
; Evaluation's depth is bounded by fuel (each me-* call passes 1- fuel,
; the mutual recursion's measure). Under it, the operations a run repeats
; are linear: a variable's lookup in the store, an array element's offset
; in array element order (9.5.3.2) and its fetch or update. (A processor
; does these in constant time; the model keeps lists.)

(defun alk-steps (k al)
  (declare (xargs :guard t))
  (cond ((atom al) 1) ((and (consp (car al)) (equal (caar al) k)) 1) (t (+ 1 (alk-steps k (cdr al))))))
(defthm alk-cost (<= (alk-steps k al) (+ 1 (len al))) :rule-classes :linear)

(defun aput-steps (k al)
  (declare (xargs :guard t))
  (cond ((atom al) 1) ((and (consp (car al)) (equal (caar al) k)) 1) (t (+ 1 (aput-steps k (cdr al))))))
(defthm aput-cost (<= (aput-steps k al) (+ 1 (len al))) :rule-classes :linear)

(defun arr-offset-steps (idx lbs ubs)
  (declare (xargs :guard t))
  (cond ((and (atom idx) (atom lbs)) 1)
        ((or (atom idx) (atom lbs) (atom ubs)) 1)
        ((not (and (integerp (car idx)) (integerp (car lbs)) (integerp (car ubs))
                   (<= (car lbs) (car idx)) (<= (car idx) (car ubs)))) 1)
        (t (+ 1 (arr-offset-steps (cdr idx) (cdr lbs) (cdr ubs))))))
(defthm arr-offset-cost (<= (arr-offset-steps idx lbs ubs) (+ 1 (len idx))) :rule-classes :linear)

(defun nth-safe-steps (n xs)
  (declare (xargs :guard t))
  (if (atom xs) 1 (if (not (posp n)) 1 (+ 1 (nth-safe-steps (1- n) (cdr xs))))))
(defthm nth-safe-cost (<= (nth-safe-steps n xs) (+ 1 (len xs))) :rule-classes :linear)

(defun upd-safe-steps (n xs)
  (declare (xargs :guard t))
  (if (atom xs) 1 (if (not (posp n)) 1 (+ 1 (upd-safe-steps (1- n) (cdr xs))))))
(defthm upd-safe-cost (<= (upd-safe-steps n xs) (+ 1 (len xs))) :rule-classes :linear)

; an element's fetch or update: linear in the rank and the element count
(defun arr-get-steps (a idx)
  (declare (xargs :guard t))
  (+ (arr-offset-steps idx (a-lbs a) (a-ubs a)) (nth-safe-steps (arr-offset idx (a-lbs a) (a-ubs a)) (a-es a))))
(defthm arr-get-cost (<= (arr-get-steps a idx) (+ 2 (len idx) (len (a-es a)))) :rule-classes :linear)
(defun arr-set-steps (a idx)
  (declare (xargs :guard t))
  (+ (arr-offset-steps idx (a-lbs a) (a-ubs a)) (upd-safe-steps (arr-offset idx (a-lbs a) (a-ubs a)) (a-es a))))
(defthm arr-set-cost (<= (arr-set-steps a idx) (+ 2 (len idx) (len (a-es a)))) :rule-classes :linear)

; ---- tests: DO CONCURRENT's rules (11.1.7.5), each broken once

(defun lines-text (ls)              ; a program's text, one string per line
  (declare (xargs :guard t))
  (if (atom ls) "" (concatenate 'string (if (stringp (car ls)) (car ls) "") (string #\Newline) (lines-text (cdr ls)))))
(defmacro prog-lines (&rest ls) `(lines-text (list ,@ls)))
(defun run-status (text) (declare (xargs :mode :program)) (car (fortran-run text 1000000)))

; s referred to in every iteration and defined in the others: a reduction
; without REDUCE locality
(assert-event (equal (run-status (prog-lines "program p" "implicit none" "integer :: i, s" "s = 0"
                                             "do concurrent (i = 1:3)" "s = s + i" "end do" "print *, s" "end program p"))
                     '(:error :concurrent)))
; a(i) referred to in iteration i and defined in iteration i - 1
(assert-event (equal (run-status (prog-lines "program p" "implicit none" "integer :: i, a(4)" "a = 1"
                                             "do concurrent (i = 1:3)" "a(i + 1) = a(i)" "end do" "print *, a" "end program p"))
                     '(:error :concurrent)))
; EXIT out of the construct (C1172)
(assert-event (equal (run-status (prog-lines "program p" "implicit none" "integer :: i" 
                                             "do concurrent (i = 1:3)" "exit" "end do" "end program p"))
                     '(:error :concurrent)))
; each element its own iteration's: conforming
(assert-event (equal (fortran-run (prog-lines "program p" "implicit none" "integer :: i, a(3)" "a = 1"
                                              "do concurrent (i = 1:3)" "a(i) = a(i) + i" "end do" "print *, a" "end program p")
                                  1000000)
                     '(:normal (("2" "3" "4")))))
; an operand the value does not need, and its error (10.1.7)
(assert-event (equal (fortran-run (prog-lines "program p" "implicit none" "logical :: l" "integer :: z" "z = 0"
                                              "l = (z > 1) .and. (1 / z > 0)" "print *, l" "end program p")
                                  1000000)
                     '(:normal (("~PD")))))

; ---- tests: I/O on the unit * (12.6, 13)
(defun run-in (text in) (declare (xargs :mode :program)) (fortran-run-in text nil in 1000000))
; a formatted READ and WRITE, the record exactly
(assert-event (equal (run-in (prog-lines "program p" "implicit none" "integer :: n" "real(8) :: x"
                                         "read (*, '(i3, f6.1)') n, x" "write (*, '(i4, es10.2)') n + 1, x" "end program p")
                             '(" 41 2.5e1"))
                     '(:normal (("~F  42  2.50E+01")))))
; ADVANCE='NO' leaves the record open; the next WRITE continues it
(assert-event (equal (run-in (prog-lines "program p" "write (*, '(a)', advance='no') 'ab'" "write (*, '(i2)') 7" "end program p") nil)
                     '(:normal (("~Fab 7")))))
; C1223: no ADVANCE= with list-directed formatting; C1218: the format
; without FMT= only second; C1210: a specifier once
(assert-event (equal (car (run-in (prog-lines "program p" "write (*, *, advance='no') 1" "end program p") nil)) '(:error :parse)))
(assert-event (equal (car (run-in (prog-lines "program p" "write (unit=*, '(i2)') 1" "end program p") nil)) '(:error :parse)))
(assert-event (equal (car (run-in (prog-lines "program p" "write (*, '(i2)', fmt='(i3)') 1" "end program p") nil)) '(:error :parse)))
; ADVANCE= neither YES nor NO (12.6.2.4); a READ past the last record
; (12.11.3); a field that is no integer (13.7.2.1); G0 of a real, the
; processor's (13.7.5.2.3)
(assert-event (equal (car (run-in (prog-lines "program p" "write (*, '(i2)', advance='maybe') 1" "end program p") nil)) '(:error :advance)))
(assert-event (equal (car (run-in (prog-lines "program p" "integer :: n" "read *, n" "end program p") nil)) '(:error :end)))
(assert-event (equal (car (run-in (prog-lines "program p" "integer :: n" "read '(i3)', n" "end program p") '("1.5"))) '(:error :input)))
(assert-event (equal (car (run-in (prog-lines "program p" "write (*, '(g0)') 1.5d0" "end program p") nil)) '(:error :pd)))
