; fstmt-cost: fps-cost, the bound on fstmt.lisp's parser: a successful
; parse makes at most 64 calls (fp's among them) per token it consumes,
; plus fps-d nt.

(in-package "ACL2")

(include-book "fstmt-steps2")

(set-ignore-ok t)


(defthm fp-cost-linear
  (implies (mv-nth 0 (fp nt toks))
           (<= (+ (fp-steps nt toks) (* 32 (len (mv-nth 2 (fp nt toks)))))
               (+ (* 32 (len toks)) (fp-d nt))))
  :rule-classes ((:linear :trigger-terms ((fp-steps nt toks)))) :hints (("Goal" :by fp-cost)))

(defthm len-cdr-consp (implies (consp x) (equal (len (cdr x)) (+ -1 (len x)))))

; the constant each nt adds; a type-spec always reads its keyword, so it
; may owe less than nothing
(defun fps-d (nt)
  (declare (xargs :guard t))
  (case nt (:stmt 48) (:s-unit 40) (:decl-rest 32) (:shapes 48) (:shapes* 40) (:shape 32) (:ents 16)
    (:init 16) (:ent 8) (:attrs 8) (:names 8) (:ranges 40) (:range 32) (:ixs 40) (:ix 32) (:oitems 32) (:ts -63) (:io 20) (:ios 25) (otherwise 4)))

; the I/O control list's nonterminals first, each on its own: the
; induction below then answers them from these
(defmacro cost-at (nt)
  `(defthm ,(packn (list 'fps-cost- nt))
     (implies (mv-nth 0 (fps ,nt toks))
              (<= (+ (fps-steps ,nt toks) (* 64 (len (mv-nth 2 (fps ,nt toks))))) (+ (* 64 (len toks)) (fps-d ,nt))))
     :rule-classes ((:linear :trigger-terms ((fps-steps ,nt toks))))
     :hints (("Goal" ,@(case nt (:kios '(:induct (kios-ind toks))) (:oitems '(:induct (oitems-ind toks)))
                         (:items '(:induct (items-ind toks))) (otherwise nil))
              :expand ((fps ,nt toks) (fps-steps ,nt toks)) :in-theory (disable fmt-head-p fmt-of ios-ok unit-pos-p fps-open fps fps-steps)))))
(defun kios-ind (toks)               ; :kios's own recursion
  (declare (xargs :measure (len toks)))
  (if (and (consp toks) (equal (car toks) (op ",")))
      (mv-let (ok c r) (fps :io (cdr toks)) (declare (ignore c))
        (if (and ok (< (len r) (len toks))) (kios-ind r) t))
    t))
(defun oitems-ind (toks)             ; :oitems's and :items's own recursions
  (declare (xargs :measure (len toks)))
  (if (consp toks)
      (mv-let (ok e r) (fp :expr toks) (declare (ignore e))
        (if (and ok (< (len r) (len toks)) (equal (kar r) (op ","))) (oitems-ind (kdr r)) t))
    t))
(defun items-ind (toks)
  (declare (xargs :measure (len toks)))
  (if (and (consp toks) (equal (car toks) (op ",")))
      (mv-let (ok e r) (fp :expr (cdr toks)) (declare (ignore e))
        (if (and ok (< (len r) (len toks))) (items-ind r) t))
    t))
(cost-at :io)
(cost-at :kios)
(cost-at :ios)
(cost-at :oitems)
(cost-at :items)
(cost-at :s-write)
(cost-at :s-read)

(defun fps-cost-hint (id clause)
  (declare (xargs :mode :program))
  (and (equal (access clause-id id :pool-lst) (quote (1)))
       (equal (len (access clause-id id :case-lst)) 1)
       (equal (access clause-id id :primes) 0)
       (let* ((raw (case-nts clause)) (cs (set-difference-equal raw '((quote :io) (quote :kios) (quote :ios) (quote :oitems) (quote :items) (quote :s-write) (quote :s-read)))))
         (if (and (consp raw) (atom cs)) '(:in-theory (disable fps fps-steps fps-open))   ; answered by the lemmas above
           (list :expand (append (quote ((fps nt toks) (fps-steps nt toks)))
                               (loop$ for c in cs append (list (list (quote fps) c (quote toks)) (list (quote fps-steps) c (quote toks))))))))))

(defthm stmt-nt-is-s
  (implies (not (member-equal c (quote (:s-head :s-end :s-other :s-use :s-else :s-if :s-do :s-call :s-print :s-type :s-assign :s-unit :s-select :s-case :s-label :s-goto :s-format :s-write :s-read))))
           (not (equal (stmt-nt tk) c)))
  :hints (("Goal" :in-theory (enable stmt-nt))))

; a successful statement parse makes at most 64 calls per token it consumes,
; plus fps-d nt
(defthm fps-cost
  (implies (mv-nth 0 (fps nt toks))
           (<= (+ (fps-steps nt toks) (* 64 (len (mv-nth 2 (fps nt toks)))))
               (+ (* 64 (len toks)) (fps-d nt))))
  :hints (("Goal" :induct (fps-steps nt toks) :in-theory (enable member-equal)) (fps-cost-hint id clause)))
