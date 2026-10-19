; fsem: an executable meaning for fsyn's subset -- the Fortran clotran's
; generator emits. Expressions are evaluated and statements executed over
; a state: a frame (the procedure's variables) and a heap (the derived-
; type objects the procedures share by reference).
;
; What the standard leaves undefined is an explicit error, never a value
; wrapped or guessed (J3/24-007):
;   :overflow   an integer result outside int64 -- 10.1.5.2.4p1, "the
;               execution of any numeric operation whose result is not
;               defined by the arithmetic used by the processor is
;               prohibited". int64's range is -2^63 .. 2^63-1, the two's
;               complement range of gfortran and flang (16.4's model is
;               symmetric, HUGE = 2^63-1; -2^63 is the processor's, and
;               the generator relies on it: (-huge(0_int64) - 1_int64))
;   :bounds     a subscript outside its array -- 9.5.3.1p2
;   :undefined  a reference to an undefined variable -- 19.6; locals, and
;               an INTENT(OUT) dummy (15.5.2.5p20), start undefined
;   :intent     a definition through an INTENT(IN) dummy (C846)
;   :type, :syntax, :unknown-proc, :arity   a program outside the subset
;               or not conforming
;   :fuel       the model's own step bound ran out (not Fortran's)
;
; State:
;   frame  alist name -> (type . v), type :int64 or :logical, v the value
;          or :undef; or name -> (:obj intent . key) for a derived-type
;          dummy, key naming its object in the heap
;   heap   alist key -> components, an alist comp -> integer, or comp ->
;          (:array . elements) for an int64 array with lower bound 0
;          (the generator's arrays are all 0-based)
;
; Every function's guard is T and verified: the meaning runs as Common
; Lisp without a guard violation on any input, checking its operands'
; types itself.

(in-package "ACL2")

(include-book "fsyn")

; ---- safe accessors, alists

(defun kar (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun kdr (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))
(defun kadr (x) (declare (xargs :guard t)) (kar (kdr x)))
(defun kaddr (x) (declare (xargs :guard t)) (kar (kdr (kdr x))))
(defun kadddr (x) (declare (xargs :guard t)) (kar (kdr (kdr (kdr x)))))

(defun lkp (k al)
  (declare (xargs :guard t))
  (cond ((atom al) nil)
        ((and (consp (car al)) (equal (caar al) k)) (car al))
        (t (lkp k (cdr al)))))

(defun put (k v al)
  (declare (xargs :guard t))
  (cond ((atom al) (list (cons k v)))
        ((and (consp (car al)) (equal (caar al) k)) (cons (cons k v) (cdr al)))
        (t (cons (car al) (put k v (cdr al))))))

(defun int64p (x)
  (declare (xargs :guard t))
  (and (integerp x) (<= *int64-min* x) (<= x *int64-max*)))

(defun find-proc (f procs)
  (declare (xargs :guard t))
  (cond ((atom procs) nil)
        ((and (true-listp (car procs)) (equal (nth 1 (car procs)) f)) (car procs))
        (t (find-proc f (cdr procs)))))

; ---- the operations

; integer +, -, *: the exact result, or :overflow
(defun arith (op a b)
  (declare (xargs :guard t))
  (if (and (integerp a) (integerp b))
      (let ((r (case op (:add (+ a b)) (:sub (- a b)) (otherwise (* a b)))))
        (if (int64p r) (mv nil r) (mv :overflow nil)))
    (mv :type nil)))

(defthm arith-int64
  (implies (not (mv-nth 0 (arith op a b)))
           (int64p (mv-nth 1 (arith op a b)))))

(defun binop (op a b)
  (declare (xargs :guard t))
  (if (and (integerp a) (integerp b))
      (case op
        ((:add :sub :mul) (arith op a b))
        (:eq (mv nil (= a b)))
        (:lt (mv nil (< a b)))
        (:le (mv nil (<= a b)))
        (:ge (mv nil (>= a b)))
        (otherwise (mv nil (max a b))))
    (mv :type nil)))

; ---- the objects

; o's object: (mv err key intent)
(defun obj-of (o frame)
  (declare (xargs :guard t))
  (let ((b (cdr (lkp o frame))))
    (if (and (consp b) (eq (car b) :obj) (consp (cdr b)))
        (mv nil (cddr b) (cadr b))
      (mv :type nil nil))))

; component c of o: (mv err v), v an integer or (:array . elements)
(defun comp-of (o c frame heap)
  (declare (xargs :guard t))
  (mv-let (err key intent) (obj-of o frame)
    (declare (ignore intent))
    (if err (mv err nil)
      (let ((p (lkp c (cdr (lkp key heap)))))
        (if (consp p) (mv nil (cdr p)) (mv :type nil))))))

(defun farrayp (v)
  (declare (xargs :guard t))
  (and (consp v) (eq (car v) :array) (true-listp (cdr v))))

(defun read-elem (v i)
  (declare (xargs :guard t))
  (cond ((not (and (farrayp v) (integerp i))) (mv :type nil))
        ((and (<= 0 i) (< i (len (cdr v))))
         (let ((x (nth i (cdr v)))) (if (int64p x) (mv nil x) (mv :undefined nil))))
        (t (mv :bounds nil))))

; ---- evaluation and execution, one mutual recursion on fuel
;
; ev       expr -> (mv err value)
; bind     dummies x actuals -> (mv err callee-frame outs), outs pairing
;          each INTENT(OUT) dummy with the caller's variable
; invoke   a procedure on actuals -> (mv err value heap)
; ex       stmt -> (mv status frame heap), status :normal :exit :cycle
;          :return or (:error kind)
; ex-list  stmts, the same

(defun errst (k) (declare (xargs :guard t)) (list :error k))
(defun errstp (s) (declare (xargs :guard t)) (and (consp s) (eq (car s) :error)))

(defun scalar-ok (ty v)
  (declare (xargs :guard t))
  (if (eq ty :logical) (booleanp v) (and (eq ty :int64) (int64p v))))

(defun undef-locals (locals frame)
  (declare (xargs :guard t))
  (if (atom locals) frame
    (undef-locals (cdr locals) (put (kar (car locals)) (cons (kadr (car locals)) :undef) frame))))

; the callee's INTENT(OUT) values back into the caller's variables
(defun copy-out (outs callee caller)
  (declare (xargs :guard t))
  (if (atom outs) caller
    (let ((b (cdr (lkp (kar (car outs)) callee))))
      (copy-out (cdr outs) callee (put (kdr (car outs)) (cons :int64 (kdr b)) caller)))))

(mutual-recursion

 (defun f-ev (x frame heap procs fuel)
   (declare (xargs :guard t :measure (nfix fuel) :verify-guards nil))
   (if (not (posp fuel)) (mv :fuel nil)
     (case (kar x)
       (:int (if (int-lit-p (kadr x)) (mv nil (kadr x)) (mv :syntax nil)))
       (:true (mv nil t))
       (:false (mv nil nil))
       (:huge (mv nil *int64-max*))
       (:var (let ((b (cdr (lkp (kadr x) frame))))
               (cond ((not (and (consp b) (member-eq (car b) '(:int64 :logical)))) (mv :type nil))
                     ((eq (cdr b) :undef) (mv :undefined nil))
                     (t (mv nil (cdr b))))))
       (:comp (mv-let (err v) (comp-of (kadr x) (kaddr x) frame heap)
                (cond (err (mv err nil)) ((int64p v) (mv nil v)) (t (mv :type nil)))))
       (:size (mv-let (err v) (comp-of (kadr x) (kaddr x) frame heap)
                (cond (err (mv err nil)) ((farrayp v) (mv nil (len (cdr v)))) (t (mv :type nil)))))
       (:elem (mv-let (err i) (f-ev (kadddr x) frame heap procs (1- fuel))
                (if err (mv err nil)
                  (mv-let (err v) (comp-of (kadr x) (kaddr x) frame heap)
                    (if err (mv err nil) (read-elem v i))))))
       (:neg (mv-let (err a) (f-ev (kadr x) frame heap procs (1- fuel))
               (if err (mv err nil) (arith :sub 0 a))))
       (:not (mv-let (err a) (f-ev (kadr x) frame heap procs (1- fuel))
               (cond (err (mv err nil)) ((booleanp a) (mv nil (not a))) (t (mv :type nil)))))
       ((:add :sub :mul :eq :lt :le :ge :max)
        (mv-let (err a) (f-ev (kadr x) frame heap procs (1- fuel))
          (if err (mv err nil)
            (mv-let (err b) (f-ev (kaddr x) frame heap procs (1- fuel))
              (if err (mv err nil) (binop (kar x) a b))))))
       (:fcall (let ((p (find-proc (kadr x) procs)))
                 (if (not (eq (kar p) :function)) (mv :unknown-proc nil)
                   (mv-let (err v h) (f-invoke p (kaddr x) frame heap procs (1- fuel))
                     (declare (ignore h))
                     (mv err v)))))
       (otherwise (mv :syntax nil)))))

 (defun f-bind (dummies args caller callee outs heap procs fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv :fuel nil nil))
         ((atom dummies) (if (atom args) (mv nil callee outs) (mv :arity nil nil)))
         ((atom args) (mv :arity nil nil))
         (t (let ((d (car dummies)) (a (car args)))
              (case (kadr d)
                (:value (mv-let (err v) (f-ev a caller heap procs (1- fuel))
                          (cond (err (mv err nil nil))
                                ((not (int64p v)) (mv :type nil nil))
                                (t (f-bind (cdr dummies) (cdr args) caller
                                         (put (kar d) (cons :int64 v) callee) outs heap procs (1- fuel))))))
                ((:in :inout)
                 (mv-let (err key intent) (if (eq (kar a) :var) (obj-of (kadr a) caller) (mv :type nil nil))
                   (cond (err (mv err nil nil))
                         ; an INTENT(IN) object cannot become an INTENT(INOUT) dummy (C846)
                         ((and (eq (kadr d) :inout) (not (eq intent :inout))) (mv :intent nil nil))
                         (t (f-bind (cdr dummies) (cdr args) caller
                                  (put (kar d) (list* :obj (kadr d) key) callee) outs heap procs (1- fuel))))))
                (:out (let ((b (cdr (lkp (kadr a) caller))))
                        (if (and (eq (kar a) :var) (consp b) (eq (car b) :int64))
                            ; undefined on entry (15.5.2.5p20)
                            (f-bind (cdr dummies) (cdr args) caller (put (kar d) (cons :int64 :undef) callee)
                                  (cons (cons (kar d) (kadr a)) outs) heap procs (1- fuel))
                          (mv :type nil nil))))
                (otherwise (mv :syntax nil nil)))))))

 (defun f-invoke (p args caller heap procs fuel)
   ; a function answers (mv err r heap); a subroutine (mv err frame heap),
   ; the frame the caller's with the INTENT(OUT) values copied out
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv :fuel nil heap)
     (let* ((fn (eq (kar p) :function))
            (dummies (if fn (nth 4 (true-list-fix p)) (nth 3 (true-list-fix p))))
            (locals (if fn (nth 6 (true-list-fix p)) (nth 4 (true-list-fix p))))
            (body (if fn (nth 7 (true-list-fix p)) (nth 5 (true-list-fix p)))))
       (mv-let (err callee outs) (f-bind dummies args caller nil nil heap procs (1- fuel))
         (if err (mv err nil heap)
           (let ((callee (undef-locals (if fn (cons (list "r" (nth 5 (true-list-fix p))) locals) locals) callee)))
             (mv-let (st fr h) (f-ex-list body callee heap procs (1- fuel))
               (cond ((errstp st) (mv (kadr st) nil heap))
                     ((not (member-eq st '(:normal :return))) (mv :syntax nil heap)) ; EXIT or CYCLE outside a DO
                     (fn (let ((b (cdr (lkp "r" fr))))
                           (if (and (consp b) (scalar-ok (car b) (cdr b)))
                               (mv nil (cdr b) heap)
                             (mv :undefined nil heap))))
                     (t (mv nil (copy-out outs fr caller) h))))))))))

 (defun f-ex (x frame heap procs fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (if (not (posp fuel)) (mv (errst :fuel) frame heap)
     (case (kar x)
       (:assign
        (mv-let (err v) (f-ev (kaddr x) frame heap procs (1- fuel))
          (if err (mv (errst err) frame heap)
            (let ((d (kadr x)))
              (case (kar d)
                (:var (let ((b (cdr (lkp (kadr d) frame))))
                        (if (and (consp b) (scalar-ok (car b) v))
                            (mv :normal (put (kadr d) (cons (car b) v) frame) heap)
                          (mv (errst :type) frame heap))))
                ((:comp :elem)
                 (mv-let (err key intent) (obj-of (kadr d) frame)
                   (cond (err (mv (errst err) frame heap))
                         ((not (eq intent :inout)) (mv (errst :intent) frame heap))
                         ((not (int64p v)) (mv (errst :type) frame heap))
                         (t (let* ((comps (cdr (lkp key heap))) (p (lkp (kaddr d) comps)))
                              (cond ((not (consp p)) (mv (errst :type) frame heap))
                                    ((eq (kar d) :comp)
                                     (if (int64p (cdr p))
                                         (mv :normal frame (put key (put (kaddr d) v comps) heap))
                                       (mv (errst :type) frame heap)))
                                    (t (mv-let (err i) (f-ev (kadddr d) frame heap procs (1- fuel))
                                         (cond (err (mv (errst err) frame heap))
                                               ((not (and (farrayp (cdr p)) (integerp i))) (mv (errst :type) frame heap))
                                               ((not (and (<= 0 i) (< i (len (cddr p))))) (mv (errst :bounds) frame heap))
                                               (t (mv :normal frame
                                                      (put key (put (kaddr d) (cons :array (update-nth i v (cddr p))) comps)
                                                           heap))))))))))))
                (otherwise (mv (errst :syntax) frame heap)))))))
       (:if (mv-let (err c) (f-ev (kadr x) frame heap procs (1- fuel))
              (cond (err (mv (errst err) frame heap))
                    ((not (booleanp c)) (mv (errst :type) frame heap))
                    (c (f-ex-list (kaddr x) frame heap procs (1- fuel)))
                    (t (f-ex-list (kadddr x) frame heap procs (1- fuel))))))
       (:select (mv-let (err k) (f-ev (kadr x) frame heap procs (1- fuel))
                  (cond (err (mv (errst err) frame heap))
                        ((not (integerp k)) (mv (errst :type) frame heap))
                        (t (let ((arm (lkp k (kaddr x))))
                             (f-ex-list (if arm (kadr arm) (kadddr x)) frame heap procs (1- fuel)))))))
       (:do (mv-let (st fr h) (f-ex-list (kadr x) frame heap procs (1- fuel))
              (cond ((eq st :exit) (mv :normal fr h))
                    ((member-eq st '(:normal :cycle)) (f-ex x fr h procs (1- fuel)))
                    (t (mv st fr h)))))
       ((:cycle :exit :return) (mv (kar x) frame heap))
       (:call (let ((p (find-proc (kadr x) procs)))
                (if (not (eq (kar p) :subroutine)) (mv (errst :unknown-proc) frame heap)
                  (mv-let (err fr h) (f-invoke p (kaddr x) frame heap procs (1- fuel))
                    (if err (mv (errst err) frame heap) (mv :normal fr h))))))
       (otherwise (mv (errst :syntax) frame heap)))))

 (defun f-ex-list (xs frame heap procs fuel)
   (declare (xargs :guard t :measure (nfix fuel)))
   (cond ((not (posp fuel)) (mv (errst :fuel) frame heap))
         ((atom xs) (mv :normal frame heap))
         (t (mv-let (st fr h) (f-ex (car xs) frame heap procs (1- fuel))
              (if (eq st :normal) (f-ex-list (cdr xs) fr h procs (1- fuel)) (mv st fr h)))))))

(verify-guards f-ev)

; ---- running a program: the harness's prints and calls, in a main frame
;
; objects  ((name ((comp :scalar v) (comp :array (v0 v1 ...)) ...)) ...)
; vars     ((name type) ...), the main program's variables
; probes   (:print e) prints e's value; (:call s args) calls s
; The answer: the values printed, then (:error kind) if one stopped it.

(defun mk-comps (cs)
  (declare (xargs :guard t))
  (if (atom cs) nil
    (let ((c (car cs)))
      (cons (cons (kar c) (if (eq (kadr c) :array) (cons :array (true-list-fix (kaddr c))) (kaddr c)))
            (mk-comps (cdr cs))))))

(defun mk-heap (objs)
  (declare (xargs :guard t))
  (if (atom objs) nil
    (cons (cons (kar (car objs)) (mk-comps (kadr (car objs)))) (mk-heap (cdr objs)))))

(defun mk-main (objs frame)
  (declare (xargs :guard t))
  (if (atom objs) frame
    (mk-main (cdr objs) (put (kar (car objs)) (list* :obj :inout (kar (car objs))) frame))))

(defun run-probes (probes frame heap procs fuel)
  (declare (xargs :guard t))
  (if (atom probes) nil
    (let ((p (car probes)))
      (if (eq (kar p) :print)
          (mv-let (err v) (f-ev (kadr p) frame heap procs fuel)
            (if err (list (list :error err))
              (cons v (run-probes (cdr probes) frame heap procs fuel))))
        (mv-let (st fr h) (f-ex p frame heap procs fuel)
          (if (eq st :normal) (run-probes (cdr probes) fr h procs fuel)
            (list (if (errstp st) st (list :error :syntax)))))))))

(defun fsem-run (module objs vars probes fuel)
  (declare (xargs :guard t))
  (run-probes probes (mk-main objs (undef-locals vars nil)) (mk-heap objs) (kaddr module) fuel))

; ---- tests

(defmacro ev0 (x) `(mv-let (err v) (f-ev ',x nil nil nil 1000) (if err (list :error err) v)))

(assert-event (equal (ev0 (:add (:int 2) (:mul (:int 3) (:int 4)))) 14))
(assert-event (equal (ev0 (:sub (:neg (:huge)) (:int 1))) *int64-min*))
(assert-event (equal (ev0 (:add (:huge) (:int 1))) '(:error :overflow)))
(assert-event (equal (ev0 (:neg (:sub (:neg (:huge)) (:int 1)))) '(:error :overflow)))
(assert-event (equal (ev0 (:mul (:int 4294967296) (:int 4294967296))) '(:error :overflow)))
(assert-event (equal (ev0 (:not (:lt (:int 1099511627776) (:int 5)))) t))
(assert-event (equal (ev0 (:max (:int 0) (:int -7))) 0))
(assert-event (equal (ev0 (:var "x")) '(:error :type)))

; the generator's bnd40p, and a recursive function, and a subroutine
; updating an object in place with an INTENT(OUT) result
(defconst *test-module*
  '(:module "t"
    ((:function "bnd40p" t nil (("x_" :value :int64)) :logical nil
      ((:if (:not (:lt (:var "x_") (:int 0)))
            ((:assign (:var "r") (:not (:lt (:int 1099511627776) (:var "x_")))) (:return))
            ((:assign (:var "r") (:false)) (:return)))))
     (:function "fact" t t (("n_" :value :int64)) :int64 nil
      ((:if (:le (:var "n_") (:int 1))
            ((:assign (:var "r") (:int 1)))
            ((:assign (:var "r") (:mul (:var "n_") (:fcall "fact" ((:sub (:var "n_") (:int 1))))))))))
     (:subroutine "sum_to" nil (("st" :inout "s") ("r" :out :int64)) (("i" :int64))
      ((:assign (:var "i") (:int 0))
       (:assign (:var "r") (:int 0))
       (:do ((:if (:lt (:var "i") (:size "st" "a"))
                  ((:assign (:var "r") (:add (:var "r") (:elem "st" "a" (:var "i"))))
                   (:assign (:elem "st" "a" (:var "i")) (:int 0))
                   (:assign (:var "i") (:add (:var "i") (:int 1)))
                   (:cycle))
                  ((:exit)))))
       (:assign (:comp "st" "n") (:var "i"))))
     (:function "peek" t nil (("st" :in "s") ("i_" :value :int64)) :int64 nil
      ((:assign (:var "r") (:elem "st" "a" (:var "i_")))))
     (:subroutine "poke" nil (("st" :in "s")) nil
      ((:assign (:comp "st" "n") (:int 1))))
     (:function "noresult" t nil nil :int64 nil nil)
     (:function "pick" t nil (("k_" :value :int64)) :int64 nil
      ((:select (:var "k_")
                ((1 ((:assign (:var "r") (:int 10))))
                 (-1 ((:assign (:var "r") (:int 20)))))
                ((:assign (:var "r") (:int 30)))))))))

(assert-event (fmodule-p *test-module*))

(defconst *test-objs* '(("st" (("n" :scalar 0) ("a" :array (5 6 7))))))

(defmacro run0 (&rest probes)
  `(fsem-run *test-module* *test-objs* '(("o" :int64)) ',probes 100000))

(assert-event (equal (run0 (:print (:fcall "bnd40p" ((:int 5))))
                           (:print (:fcall "bnd40p" ((:int -1))))
                           (:print (:fcall "fact" ((:int 20))))
                           (:print (:fcall "pick" ((:int -1))))
                           (:print (:fcall "pick" ((:int 2)))))
                     '(t nil 2432902008176640000 20 30)))
(assert-event (equal (run0 (:print (:fcall "fact" ((:int 21))))) '((:error :overflow))))
(assert-event (equal (run0 (:call "sum_to" ((:var "st") (:var "o")))
                           (:print (:var "o")) (:print (:comp "st" "n")) (:print (:elem "st" "a" (:int 2))))
                     '(18 3 0)))
(assert-event (equal (run0 (:print (:fcall "peek" ((:var "st") (:int 3))))) '((:error :bounds))))
(assert-event (equal (run0 (:call "poke" ((:var "st")))) '((:error :intent))))
(assert-event (equal (run0 (:print (:var "o"))) '((:error :undefined))))
(assert-event (equal (run0 (:print (:fcall "noresult" nil))) '((:error :undefined))))
(assert-event (equal (fsem-run *test-module* *test-objs* nil '((:do nil)) 1000) '((:error :fuel))))
