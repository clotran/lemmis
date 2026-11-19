; gen-st-xrfb: p-sorc-r discharged (GEN.md "What remains" 4c, step 3).
; hpg-run-from-batch's callees hpg_run_pop and hpg_run_new are now
; g-st-module's output (gen-st's extern roles, gen-st-heap's *heapg-xmod*;
; check-gen compares their text with heap_gen.inc). Each is run
; symbolically on hs's entry laid out by hs-rep: its hp_* reads and writes
; are fsem's :extern procedures on "%ext" (fsem ext-op), a write to "%ext"
; is again an hs-rep (put-ext-hs-rep), so the procedure answers its ACL2
; value (`rp-ok`, `rn-ok`). Then p-sorc-r holds of any procs holding these
; procedures, hpg_add, hpg_s64 and the externs (`xr-finds`), and
; hpg-run-from-batch is correct with no hypothesis on the procedures past
; that (`hpg-run-from-batch-fortran-correct-x`).
;
; hp_n_arena is read as h-aival's length (hpg_run_new reads only that one
; of the arena's arrays).

(in-package "ACL2")

(include-book "gen-st-ext")
(include-book "gen-st-rfb")
(include-book "gen-stcsorc")
(include-book "gen-stok")

; ---- the procedures

(defconst *xr-fns*
  (mv-let (e ps) (g-module (list (assoc-eq 'hpg-s64 *heapg-st-raw*) (assoc-eq 'hpg-add *heapg-st-raw*)) nil)
    (if e nil ps)))
(defconst *x-s64* (find-proc "hpg_s64" *xr-fns*))
(defconst *x-add* (find-proc "hpg_add" *xr-fns*))
(defconst *rp-proc* (find-proc "hpg_run_pop" *heapg-xmod*))
(defconst *rn-proc* (find-proc "hpg_run_new" *heapg-xmod*))

(defconst *xr-externs*
  `((:extern "hp_n_nrb" :size ,*h-nrbi*) (:extern "hp_nrb" :elem ,*h-nrbi*) (:extern "hp_set_nrb" :set-elem ,*h-nrbi*)
    (:extern "hp_n_rb" :size ,*h-rbi*) (:extern "hp_rb" :elem ,*h-rbi*)
    (:extern "hp_n_chead" :size ,*h-cheadi*) (:extern "hp_chead" :elem ,*h-cheadi*)
    (:extern "hp_set_chead" :set-elem ,*h-cheadi*)
    (:extern "hp_n_arena" :size ,*h-aivali*) (:extern "hp_aival" :elem ,*h-aivali*)
    (:extern "hp_acap" :scalar ,*h-acap*)
    (:extern "hp_aused" :scalar ,*h-aused*) (:extern "hp_set_aused" :set-scalar ,*h-aused*)
    (:extern "hp_areu" :scalar ,*h-areu*) (:extern "hp_set_areu" :set-scalar ,*h-areu*)
    (:extern "hp_afre" :scalar ,*h-afre*) (:extern "hp_set_afre" :set-scalar ,*h-afre*)
    (:extern "hp_asince" :scalar ,*h-asince*) (:extern "hp_set_asince" :set-scalar ,*h-asince*)))

(assert-event (and *x-s64* *x-add* *rp-proc* *rn-proc*
                   (fmodule-p (list :module "m" (append *xr-externs* (list *x-s64* *x-add* *rp-proc* *rn-proc*))))))

(defun xr-finds-fn (es)
  (declare (xargs :mode :program))
  (if (atom es) nil
    (cons `(equal (find-proc ,(cadr (car es)) procs) ',(car es)) (xr-finds-fn (cdr es)))))

(make-event
 `(defmacro xr-finds ()
    '(and ,@(xr-finds-fn *xr-externs*)
          (equal (find-proc "hpg_s64" procs) *x-s64*) (equal (find-proc "hpg_add" procs) *x-add*)
          (equal (find-proc "hpg_run_pop" procs) *rp-proc*) (equal (find-proc "hpg_run_new" procs) *rn-proc*))))

; ---- the expansions a symbolic run needs: f-ev of every expression, f-ex of every :xcall statement

(mutual-recursion
 (defun xr-exprs (x)
   (declare (xargs :mode :program))
   (cond ((atom x) nil)
         ((member-eq (car x) '(:int :true :false :var :huge)) (list x))
         ((eq (car x) :xcall) (cons x (xr-exprs-l (cadddr x))))
         ((eq (car x) :fcall) (cons x (xr-exprs-l (caddr x))))
         (t (cons x (xr-exprs-l (cdr x))))))
 (defun xr-exprs-l (xs)
   (declare (xargs :mode :program))
   (if (atom xs) nil (append (xr-exprs (car xs)) (xr-exprs-l (cdr xs))))))

(mutual-recursion
 (defun xr-stmt (s)
   ; (mv exprs xcall-stmts)
   (declare (xargs :mode :program))
   (case (car s)
     (:assign (mv (append (xr-exprs (caddr s)) (if (eq (car (cadr s)) :elem) (xr-exprs (cadddr (cadr s))) nil)) nil))
     (:if (mv-let (e1 x1) (xr-stmts (caddr s))
            (mv-let (e2 x2) (xr-stmts (cadddr s))
              (mv (append (xr-exprs (cadr s)) e1 e2) (append x1 x2)))))
     (:xcall (mv (xr-exprs-l (cadddr s)) (list s)))
     (:call (mv (xr-exprs-l (caddr s)) nil))
     (:do (xr-stmts (cadr s)))
     (otherwise (mv nil nil))))
 (defun xr-stmts (ss)
   (declare (xargs :mode :program))
   (if (atom ss) (mv nil nil)
     (mv-let (e1 x1) (xr-stmt (car ss))
       (mv-let (e2 x2) (xr-stmts (cdr ss))
         (mv (append e1 e2) (append x1 x2)))))))

(defun xr-proc-body (p) (declare (xargs :mode :program)) (if (eq (car p) :function) (nth 7 p) (nth 5 p)))

(defun xr-ev-hints (es)
  (declare (xargs :mode :program))
  (if (atom es) nil (cons `(:free (fr h k) (f-ev ',(car es) fr h procs k)) (xr-ev-hints (cdr es)))))
(defun xr-ex-hints (ss)
  (declare (xargs :mode :program))
  (if (atom ss) nil (cons `(:free (fr h k) (f-ex ',(car ss) fr h procs k)) (xr-ex-hints (cdr ss)))))

; ps: the procedures run (the callees' too)
(defun xr-expands (ps)
  (declare (xargs :mode :program))
  (if (atom ps) nil
    (mv-let (es xs) (xr-stmts (xr-proc-body (car ps)))
      (append (xr-ev-hints (remove-duplicates-equal es)) (xr-ex-hints (remove-duplicates-equal xs))
              (xr-expands (cdr ps))))))

; ---- the entry: an "%ext" write to an hs-rep is an hs-rep

(defthm put-ext-commute
  (implies (and (not (equal k "%ext")) (consp (lkp "%ext" al)))
           (equal (put "%ext" x (put k v al)) (put k v (put "%ext" x al))))
  :hints (("Goal" :in-theory (enable put))))

(defthm put-ext-hs-rep
  (implies (and (equal (nth 0 h2) (nth 0 h)) (equal (nth 10 h2) (nth 10 h)) (equal (nth 11 h2) (nth 11 h))
                (equal (nth 12 h2) (nth 12 h)) (equal (nth 13 h2) (nth 13 h)) (equal (nth 14 h2) (nth 14 h))
                (equal (nth 15 h2) (nth 15 h)) (equal (nth 16 h2) (nth 16 h)) (equal (nth 31 h2) (nth 31 h))
                (equal (nth 32 h2) (nth 32 h)) (equal (nth 33 h2) (nth 33 h)) (equal (nth 34 h2) (nth 34 h)))
           (equal (put "%ext" (hs-ext h2) (hs-rep c h)) (hs-rep c h2)))
  :hints (("Goal" :in-theory (e/d (hs-rep) (hs-ext hs-del put)))))

; per extern field i: its write (fsem's ext-op on the entry) is the stobj's update-nth
(defmacro xr-ext-write (name i)
  `(progn
     (defthm ,(packn (list name '-ext)) (equal (update-nth ,i z (hs-ext h)) (hs-ext (update-nth ,i z h)))
       :hints (("Goal" :in-theory (enable hs-ext))))
     (defthm ,(packn (list name '-nth)) (equal (nth ,i (hs-ext h)) (nth ,i h))
       :hints (("Goal" :in-theory (enable hs-ext))))
     (defthm ,name (equal (put "%ext" (hs-ext (update-nth ,i z h)) (hs-rep c h)) (hs-rep c (update-nth ,i z h)))
       :hints (("Goal" :in-theory (disable hs-ext hs-rep put)
                :use ((:instance put-ext-hs-rep (h2 (update-nth ,i z h)))))))))

(xr-ext-write xw-nrb *h-nrbi*)
(xr-ext-write xw-rb *h-rbi*)
(xr-ext-write xw-chead *h-cheadi*)
(xr-ext-write xw-aival *h-aivali*)
(xr-ext-write xw-acap *h-acap*)
(xr-ext-write xw-aused *h-aused*)
(xr-ext-write xw-areu *h-areu*)
(xr-ext-write xw-afre *h-afre*)
(xr-ext-write xw-asince *h-asince*)

(in-theory (disable hs-ext))


; ---- each callee's procedure answers its ACL2 value on the entry's stobj, the result to the CALL's d

(defmacro xr-hyps ()
  '(and (xr-finds) (hpgp hpg) (hpg-rn-ok hpg)
        (equal (cdr (lkp ob caller)) (list* :obj :inout key))
        (consp (cdr (lkp d caller))) (equal (cadr (lkp d caller)) :int64)
        (dr-heap-at heap key cm hpg)
        (integerp fuel) (< 70 fuel)))

(nt-arr-lemma h-rb-int64 h-rbp)
(nt-arr-lemma h-nrb-int64 h-nrbp)
(nt-arr-lemma h-chead-int64 h-cheadp)
(nt-arr-lemma h-aival-int64 h-aivalp)

(defthm hpgp-xr-arrs
  (implies (hpgp hpg)
           (and (h-rbp (nth *h-rbi* hpg)) (h-nrbp (nth *h-nrbi* hpg)) (h-cheadp (nth *h-cheadi* hpg))
                (h-aivalp (nth *h-aivali* hpg))))
  :hints (("Goal" :in-theory (e/d (hpgp) (h-rbp h-nrbp h-cheadp h-aivalp)))))

(defmacro xr-tl (name recog)
  `(defthm ,name (implies (,recog x) (true-listp x)) :rule-classes :forward-chaining))
(xr-tl h-rbp-tl h-rbp)
(xr-tl h-nrbp-tl h-nrbp)
(xr-tl h-cheadp-tl h-cheadp)
(xr-tl h-aivalp-tl h-aivalp)
(in-theory (disable h-rbp h-nrbp h-cheadp h-aivalp))

(defthm hpgp-xr-tl
  (implies (hpgp hpg)
           (and (true-listp (nth *h-rbi* hpg)) (true-listp (nth *h-nrbi* hpg)) (true-listp (nth *h-cheadi* hpg))
                (true-listp (nth *h-aivali* hpg))))
  :hints (("Goal" :in-theory (disable hpgp hpgp-xr-arrs h-rbp-tl h-nrbp-tl h-cheadp-tl h-aivalp-tl)
           :use (hpgp-xr-arrs (:instance h-rbp-tl (x (nth *h-rbi* hpg))) (:instance h-nrbp-tl (x (nth *h-nrbi* hpg)))
                 (:instance h-cheadp-tl (x (nth *h-cheadi* hpg))) (:instance h-aivalp-tl (x (nth *h-aivali* hpg)))))))


; an element read within the array is an int64: integerp by type, the bounds by linear
(defmacro xr-elem-lemma (name idx lem)
  `(defthm ,name
     (implies (and (hpgp hpg) (natp j) (< j (len (nth ,idx hpg))))
              (and (integerp (nth j (nth ,idx hpg)))
                   (<= -9223372036854775808 (nth j (nth ,idx hpg)))
                   (<= (nth j (nth ,idx hpg)) 9223372036854775807)))
     :rule-classes ((:type-prescription :corollary (implies (and (hpgp hpg) (natp j) (< j (len (nth ,idx hpg))))
                                                            (integerp (nth j (nth ,idx hpg)))))
                    (:linear :corollary (implies (and (hpgp hpg) (natp j) (< j (len (nth ,idx hpg))))
                                                 (and (<= -9223372036854775808 (nth j (nth ,idx hpg)))
                                                      (<= (nth j (nth ,idx hpg)) 9223372036854775807)))))
     :hints (("Goal" :in-theory (e/d (int64p) (hpgp ,lem)) :use (hpgp-xr-arrs (:instance ,lem (l (nth ,idx hpg))))))))

(xr-elem-lemma xr-rb-elem *h-rbi* h-rb-int64)
(xr-elem-lemma xr-nrb-elem *h-nrbi* h-nrb-int64)
(xr-elem-lemma xr-chead-elem *h-cheadi* h-chead-int64)
(xr-elem-lemma xr-aival-elem *h-aivali* h-aival-int64)
; what hpg-rn-ok gives the runs: the arrays' lengths and the counters within 2^40
(defthm xr-rn-facts
  (implies (hpg-rn-ok hpg)
           (and (<= (len (nth *h-rbi* hpg)) *hb40*) (<= (len (nth *h-nrbi* hpg)) *hb40*)
                (<= (len (nth *h-cheadi* hpg)) *hb40*) (<= (len (nth *h-aivali* hpg)) *hb40*)
                (natp (nth *h-aused* hpg)) (<= (nth *h-aused* hpg) *hb40*)
                (natp (nth *h-acap* hpg)) (<= (nth *h-acap* hpg) *hb40*)
                (natp (nth *h-areu* hpg)) (<= (nth *h-areu* hpg) *hb40*)
                (natp (nth *h-afre* hpg)) (<= (nth *h-afre* hpg) *hb40*)
                (natp (nth *h-asince* hpg)) (<= (nth *h-asince* hpg) *hb40*)))
  :rule-classes ((:forward-chaining :trigger-terms ((hpg-rn-ok hpg))))
  :hints (("Goal" :in-theory (enable hpg-rn-ok))))

; ---- hpg_run_pop: the procedure's shape, its invocation, its body's run

(defconst *rp-ls* (nth 4 *rp-proc*))
(defconst *rp-body* (nth 5 *rp-proc*))

(defthm rp-proc-shape
  (equal *rp-proc*
         (list :subroutine "hpg_run_pop" (nth 2 *rp-proc*)
               (list (list "hs" :inout "heap_state") (list "c_" :value :int64) (list "r" :out :int64))
               *rp-ls* *rp-body*))
  :rule-classes nil)

(defmacro xr-fr1 (ls o)
  `(undef-locals ,ls (put "r" (cons :int64 :undef) (put "c_" (cons :int64 c) (put ,o (list* :obj :inout key) nil)))))

(defthm f-invoke-sub-r1
  (implies (and (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (consp (cdr (lkp d caller))) (equal (cadr (lkp d caller)) :int64)
                (int64p c) (integerp fuel) (< 10 fuel)
                (equal (mv-nth 0 (f-ex-list body (xr-fr1 ls o) heap procs (1- fuel))) :normal))
           (equal (f-invoke (list :subroutine nm rec
                                  (list (list o :inout cc) (list "c_" :value :int64) (list "r" :out :int64))
                                  ls body)
                            (list (list :var ob) (g-lit c) (list :var d)) caller heap procs fuel)
                  (mv nil (copy-out (list (cons "r" d)) (mv-nth 1 (f-ex-list body (xr-fr1 ls o) heap procs (1- fuel))) caller)
                      (mv-nth 2 (f-ex-list body (xr-fr1 ls o) heap procs (1- fuel))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-ex-list undef-locals g-lit copy-out put)
           :expand ((:free (p) (f-invoke p (list (list :var ob) (g-lit c) (list :var d)) caller heap procs fuel))
                    (:free (ds as callee outs f) (f-bind ds as caller callee outs heap procs f))))))

(make-event
 `(defthm rp-run
    (implies (and (xr-finds) (hpgp hpg) (hpg-rn-ok hpg) (natp c) (int64p c)
                  (dr-heap-at heap key cm hpg) (integerp k) (< 50 k))
             (let ((r (f-ex-list *rp-body* (xr-fr1 *rp-ls* "hs") heap procs k)))
               (and (equal (mv-nth 0 r) :normal)
                    (equal (cdr (lkp "r" (mv-nth 1 r))) (cons :int64 (mv-nth 0 (hpg-run-pop c hpg))))
                    (equal (mv-nth 2 r) (put key (hs-rep cm (mv-nth 1 (hpg-run-pop c hpg))) heap)))))
    :hints (("Goal" :do-not-induct t
             :cases ((not (and (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg)))))
                     (and (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg)))
                          (not (and (< 0 (nth c (nth *h-nrbi* hpg))) (<= (nth c (nth *h-nrbi* hpg)) 64)
                                    (< (+ (* (- c 1) 64) (nth c (nth *h-nrbi* hpg))) (len (nth *h-rbi* hpg))))))
                     (and (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg)))
                          (< 0 (nth c (nth *h-nrbi* hpg))) (<= (nth c (nth *h-nrbi* hpg)) 64)
                          (< (+ (* (- c 1) 64) (nth c (nth *h-nrbi* hpg))) (len (nth *h-rbi* hpg)))
                          (not (< 0 (nth (+ (* (- c 1) 64) (nth c (nth *h-nrbi* hpg))) (nth *h-rbi* hpg)))))
                     (and (<= 1 c) (<= c 8) (< c (len (nth *h-nrbi* hpg)))
                          (< 0 (nth c (nth *h-nrbi* hpg))) (<= (nth c (nth *h-nrbi* hpg)) 64)
                          (< (+ (* (- c 1) 64) (nth c (nth *h-nrbi* hpg))) (len (nth *h-rbi* hpg)))
                          (< 0 (nth (+ (* (- c 1) 64) (nth c (nth *h-nrbi* hpg))) (nth *h-rbi* hpg)))))
             :in-theory (e/d (hpg-run-pop h-nrbi h-rbi h-nrb-length h-rb-length update-h-nrbi obj-of int64p
                              ext-op ext-read-p ext-write-p ext-dums)
                             (f-ev f-bind f-ex hs-rep hpgp hpg-rn-ok dr-heap-at))
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      ,@(xr-expands (list *rp-proc*)))))))


(defthm rp-ok
  (implies (and (xr-hyps) (natp c) (int64p c))
           (equal (f-invoke *rp-proc* (list (list :var ob) (g-lit c) (list :var d)) caller heap procs fuel)
                  (mv nil (put d (cons :int64 (mv-nth 0 (hpg-run-pop c hpg))) caller)
                      (put key (hs-rep cm (mv-nth 1 (hpg-run-pop c hpg))) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (int64p) (f-invoke f-ex-list hpg-run-pop hpgp hpg-rn-ok g-lit undef-locals put
                                     f-invoke-sub-r1 rp-run hs-rep dr-heap-at f-ex-list-open f-ex-list-nil))
           :expand ((:free (fr) (copy-out (list (cons "r" d)) fr caller)) (:free (fr) (copy-out nil fr caller)))
           :use (rp-proc-shape (:instance rp-run (k (1- fuel)))
                 (:instance f-invoke-sub-r1 (o "hs") (cc "heap_state") (nm "hpg_run_pop")
                            (rec (nth 2 *rp-proc*)) (ls *rp-ls*) (body *rp-body*))))))

; ---- hpg_run_new (two values, through gen-st-rfb's f-invoke-sub-r); its hpg_add and hpg_s64 calls run too

(defconst *rn-ls* (nth 4 *rn-proc*))
(defconst *rn-body* (nth 5 *rn-proc*))

(defthm rn-proc-shape
  (equal *rn-proc*
         (list :subroutine "hpg_run_new" (nth 2 *rn-proc*)
               (list (list "hs" :inout "heap_state") (list "c_" :value :int64) (list "l_" :value :int64)
                     (list "r" :out :int64))
               *rn-ls* *rn-body*))
  :rule-classes nil)

(defmacro rn-fr0 ()
  '(undef-locals *rn-ls* (put "r" (cons :int64 :undef) (put "l_" (cons :int64 l) (put "c_" (cons :int64 c)
                                                                                    (put "hs" (list* :obj :inout key) nil))))))

(defmacro rn-h ()
  '(if (< c (len (nth *h-cheadi* hpg))) (nth c (nth *h-cheadi* hpg)) 0))

(make-event
 `(defthm rn-run
    (implies (and (xr-finds) (hpgp hpg) (hpg-rn-ok hpg) (natp c) (int64p c) (natp l) (<= l *hb40*)
                  (dr-heap-at heap key cm hpg) (integerp k) (< 60 k))
             (let ((r (f-ex-list *rn-body* (rn-fr0) heap procs k)))
               (and (equal (mv-nth 0 r) :normal)
                    (equal (cdr (lkp "r" (mv-nth 1 r))) (cons :int64 (mv-nth 0 (hpg-run-new c l hpg))))
                    (equal (mv-nth 2 r) (put key (hs-rep cm (mv-nth 1 (hpg-run-new c l hpg))) heap)))))
    :hints (("Goal" :do-not-induct t
             :cases ((and (< 0 (rn-h)) (< (rn-h) (len (nth *h-aivali* hpg))))
                     (and (not (and (< 0 (rn-h)) (< (rn-h) (len (nth *h-aivali* hpg)))))
                          (< 0 l) (not (< (nth *h-acap* hpg) (+ (nth *h-aused* hpg) l))))
                     (and (not (and (< 0 (rn-h)) (< (rn-h) (len (nth *h-aivali* hpg)))))
                          (not (and (< 0 l) (not (< (nth *h-acap* hpg) (+ (nth *h-aused* hpg) l)))))))
             :in-theory (e/d (hpg-run-new hpg-add hpg-s64 h-cheadi h-aivali h-chead-length h-aival-length update-h-cheadi
                              h-acap h-aused h-areu h-afre h-asince update-h-aused update-h-areu update-h-afre
                              update-h-asince obj-of int64p ext-op ext-read-p ext-write-p ext-dums)
                             (f-ev f-bind f-ex f-invoke hs-rep hpgp hpg-rn-ok dr-heap-at))
             :expand ((:free (ds as cl ce outs h k) (f-bind ds as cl ce outs h procs k))
                      (:free (as cl h k) (f-invoke ',*x-add* as cl h procs k))
                      (:free (as cl h k) (f-invoke ',*x-s64* as cl h procs k))
                      ,@(xr-expands (list *rn-proc* *x-add* *x-s64*)))))))

(defthm rn-ok
  (implies (and (xr-hyps) (natp c) (int64p c) (natp l) (<= l *hb40*))
           (equal (f-invoke *rn-proc* (list (list :var ob) (g-lit c) (g-lit l) (list :var d)) caller heap procs fuel)
                  (mv nil (put d (cons :int64 (mv-nth 0 (hpg-run-new c l hpg))) caller)
                      (put key (hs-rep cm (mv-nth 1 (hpg-run-new c l hpg))) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (int64p) (f-invoke f-ex-list hpg-run-new hpgp hpg-rn-ok g-lit undef-locals put
                                     f-invoke-sub-r rn-run hs-rep dr-heap-at f-ex-list-open f-ex-list-nil))
           :expand ((:free (fr) (copy-out (list (cons "r" d)) fr caller)) (:free (fr) (copy-out nil fr caller)))
           :use (rn-proc-shape (:instance rn-run (k (1- fuel)))
                 (:instance f-invoke-sub-r (o "hs") (cc "heap_state") (nm "hpg_run_new")
                            (rec (nth 2 *rn-proc*)) (ls *rn-ls*) (body *rn-body*))))))


; ---- the same from a CALL's argument codes (sv answers them): f-bind sees only their values

(defmacro xr-cv (cc) `(and (not (mv-nth 0 (sv ,cc caller heap))) (int64p (mv-nth 1 (sv ,cc caller heap)))))

(defthm xr-bind1
  (implies (and (xr-cv cc) (integerp k) (< (+ 6 (acl2-count cc)) k))
           (equal (f-bind (list '("hs" :inout "heap_state") (list "c_" :value :int64) '("r" :out :int64)) (list (list :var ob) cc (list :var d)) caller nil nil heap procs k)
                  (f-bind (list '("hs" :inout "heap_state") (list "c_" :value :int64) '("r" :out :int64)) (list (list :var ob) (g-lit (mv-nth 1 (sv cc caller heap))) (list :var d))
                          caller nil nil heap procs k)))
  :hints (("Goal" :do-not-induct t :in-theory (disable sv g-lit put obj-of f-ev f-invoke f-ex f-ex-list)
           :expand ((:free (as ce outs) (f-bind (list '("hs" :inout "heap_state") (list "c_" :value :int64) '("r" :out :int64)) as caller ce outs heap procs k))
                    (:free (as ce outs) (f-bind (list (list "c_" :value :int64) '("r" :out :int64)) as caller ce outs heap procs (1- k)))))))

(defthm xr-bind2
  (implies (and (xr-cv cc) (xr-cv cl) (integerp k) (< (+ 8 (acl2-count cc) (acl2-count cl)) k))
           (equal (f-bind (list '("hs" :inout "heap_state") (list "c_" :value :int64) (list "l_" :value :int64) '("r" :out :int64)) (list (list :var ob) cc cl (list :var d))
                          caller nil nil heap procs k)
                  (f-bind (list '("hs" :inout "heap_state") (list "c_" :value :int64) (list "l_" :value :int64) '("r" :out :int64))
                          (list (list :var ob) (g-lit (mv-nth 1 (sv cc caller heap))) (g-lit (mv-nth 1 (sv cl caller heap))) (list :var d))
                          caller nil nil heap procs k)))
  :hints (("Goal" :do-not-induct t :in-theory (disable sv g-lit put obj-of f-ev f-invoke f-ex f-ex-list)
           :expand ((:free (as ce outs) (f-bind (list '("hs" :inout "heap_state") (list "c_" :value :int64) (list "l_" :value :int64) '("r" :out :int64))
                                                as caller ce outs heap procs k))
                    (:free (as ce outs) (f-bind (list (list "c_" :value :int64) (list "l_" :value :int64) '("r" :out :int64))
                                                as caller ce outs heap procs (1- k)))
                    (:free (as ce outs) (f-bind (list (list "l_" :value :int64) '("r" :out :int64)) as caller ce outs heap procs (- k 2)))))))

(defthm rp-okc
  (implies (and (xr-hyps) (xr-cv cc) (natp (mv-nth 1 (sv cc caller heap))) (< (+ 70 (acl2-count cc)) fuel))
           (equal (f-invoke *rp-proc* (list (list :var ob) cc (list :var d)) caller heap procs fuel)
                  (mv nil (put d (cons :int64 (mv-nth 0 (hpg-run-pop (mv-nth 1 (sv cc caller heap)) hpg))) caller)
                      (put key (hs-rep cm (mv-nth 1 (hpg-run-pop (mv-nth 1 (sv cc caller heap)) hpg))) heap))))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-invoke f-bind sv g-lit rp-ok xr-bind1 hpg-run-pop hs-rep)
           :use ((:instance rp-ok (c (mv-nth 1 (sv cc caller heap))))
                 (:instance f-invoke-same-bind (p *rp-proc*) (a1 (list (list :var ob) cc (list :var d)))
                            (a2 (list (list :var ob) (g-lit (mv-nth 1 (sv cc caller heap))) (list :var d))))
                 (:instance xr-bind1 (k (1- fuel)))))))

(defthm rn-okc
  (implies (and (xr-hyps) (xr-cv cc) (xr-cv cl) (natp (mv-nth 1 (sv cc caller heap)))
                (natp (mv-nth 1 (sv cl caller heap))) (<= (mv-nth 1 (sv cl caller heap)) *hb40*)
                (< (+ 70 (acl2-count cc) (acl2-count cl)) fuel))
           (equal (f-invoke *rn-proc* (list (list :var ob) cc cl (list :var d)) caller heap procs fuel)
                  (mv nil (put d (cons :int64 (mv-nth 0 (hpg-run-new (mv-nth 1 (sv cc caller heap))
                                                                     (mv-nth 1 (sv cl caller heap)) hpg))) caller)
                      (put key (hs-rep cm (mv-nth 1 (hpg-run-new (mv-nth 1 (sv cc caller heap))
                                                                 (mv-nth 1 (sv cl caller heap)) hpg))) heap))))
  :hints (("Goal" :do-not-induct t :in-theory (disable f-invoke f-bind sv g-lit rn-ok xr-bind2 hpg-run-new hs-rep)
           :use ((:instance rn-ok (c (mv-nth 1 (sv cc caller heap))) (l (mv-nth 1 (sv cl caller heap))))
                 (:instance f-invoke-same-bind (p *rn-proc*) (a1 (list (list :var ob) cc cl (list :var d)))
                            (a2 (list (list :var ob) (g-lit (mv-nth 1 (sv cc caller heap)))
                                      (g-lit (mv-nth 1 (sv cl caller heap))) (list :var d))))
                 (:instance xr-bind2 (k (1- fuel)))))))

; ---- p-sorc-r: a CALL the oracle answers, f-ex answers the same

(defthm xr-count-args
  (implies (equal (kar x) :call)
           (and (< (acl2-count (cadr (kaddr x))) (acl2-count x)) (< (acl2-count (caddr (kaddr x))) (acl2-count x))
                (< (+ (acl2-count (cadr (kaddr x))) (acl2-count (caddr (kaddr x)))) (acl2-count x))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable kaddr kar))))


; the CALL statement: f-ex finds the procedure and invokes it
(defthm xr-ex-rp
  (implies (and (xr-hyps) (equal (kar x) :call) (equal (kadr x) "hpg_run_pop")
                (equal (kaddr x) (list (list :var ob) cc (list :var d)))
                (xr-cv cc) (natp (mv-nth 1 (sv cc caller heap))) (< (+ 71 (acl2-count cc)) fuel))
           (equal (f-ex x caller heap procs fuel)
                  (mv :normal (put d (cons :int64 (mv-nth 0 (hpg-run-pop (mv-nth 1 (sv cc caller heap)) hpg))) caller)
                      (put key (hs-rep cm (mv-nth 1 (hpg-run-pop (mv-nth 1 (sv cc caller heap)) hpg))) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-invoke rp-okc hs-rep hpgp hpg-rn-ok sv hpg-run-pop dr-heap-at put)
           :expand ((f-ex x caller heap procs fuel))
           :use ((:instance rp-okc (fuel (1- fuel)))))))

(defthm xr-ex-rn
  (implies (and (xr-hyps) (equal (kar x) :call) (equal (kadr x) "hpg_run_new")
                (equal (kaddr x) (list (list :var ob) cc cl (list :var d)))
                (xr-cv cc) (xr-cv cl) (natp (mv-nth 1 (sv cc caller heap)))
                (natp (mv-nth 1 (sv cl caller heap))) (<= (mv-nth 1 (sv cl caller heap)) *hb40*)
                (< (+ 71 (acl2-count cc) (acl2-count cl)) fuel))
           (equal (f-ex x caller heap procs fuel)
                  (mv :normal (put d (cons :int64 (mv-nth 0 (hpg-run-new (mv-nth 1 (sv cc caller heap))
                                                                         (mv-nth 1 (sv cl caller heap)) hpg))) caller)
                      (put key (hs-rep cm (mv-nth 1 (hpg-run-new (mv-nth 1 (sv cc caller heap))
                                                                 (mv-nth 1 (sv cl caller heap)) hpg))) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-invoke rn-okc hs-rep hpgp hpg-rn-ok sv hpg-run-new dr-heap-at put)
           :expand ((f-ex x caller heap procs fuel))
           :use ((:instance rn-okc (fuel (1- fuel)))))))

; what the oracle answering says of the CALL's arguments, and what it answers

(defthm xr-scv-noshape
  (implies (not (rfb-shape name a)) (mv-nth 0 (s-call-val-r name a fr heap)))
  :hints (("Goal" :in-theory (e/d (s-call-val-r) (rfb-shape sv obj-of hs-hpg dr-heap-at hpgp hpg-rn-ok hs-rep)))))

(defthm xr-scv-shape
  (and (implies (not (mv-nth 0 (s-call-val-r "hpg_run_pop" a fr heap)))
                (equal a (list (list :var (kadr (car a))) (cadr a) (list :var (kadr (caddr a))))))
       (implies (not (mv-nth 0 (s-call-val-r "hpg_run_new" a fr heap)))
                (equal a (list (list :var (kadr (car a))) (cadr a) (caddr a) (list :var (kadr (cadddr a)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(rfb-shape xr-scv-noshape) (theory 'minimal-theory))
           :use ((:instance xr-scv-noshape (name "hpg_run_pop")) (:instance xr-scv-noshape (name "hpg_run_new"))))))

(defmacro xs-key () '(mv-nth 1 (obj-of ob fr)))
(defmacro xs-e () '(cdr (lkp (xs-key) heap)))
(defmacro xs-c () '(mv-nth 1 (sv cc fr heap)))
(defmacro xs-l () '(mv-nth 1 (sv cl fr heap)))

(defthm xr-scv-rp
  (implies (and (equal name "hpg_run_pop") (equal a (list (list :var ob) cc (list :var d)))
                (not (mv-nth 0 (s-call-val-r name a fr heap))))
           (let ((hpg (hs-hpg (xs-e))))
             (and (equal (cdr (lkp ob fr)) (list* :obj :inout (xs-key)))
                  (consp (cdr (lkp d fr))) (equal (cadr (lkp d fr)) :int64)
                  (dr-heap-at heap (xs-key) (xs-e) hpg) (hpgp hpg) (hpg-rn-ok hpg)
                  (not (mv-nth 0 (sv cc fr heap))) (natp (xs-c)) (int64p (xs-c))
                  (equal (mv-nth 1 (s-call-val-r name a fr heap))
                         (put d (cons :int64 (mv-nth 0 (hpg-run-pop (xs-c) hpg))) fr))
                  (equal (mv-nth 2 (s-call-val-r name a fr heap))
                         (put (xs-key) (hs-rep (xs-e) (mv-nth 1 (hpg-run-pop (xs-c) hpg))) heap)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (s-call-val-r rfb-res) (hs-rep hpgp hpg-rn-ok sv hpg-run-pop hpg-run-new hs-hpg dr-heap-at
                                                   dr-heap-at-lkp dr-heap-at-self put obj-of))
           :use ((:instance obj-of-binding (caller fr))))))

(defthm xr-scv-rn
  (implies (and (equal name "hpg_run_new") (equal a (list (list :var ob) cc cl (list :var d)))
                (not (mv-nth 0 (s-call-val-r name a fr heap))))
           (let ((hpg (hs-hpg (xs-e))))
             (and (equal (cdr (lkp ob fr)) (list* :obj :inout (xs-key)))
                  (consp (cdr (lkp d fr))) (equal (cadr (lkp d fr)) :int64)
                  (dr-heap-at heap (xs-key) (xs-e) hpg) (hpgp hpg) (hpg-rn-ok hpg)
                  (not (mv-nth 0 (sv cc fr heap))) (natp (xs-c)) (int64p (xs-c))
                  (not (mv-nth 0 (sv cl fr heap))) (natp (xs-l)) (<= (xs-l) *hb40*) (int64p (xs-l))
                  (equal (mv-nth 1 (s-call-val-r name a fr heap))
                         (put d (cons :int64 (mv-nth 0 (hpg-run-new (xs-c) (xs-l) hpg))) fr))
                  (equal (mv-nth 2 (s-call-val-r name a fr heap))
                         (put (xs-key) (hs-rep (xs-e) (mv-nth 1 (hpg-run-new (xs-c) (xs-l) hpg))) heap)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (s-call-val-r rfb-res) (hs-rep hpgp hpg-rn-ok sv hpg-run-pop hpg-run-new hs-hpg dr-heap-at
                                                   dr-heap-at-lkp dr-heap-at-self put obj-of))
           :use ((:instance obj-of-binding (caller fr))))))

; the CALL from its statement x: its arguments in the shape the oracle asks
(defmacro xa () '(kaddr x))
(defmacro x-ob () '(kadr (car (xa))))
(defmacro x-key () '(mv-nth 1 (obj-of (x-ob) fr)))
(defmacro x-e () '(cdr (lkp (x-key) heap)))

(defthm xr-call-rp
  (implies (and (xr-finds) (equal (kar x) :call) (equal (kadr x) "hpg_run_pop")
                (not (mv-nth 0 (s-call-val-r (kadr x) (kaddr x) fr heap)))
                (integerp fuel) (< (+ 80 (acl2-count x)) fuel))
           (equal (f-ex x fr heap procs fuel)
                  (mv :normal (mv-nth 1 (s-call-val-r (kadr x) (kaddr x) fr heap))
                      (mv-nth 2 (s-call-val-r (kadr x) (kaddr x) fr heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(xr-count-args (:type-prescription acl2-count)) (theory 'minimal-theory))
           :use ((:instance xr-scv-shape (a (xa)))
                 (:instance xr-scv-rp (name (kadr x)) (a (xa)) (ob (x-ob)) (cc (cadr (xa))) (d (kadr (caddr (xa)))))
                 (:instance xr-ex-rp (caller fr) (ob (x-ob)) (cc (cadr (xa))) (d (kadr (caddr (xa))))
                            (key (x-key)) (cm (x-e)) (hpg (hs-hpg (x-e))))))))

(defthm xr-call-rn
  (implies (and (xr-finds) (equal (kar x) :call) (equal (kadr x) "hpg_run_new")
                (not (mv-nth 0 (s-call-val-r (kadr x) (kaddr x) fr heap)))
                (integerp fuel) (< (+ 80 (acl2-count x)) fuel))
           (equal (f-ex x fr heap procs fuel)
                  (mv :normal (mv-nth 1 (s-call-val-r (kadr x) (kaddr x) fr heap))
                      (mv-nth 2 (s-call-val-r (kadr x) (kaddr x) fr heap)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(xr-count-args (:type-prescription acl2-count)) (theory 'minimal-theory))
           :use ((:instance xr-scv-shape (a (xa)))
                 (:instance xr-scv-rn (name (kadr x)) (a (xa)) (ob (x-ob)) (cc (cadr (xa))) (cl (caddr (xa)))
                            (d (kadr (cadddr (xa)))))
                 (:instance xr-ex-rn (caller fr) (ob (x-ob)) (cc (cadr (xa))) (cl (caddr (xa))) (d (kadr (cadddr (xa))))
                            (key (x-key)) (cm (x-e)) (hpg (hs-hpg (x-e))))))))

(defthm xr-scv-other
  (implies (and (not (equal name "hpg_run_pop")) (not (equal name "hpg_run_new")))
           (mv-nth 0 (s-call-val-r name a fr heap)))
  :hints (("Goal" :in-theory (e/d (rfb-shape) (xr-scv-noshape)) :use xr-scv-noshape)))

(defthm xr-call-ok
  (implies (and (xr-finds) (eq (kar x) :call) (not (mv-nth 0 (s-call-val-r (kadr x) (kaddr x) fr heap)))
                (integerp fuel) (< (+ 80 (acl2-count x)) fuel))
           (equal (f-ex x fr heap procs fuel)
                  (mv :normal (mv-nth 1 (s-call-val-r (kadr x) (kaddr x) fr heap))
                      (mv-nth 2 (s-call-val-r (kadr x) (kaddr x) fr heap)))))
  :hints (("Goal" :do-not-induct t :cases ((equal (kadr x) "hpg_run_pop") (equal (kadr x) "hpg_run_new"))
           :in-theory (disable f-ex s-call-val-r xr-call-rp xr-call-rn)
           :use (xr-call-rp xr-call-rn (:instance xr-scv-other (name (kadr x)) (a (kaddr x)))))))

(defmacro xrw (k) `(mv-nth ,k (p-sorc-r-witness procs 80)))

(defthm p-sorc-r-holds
  (implies (xr-finds) (p-sorc-r procs 80))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(p-sorc-r) (theory 'minimal-theory))
           :use ((:instance xr-call-ok (x (xrw 0)) (fr (xrw 1)) (heap (xrw 2)) (fuel (xrw 3)))))))

; ---- the theorem: no hypothesis on the procedures past xr-finds

(defthm hpg-run-from-batch-fortran-correct-x
  (implies (and (xr-finds)
                (hpgp hpg) (hpg-rn-ok hpg) (natp c) (int64p c) (natp l) (<= l *hb40*)
                (equal (cdr (lkp ob caller)) (list* :obj :inout key))
                (consp (cdr (lkp d caller))) (equal (cadr (lkp d caller)) :int64)
                (dr-heap-at heap key comps hpg)
                (integerp fuel) (< (+ 91 (acl2-count *rfb-body*)) fuel))
           (equal (f-invoke *rfb-proc* (list (list :var ob) (g-lit c) (g-lit l) (list :var d)) caller heap procs fuel)
                  (mv nil (put d (cons :int64 (mv-nth 0 (hpg-run-from-batch c l hpg))) caller)
                      (put key (hs-rep comps (mv-nth 1 (hpg-run-from-batch c l hpg))) heap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable f-invoke hpg-run-from-batch hpgp hpg-rn-ok hs-rep dr-heap-at p-sorc-r-holds
                               hpg-run-from-batch-fortran-correct)
           :use (p-sorc-r-holds (:instance hpg-run-from-batch-fortran-correct (b 80))))))
