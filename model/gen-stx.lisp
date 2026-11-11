; gen-stx: the heap-aware fuel-free meaning of gen-st's output, the ground
; for the general stobj theorem (GEN.md "What remains" 4 (a)). sv is fv
; plus the stobj reads (:comp, :size, :elem, through fsem's comp-of on the
; frame and heap); sv-is-f-ev ties it to f-ev at large fuel once, so the
; per-case lemmas against a-sx/a-st reason without fuel, as layer 2's do
; through fv. Calls (:fcall) are not taken yet.

(in-package "ACL2")

(include-book "gen-cf")

; the expressions sv takes: cf-expr's and the stobj reads
(defun cs-expr (e)
  (declare (xargs :guard t))
  (case (kar e)
    ((:int :true :false :huge :var :comp :size) t)
    ((:neg :not) (cs-expr (kadr e)))
    ((:add :sub :mul :eq :lt :le :ge :max) (and (cs-expr (kadr e)) (cs-expr (kaddr e))))
    (:elem (cs-expr (kadddr e)))
    (otherwise nil)))

(defun sv (e fr heap)
  (declare (xargs :guard t :measure (acl2-count e)))
  (case (kar e)
    (:int (if (int-lit-p (kadr e)) (mv nil (kadr e)) (mv :syntax nil)))
    (:true (mv nil t))
    (:false (mv nil nil))
    (:huge (mv nil *int64-max*))
    (:var (let ((b (cdr (lkp (kadr e) fr))))
            (cond ((not (and (consp b) (member-eq (car b) '(:int64 :logical)))) (mv :type nil))
                  ((eq (cdr b) :undef) (mv :undefined nil))
                  (t (mv nil (cdr b))))))
    (:comp (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
             (cond (err (mv err nil)) ((int64p v) (mv nil v)) (t (mv :type nil)))))
    (:size (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
             (cond (err (mv err nil)) ((farrayp v) (mv nil (len (cdr v)))) (t (mv :type nil)))))
    (:elem (mv-let (err i) (sv (kadddr e) fr heap)
             (if err (mv err nil)
               (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
                 (if err (mv err nil) (read-elem v i))))))
    (:neg (mv-let (err a) (sv (kadr e) fr heap) (if err (mv err nil) (arith :sub 0 a))))
    (:not (mv-let (err a) (sv (kadr e) fr heap)
            (cond (err (mv err nil)) ((booleanp a) (mv nil (not a))) (t (mv :type nil)))))
    ((:add :sub :mul :eq :lt :le :ge :max)
     (mv-let (err a) (sv (kadr e) fr heap)
       (if err (mv err nil)
         (mv-let (err b) (sv (kaddr e) fr heap)
           (if err (mv err nil) (binop (kar e) a b))))))
    (otherwise (mv :syntax nil))))

(in-theory (disable sv))

(defun sv-ind (e k)
  (declare (xargs :measure (nfix k)))
  (if (zp k) e (list (sv-ind (kadr e) (1- k)) (sv-ind (kaddr e) (1- k)) (sv-ind (kadddr e) (1- k)))))

(defthm sv-is-f-ev
  (implies (and (cs-expr e) (< (acl2-count e) k) (integerp k))
           (equal (f-ev e fr heap procs k) (sv e fr heap)))
  :hints (("Goal" :induct (sv-ind e k) :in-theory (enable sv) :expand ((f-ev e fr heap procs k)))))

; a stobj-free expression: sv is fv
(defthm sv-is-fv
  (implies (cf-expr e) (equal (sv e fr heap) (fv e fr)))
  :hints (("Goal" :induct (sv e fr heap) :in-theory (enable sv fv))))

; ---- statements: assignments to a variable, a component or an element,
; if, select, return, cycle, exit; sx is fx on the heap, (mv status frame heap)

(mutual-recursion
 (defun cs-stmt (s)
   (declare (xargs :guard t :measure (acl2-count s)))
   (case (kar s)
     (:assign (and (cs-expr (kaddr s))
                   (case (kar (kadr s))
                     ((:var :comp) t)
                     (:elem (cs-expr (kadddr (kadr s))))
                     (otherwise nil))))
     (:if (and (cs-expr (kadr s)) (cs-stmts (kaddr s)) (cs-stmts (kadddr s))))
     (:select (and (cs-expr (kadr s)) (cs-arms (kaddr s)) (cs-stmts (kadddr s))))
     ((:return :cycle :exit) t)
     (otherwise nil)))
 (defun cs-arms (arms)
   (declare (xargs :guard t :measure (acl2-count arms)))
   (if (atom arms) t (and (cs-stmts (kadr (car arms))) (cs-arms (cdr arms)))))
 (defun cs-stmts (ss)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) t (and (cs-stmt (car ss)) (cs-stmts (cdr ss))))))

(mutual-recursion
 (defun sx (x frame heap)
   (declare (xargs :guard t :measure (acl2-count x)))
   (case (kar x)
     (:assign
      (mv-let (err v) (sv (kaddr x) frame heap)
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
                                  (t (mv-let (err i) (sv (kadddr d) frame heap)
                                       (cond (err (mv (errst err) frame heap))
                                             ((not (and (farrayp (cdr p)) (integerp i))) (mv (errst :type) frame heap))
                                             ((not (and (<= 0 i) (< i (len (cddr p))))) (mv (errst :bounds) frame heap))
                                             (t (mv :normal frame
                                                    (put key (put (kaddr d) (cons :array (update-nth i v (cddr p))) comps)
                                                         heap))))))))))))
              (otherwise (mv (errst :syntax) frame heap)))))))
     (:if (mv-let (err c) (sv (kadr x) frame heap)
            (cond (err (mv (errst err) frame heap))
                  ((not (booleanp c)) (mv (errst :type) frame heap))
                  (c (sx-list (kaddr x) frame heap))
                  (t (sx-list (kadddr x) frame heap)))))
     (:select (mv-let (err k) (sv (kadr x) frame heap)
                (cond (err (mv (errst err) frame heap))
                      ((not (integerp k)) (mv (errst :type) frame heap))
                      (t (let ((arm (lkp k (kaddr x))))
                           (sx-list (if arm (kadr arm) (kadddr x)) frame heap))))))
     ((:cycle :exit :return) (mv (kar x) frame heap))
     (otherwise (mv (errst :syntax) frame heap))))
 (defun sx-list (ss frame heap)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) (mv :normal frame heap)
     (mv-let (st fr2 h2) (sx (car ss) frame heap)
       (if (eq st :normal) (sx-list (cdr ss) fr2 h2) (mv st fr2 h2))))))

(in-theory (disable sx sx-list))

(defun sx-ind (flag s fr heap k)
  (declare (xargs :measure (acl2-count s) :verify-guards nil))
  (if (or (zp k) (atom s)) (list fr heap k)
    (if (eq flag :stmt)
        (mv-let (err v) (sv (kadr s) fr heap)
          (declare (ignore err))
          (list (sx-ind :list (kaddr s) fr heap (1- k))
                (sx-ind :list (kadddr s) fr heap (1- k))
                (sx-ind :list (kadr (lkp v (kaddr s))) fr heap (1- k))))
      (mv-let (st fr2 h2) (sx (car s) fr heap)
        (declare (ignore st))
        (list (sx-ind :stmt (car s) fr heap (1- k))
              (sx-ind :list (cdr s) fr2 h2 (1- k)))))))

(defthm f-ex-assign-obj
  (implies (and (posp k) (eq (kar s) :assign) (member-eq (kar (kadr s)) '(:comp :elem)))
           (equal (f-ex s fr heap procs k)
                  (mv-let (err v) (f-ev (kaddr s) fr heap procs (1- k))
                    (if err (mv (errst err) fr heap)
                      (let ((d (kadr s)))
                        (mv-let (err key intent) (obj-of (kadr d) fr)
                          (cond (err (mv (errst err) fr heap))
                                ((not (eq intent :inout)) (mv (errst :intent) fr heap))
                                ((not (int64p v)) (mv (errst :type) fr heap))
                                (t (let* ((comps (cdr (lkp key heap))) (p (lkp (kaddr d) comps)))
                                     (cond ((not (consp p)) (mv (errst :type) fr heap))
                                           ((eq (kar d) :comp)
                                            (if (int64p (cdr p))
                                                (mv :normal fr (put key (put (kaddr d) v comps) heap))
                                              (mv (errst :type) fr heap)))
                                           (t (mv-let (err i) (f-ev (kadddr d) fr heap procs (1- k))
                                                (cond (err (mv (errst err) fr heap))
                                                      ((not (and (farrayp (cdr p)) (integerp i))) (mv (errst :type) fr heap))
                                                      ((not (and (<= 0 i) (< i (len (cddr p))))) (mv (errst :bounds) fr heap))
                                                      (t (mv :normal fr
                                                             (put key (put (kaddr d) (cons :array (update-nth i v (cddr p))) comps)
                                                                  heap))))))))))))))))
  :hints (("Goal" :expand ((f-ex s fr heap procs k)))))

(defthm f-ex-jump
  (implies (and (posp k) (member-eq (kar s) '(:cycle :exit :return)))
           (equal (f-ex s fr heap procs k) (mv (kar s) fr heap)))
  :hints (("Goal" :expand ((f-ex s fr heap procs k)))))

(defthm count-kadddr-kadr
  (implies (consp s) (< (acl2-count (kadddr (kadr s))) (acl2-count s)))
  :rule-classes :linear)

(defthm count-lkp-arm-cadr
  (<= (acl2-count (cadr (lkp k arms))) (acl2-count arms))
  :rule-classes :linear)

(defthm cs-arms-lkp
  (implies (cs-arms arms) (cs-stmts (cadr (lkp k arms)))))

(defthm sx-is-f-ex-flag
  (implies (and (integerp k) (< (acl2-count s) k))
           (if (eq flag :stmt)
               (implies (cs-stmt s) (equal (f-ex s fr heap procs k) (sx s fr heap)))
             (implies (cs-stmts s) (equal (f-ex-list s fr heap procs k) (sx-list s fr heap)))))
  :rule-classes nil
  :hints (("Goal" :induct (sx-ind flag s fr heap k) :do-not-induct t
           :in-theory (disable f-ex f-ex-list f-ex-return))
          (and stable-under-simplificationp
               '(:expand ((sx s fr heap) (sx-list s fr heap) (cs-stmt s) (cs-stmts s))))))

(defthm sx-is-f-ex
  (implies (and (cs-stmt s) (integerp k) (< (acl2-count s) k))
           (equal (f-ex s fr heap procs k) (sx s fr heap)))
  :hints (("Goal" :use (:instance sx-is-f-ex-flag (flag :stmt)))))

(defthm sx-list-is-f-ex-list
  (implies (and (cs-stmts ss) (integerp k) (< (acl2-count ss) k))
           (equal (f-ex-list ss fr heap procs k) (sx-list ss fr heap)))
  :hints (("Goal" :use (:instance sx-is-f-ex-flag (flag :list) (s ss)))))

; ---- stobj-free statements: sx is fx, the heap unchanged

(defthm cf-expr-cs (implies (cf-expr e) (cs-expr e)))

(defun cfcs-ind (flag x)
  (declare (xargs :measure (acl2-count x)))
  (cond ((atom x) nil)
        ((eq flag :stmt) (list (cfcs-ind :list (kaddr x)) (cfcs-ind :list (kadddr x)) (cfcs-ind :arms (kaddr x))))
        ((eq flag :arms) (list (cfcs-ind :list (kadr (car x))) (cfcs-ind :arms (cdr x))))
        (t (list (cfcs-ind :stmt (car x)) (cfcs-ind :list (cdr x))))))

(defthm cf-cs-flag
  (case flag
    (:stmt (implies (cf-stmt x) (cs-stmt x)))
    (:arms (implies (cf-arms x) (cs-arms x)))
    (otherwise (implies (cf-stmts x) (cs-stmts x))))
  :rule-classes nil
  :hints (("Goal" :induct (cfcs-ind flag x)
           :expand ((cf-stmt x) (cs-stmt x) (cf-arms x) (cs-arms x) (cf-stmts x) (cs-stmts x)))))

(defthm cf-stmts-cs
  (implies (cf-stmts ss) (cs-stmts ss))
  :hints (("Goal" :use (:instance cf-cs-flag (flag :list) (x ss)))))

(defthm sx-list-is-fx-list
  (implies (cf-stmts ss) (equal (sx-list ss fr heap) (+h (fx-list ss fr) heap)))
  :hints (("Goal" :in-theory (disable sx-list-is-f-ex-list fx-list-is-f-ex-list)
           :use ((:instance sx-list-is-f-ex-list (k (1+ (acl2-count ss))) (procs nil))
                 (:instance fx-list-is-f-ex-list (k (1+ (acl2-count ss))) (procs nil))))))
