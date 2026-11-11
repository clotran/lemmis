; gen-names: what g-expr's statements write and its code reads. Every name
; its statements assign is a temporary it made, new against the names in
; scope and every temporary made before; its code reads only names in scope
; and its own temporaries. gen-proof.lisp uses these to keep a value, once
; computed, unchanged by the statements that follow.

(in-package "ACL2")

(include-book "gen")
(include-book "gen-cf")

(set-irrelevant-formals-ok t)

(defun evs-names (cs)
  (declare (xargs :guard t))
  (if (atom cs) nil (append (ev-names (car cs)) (evs-names (cdr cs)))))

(defthm ev-names-list-is-evs-names (equal (ev-names-list cs) (evs-names cs)))

(defun fr-after (ss fr) (mv-let (st fr2) (fx-list ss fr) (declare (ignore st)) fr2))
(defun a-vals (xs env defs n) (mv-let (e vs) (a-ev-list xs env defs n) (declare (ignore e)) vs))

; g-expr's recursion (flag :expr, :args, :binds), carrying what the semantic
; proof needs too: a-ev's env and fuel, and the frame each part starts from
(defun g-ind (flag x vars em cnt locs sigs fnames env defs n fr)
  (declare (xargs :measure (acl2-count x) :verify-guards nil
                  :hints (("Goal" :in-theory (disable g-big)))))
  (cond
   ((eq flag :args)
    (if (atom x) nil
      (mv-let (e s c ty cnt1 locs1) (g-expr (car x) em cnt locs sigs fnames)
        (declare (ignore e c ty))
        (list (g-ind :expr (car x) nil em cnt locs sigs fnames env defs (1- n) fr)
              (g-ind :args (cdr x) nil em cnt1 locs1 sigs fnames env defs (1- n)
                     (fr-after s fr))))))
   ((eq flag :binds)
    (cond ((or (atom vars) (atom x)) nil)
          ((eq (car vars) (car x))
           (g-ind :binds (cdr x) (cdr vars) em cnt locs sigs fnames env defs (1- n) fr))
          (t (mv-let (e s c ty cnt1 locs1) (g-expr (car x) em cnt locs sigs fnames)
               (declare (ignore e))
               (mv-let (e tmp cnt2 locs2) (g-fresh (car vars) ty cnt1 locs1 (append fnames (em-names em)))
                 (declare (ignore e))
                 (list (g-ind :expr (car x) nil em cnt locs sigs fnames env defs (1- n) fr)
                       (g-ind :binds (cdr x) (cdr vars) em cnt2 locs2 sigs fnames env defs (1- n)
                              (fr-after (append s (list (list :assign (list :var tmp) c))) fr))))))))
   ((or (symbolp x) (atom x) (eq (car x) 'quote)) nil)
   ((member-eq (car x) '(if implies))
    (let ((imp (eq (car x) 'implies)))
      (mv-let (e sc cc tc cnt1 locs1) (g-expr (kadr x) em cnt locs sigs fnames)
        (declare (ignore e cc tc))
        (mv-let (e sa ca ta cnt2 locs2) (g-expr (kaddr x) em cnt1 locs1 sigs fnames)
          (declare (ignore e sa ca ta))
          (let ((fr1 (fr-after sc fr)))
            (list (g-ind :expr (kadr x) nil em cnt locs sigs fnames env defs (if imp (- n 2) (1- n)) fr)
                  (g-ind :expr (kaddr x) nil em cnt1 locs1 sigs fnames env defs (if imp (- n 3) (1- n)) fr1)
                  (g-ind :expr (kadddr x) nil em cnt2 locs2 sigs fnames env defs (1- n) fr1)))))))
   ((and (eq (car x) '<) (true-listp x) (= (len x) 3) (or (g-big (kadr x)) (g-big (kaddr x))))
    (if (g-big (kadr x))
        (g-ind :expr (kaddr x) nil em cnt locs sigs fnames env defs (- n 3) fr)
      (g-ind :expr (kadr x) nil em cnt locs sigs fnames env defs (- n 2) fr)))
   ((consp (car x))
    (mv-let (e s binds cnt1 locs1) (g-binds (kadr (car x)) (cdr x) em cnt locs sigs fnames)
      (declare (ignore e))
      (list (g-ind :binds (cdr x) (kadr (car x)) em cnt locs sigs fnames env defs (1- n) fr)
            (g-ind :expr (kaddr (car x)) nil (append binds em) cnt1 locs1 sigs fnames
                   (pairlis$ (true-list-fix (kadr (car x))) (a-vals (cdr x) env defs (1- n)))
                   defs (1- n) (fr-after s fr)))))
   ((eq (car x) 'the-check)
    (g-ind :expr (kadddr x) nil em cnt locs sigs fnames env defs (- n 4) fr))
   (t (g-ind :args (cdr x) nil em cnt locs sigs fnames env defs (1- n) fr))))

; ---- list facts

(defthm subsetp-cons-r (implies (subsetp-equal a b) (subsetp-equal a (cons x b))))
(defthm subsetp-refl (subsetp-equal x x))
(defthm subsetp-trans
  (implies (and (subsetp-equal a b) (subsetp-equal b c)) (subsetp-equal a c))
  :rule-classes nil)
(defthm subsetp-app-l (equal (subsetp-equal (append a b) c) (and (subsetp-equal a c) (subsetp-equal b c))))
(defthm subsetp-app-r1 (implies (subsetp-equal a b) (subsetp-equal a (append b c))))
(defthm subsetp-app-r2 (implies (subsetp-equal a c) (subsetp-equal a (append b c))))
(defthm member-tlf (iff (member-equal x (true-list-fix b)) (member-equal x b)))
(defthm subsetp-tlf (iff (subsetp-equal a (true-list-fix b)) (subsetp-equal a b)))
(defthm strip-cars-tlf-member (iff (member-equal x (strip-cars (true-list-fix b))) (member-equal x (strip-cars b))))
(defthm member-strip-cars (implies (member-equal x b) (member-equal (car x) (strip-cars b))))
(defthm member-strip-cars-cons (implies (member-equal (cons a d) b) (member-equal a (strip-cars b))))
(defthm subsetp-strip-cars
  (implies (subsetp-equal a b) (subsetp-equal (strip-cars a) (strip-cars b))))
(defthm not-member-strip-cars-sub
  (implies (and (subsetp-equal a b) (not (member-equal x (strip-cars b))))
           (not (member-equal x (strip-cars a)))))
(defthm strip-cars-tlf (equal (strip-cars (true-list-fix l)) (strip-cars l)))
(defthm subsetp-strip-cars-trans
  (implies (and (subsetp-equal a (strip-cars b)) (subsetp-equal b c)) (subsetp-equal a (strip-cars c)))
  :hints (("Goal" :use (:instance subsetp-trans (b (strip-cars b)) (c (strip-cars c))))))
(defthm subsetp-app-strip-cars-trans
  (implies (and (subsetp-equal a (append e (strip-cars b))) (subsetp-equal b c))
           (subsetp-equal a (append e (strip-cars c))))
  :hints (("Goal" :use (:instance subsetp-trans (b (append e (strip-cars b))) (c (append e (strip-cars c)))))))
(defthm intersectp-app-l
  (equal (intersectp-equal (append a b) c) (or (intersectp-equal a c) (intersectp-equal b c))))
(defthm intersectp-app-r
  (equal (intersectp-equal a (append b c)) (or (intersectp-equal a b) (intersectp-equal a c))))
(defthm intersectp-cons-r
  (iff (intersectp-equal a (cons x c)) (or (member-equal x a) (intersectp-equal a c))))
(defthm intersectp-subset-r
  (implies (and (not (intersectp-equal a c)) (subsetp-equal b c)) (not (intersectp-equal a b))))
(defthm em-names-app (equal (em-names (append a b)) (append (em-names a) (em-names b))))

; ---- the facts, per flag

;; g-expr's case, as its cond picks it
(defun gkind (x)
  (cond ((symbolp x) :sym) ((atom x) :atom) ((eq (car x) 'quote) :quote)
        ((member-eq (car x) '(if implies)) :if)
        ((and (eq (car x) '<) (true-listp x) (= (len x) 3) (or (g-big (kadr x)) (g-big (kaddr x)))) :big)
        ((consp (car x)) :lambda)
        ((eq (car x) 'the-check) :the-check)
        (t :call)))

(defun gs-ok (flag x vars em cnt locs sigs fnames)
  (declare (xargs :verify-guards nil))
  (let ((old (append fnames (em-names em) (strip-cars locs))))
    (case flag
      (:args (mv-let (e s cs ts cnt2 locs2) (g-args x em cnt locs sigs fnames)
               (declare (ignore ts cnt2))
               (implies (not e)
                        (and (subsetp-equal locs locs2)
                             (subsetp-equal (asg :list s) (strip-cars locs2))
                             (not (intersectp-equal (asg :list s) old))
                             (subsetp-equal (evs-names cs) (append (em-names em) (strip-cars locs2)))))))
      (:binds (mv-let (e s binds cnt2 locs2) (g-binds vars x em cnt locs sigs fnames)
                (declare (ignore cnt2))
                (implies (not e)
                         (and (subsetp-equal locs locs2)
                              (subsetp-equal (asg :list s) (strip-cars locs2))
                              (not (intersectp-equal (asg :list s) old))
                              (subsetp-equal (em-names binds) (strip-cars locs2))))))
      (otherwise (mv-let (e s c ty cnt2 locs2) (g-expr x em cnt locs sigs fnames)
                   (declare (ignore ty cnt2))
                   (implies (not e)
                            (and (subsetp-equal locs locs2)
                                 (subsetp-equal (asg :list s) (strip-cars locs2))
                                 (not (intersectp-equal (asg :list s) old))
                                 (subsetp-equal (ev-names c) (append (em-names em) (strip-cars locs2))))))))))

(defmacro g-cnt (x em cnt locs) `(mv-nth 4 (g-expr ,x ,em ,cnt ,locs sigs fnames)))
(defmacro g-locs (x em cnt locs) `(mv-nth 5 (g-expr ,x ,em ,cnt ,locs sigs fnames)))

(defthm asg-one-assign (equal (asg :list (list (list :assign (list :var tmp) c))) (list tmp))
  :hints (("Goal" :expand ((asg :list (list (list :assign (list :var tmp) c)))))))

(defthm asg-one-if (equal (asg :list (list (list :if c a b))) (append (asg :list a) (asg :list b)))
  :hints (("Goal" :expand ((asg :list (list (list :if c a b)))))))

(defthm em-names-lkp
  (implies (and (consp (lkp x em)) (consp (cdr (lkp x em))))
           (member-equal (cadr (lkp x em)) (em-names em))))

(defthm gs-base
  (implies (member-eq (gkind x) '(:sym :atom :quote)) (gs-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((g-expr x em cnt locs sigs fnames)))))

(defthm gs-if
  (implies (and (equal (gkind x) :if)
                (gs-ok :expr (kadr x) nil em cnt locs sigs fnames)
                (gs-ok :expr (kaddr x) nil em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs) sigs fnames)
                (gs-ok :expr (kadddr x) nil em
                       (g-cnt (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs))
                       (g-locs (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs))
                       sigs fnames))
           (gs-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-expr x em cnt locs sigs fnames))
           :in-theory (disable g-expr g-args g-binds)
           :use ((:instance subsetp-trans (a locs) (b (g-locs (kadr x) em cnt locs))
                            (c (g-locs (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs))))
                 (:instance subsetp-trans (a locs)
                            (b (g-locs (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs)))
                            (c (g-locs (kadddr x) em
                                       (g-cnt (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs))
                                       (g-locs (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs)))))
                 (:instance subsetp-trans (a (g-locs (kadr x) em cnt locs))
                            (b (g-locs (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs)))
                            (c (g-locs (kadddr x) em
                                       (g-cnt (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs))
                                       (g-locs (kaddr x) em (g-cnt (kadr x) em cnt locs) (g-locs (kadr x) em cnt locs)))))))))


(defthm ev-names-g-unop
  (implies (subsetp-equal (ev-names c) tgt) (subsetp-equal (ev-names (mv-nth 1 (g-unop op c ty))) tgt)))

(defthm ev-names-g-binop
  (implies (and (subsetp-equal (ev-names a) tgt) (subsetp-equal (ev-names b) tgt))
           (subsetp-equal (ev-names (mv-nth 1 (g-binop op a ta b tb))) tgt)))

(defthm evs-names-parts
  (implies (subsetp-equal (evs-names cs) tgt)
           (and (subsetp-equal (ev-names (car cs)) tgt) (subsetp-equal (ev-names (cadr cs)) tgt)))
  :hints (("Goal" :expand ((evs-names cs) (evs-names (cdr cs))))))

(defthm gs-big
  (implies (and (equal (gkind x) :big)
                (gs-ok :expr (if (g-big (kadr x)) (kaddr x) (kadr x)) nil em cnt locs sigs fnames))
           (gs-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-expr x em cnt locs sigs fnames))
           :in-theory (disable g-expr g-args g-binds))))

(defthm gs-the-check
  (implies (and (consp x) (eq (car x) 'the-check) (gs-ok :expr (kadddr x) nil em cnt locs sigs fnames))
           (gs-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-expr x em cnt locs sigs fnames))
           :in-theory (disable g-expr g-args g-binds))))

(defthm gs-call
  (implies (and (equal (gkind x) :call) (gs-ok :args (cdr x) nil em cnt locs sigs fnames))
           (gs-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-expr x em cnt locs sigs fnames))
           :in-theory (disable g-expr g-args g-binds g-unop g-binop))))

(defmacro gb-l (k) `(mv-nth ,k (g-binds (kadr (car x)) (cdr x) em cnt locs sigs fnames)))

(defthm member-subsetp
  (implies (and (member-equal x b) (subsetp-equal b c)) (member-equal x c)))

(defthm subsetp-app-drop
  ; a subset of (append b e c), b within c, is a subset of (append e c)
  (implies (and (subsetp-equal a (append b e c)) (subsetp-equal b c)) (subsetp-equal a (append e c)))
  :hints (("Goal" :induct (len a))))

(defthm gs-lambda
  (implies (and (equal (gkind x) :lambda)
                (gs-ok :binds (cdr x) (kadr (car x)) em cnt locs sigs fnames)
                (gs-ok :expr (kaddr (car x)) nil (append (gb-l 2) em) (gb-l 3) (gb-l 4) sigs fnames))
           (gs-ok :expr x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-expr x em cnt locs sigs fnames))
           :in-theory (disable g-expr g-args g-binds)
           :use ((:instance subsetp-trans (a locs) (b (gb-l 4))
                            (c (g-locs (kaddr (car x)) (append (gb-l 2) em) (gb-l 3) (gb-l 4))))
                 (:instance subsetp-trans (a (em-names (gb-l 2))) (b (strip-cars (gb-l 4)))
                            (c (strip-cars (g-locs (kaddr (car x)) (append (gb-l 2) em) (gb-l 3) (gb-l 4)))))))))

(defthm gs-args-nil
  (implies (atom x) (gs-ok :args x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((g-args x em cnt locs sigs fnames)))))

(defthm gs-args-cons
  (implies (and (consp x)
                (gs-ok :expr (car x) nil em cnt locs sigs fnames)
                (gs-ok :args (cdr x) nil em (g-cnt (car x) em cnt locs) (g-locs (car x) em cnt locs) sigs fnames))
           (gs-ok :args x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-args x em cnt locs sigs fnames) (evs-names (cons a b)))
           :in-theory (disable g-expr g-args g-binds)
           :use ((:instance subsetp-trans (a locs) (b (g-locs (car x) em cnt locs))
                            (c (mv-nth 5 (g-args (cdr x) em (g-cnt (car x) em cnt locs) (g-locs (car x) em cnt locs)
                                                 sigs fnames))))))))

(defthm gs-binds-nil
  (implies (or (atom vars) (atom x)) (gs-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :expand ((g-binds vars x em cnt locs sigs fnames)))))

(defthm gs-binds-self
  (implies (and (consp vars) (consp x) (eq (car vars) (car x))
                (gs-ok :binds (cdr x) (cdr vars) em cnt locs sigs fnames))
           (gs-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-binds vars x em cnt locs sigs fnames))
           :in-theory (disable g-expr g-args g-binds))))

(defmacro gf-l (k)
  `(mv-nth ,k (g-fresh (car vars) (mv-nth 3 (g-expr (car x) em cnt locs sigs fnames))
                       (g-cnt (car x) em cnt locs) (g-locs (car x) em cnt locs) (append fnames (em-names em)))))

(defthm gs-binds-cons
  (implies (and (consp vars) (consp x) (not (eq (car vars) (car x)))
                (gs-ok :expr (car x) nil em cnt locs sigs fnames)
                (gs-ok :binds (cdr x) (cdr vars) em (gf-l 2) (gf-l 3) sigs fnames))
           (gs-ok :binds x vars em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-binds vars x em cnt locs sigs fnames))
           :in-theory (disable g-expr g-args g-binds g-tmp)
           :use ((:instance subsetp-trans (a locs) (b (g-locs (car x) em cnt locs)) (c (gf-l 3)))
                 (:instance subsetp-trans (a locs) (b (gf-l 3))
                            (c (mv-nth 4 (g-binds (cdr vars) (cdr x) em (gf-l 2) (gf-l 3) sigs fnames))))
                 (:instance subsetp-trans (a (g-locs (car x) em cnt locs)) (b (gf-l 3))
                            (c (mv-nth 4 (g-binds (cdr vars) (cdr x) em (gf-l 2) (gf-l 3) sigs fnames))))))))
(defthm gkind-call
  (implies (and (not (equal (gkind x) :sym)) (not (equal (gkind x) :atom)) (not (equal (gkind x) :quote))
                (not (equal (gkind x) :if)) (not (equal (gkind x) :big)) (not (equal (gkind x) :lambda))
                (not (equal (gkind x) :the-check)))
           (equal (gkind x) :call)))

(defthm gs-ok-thm
  (if (eq flag :args) (gs-ok :args x vars em cnt locs sigs fnames)
    (if (eq flag :binds) (gs-ok :binds x vars em cnt locs sigs fnames)
      (gs-ok :expr x vars em cnt locs sigs fnames)))
  :rule-classes nil
  :hints (("Goal" :induct (g-ind flag x vars em cnt locs sigs fnames env defs n fr) :do-not-induct t
           :in-theory (disable gs-ok g-expr g-args g-binds g-big kadr kaddr kadddr))))

; ---- the facts as rewrite rules

(defmacro g-names-facts (s f1 f2 locs locs2 rd)
  `(and (subsetp-equal ,locs ,locs2)
        (subsetp-equal (asg :list ,s) (strip-cars ,locs2))
        (not (intersectp-equal (asg :list ,s) ,f1))
        (not (intersectp-equal (asg :list ,s) ,f2))
        (not (intersectp-equal (asg :list ,s) (strip-cars ,locs)))
        ,rd))

(defthm g-expr-names
  (implies (not (mv-nth 0 (g-expr x em cnt locs sigs fnames)))
           (g-names-facts (mv-nth 1 (g-expr x em cnt locs sigs fnames)) fnames (em-names em) locs
                          (mv-nth 5 (g-expr x em cnt locs sigs fnames))
                          (subsetp-equal (ev-names (mv-nth 2 (g-expr x em cnt locs sigs fnames)))
                                         (append (em-names em) (strip-cars (mv-nth 5 (g-expr x em cnt locs sigs fnames)))))))
  :hints (("Goal" :use (:instance gs-ok-thm (flag :expr) (vars nil)) )))

(defthm g-args-names
  (implies (not (mv-nth 0 (g-args x em cnt locs sigs fnames)))
           (g-names-facts (mv-nth 1 (g-args x em cnt locs sigs fnames)) fnames (em-names em) locs
                          (mv-nth 5 (g-args x em cnt locs sigs fnames))
                          (subsetp-equal (evs-names (mv-nth 2 (g-args x em cnt locs sigs fnames)))
                                         (append (em-names em) (strip-cars (mv-nth 5 (g-args x em cnt locs sigs fnames)))))))
  :hints (("Goal" :use (:instance gs-ok-thm (flag :args) (vars nil)) )))

(defthm g-binds-names
  (implies (not (mv-nth 0 (g-binds vars x em cnt locs sigs fnames)))
           (g-names-facts (mv-nth 1 (g-binds vars x em cnt locs sigs fnames)) fnames (em-names em) locs
                          (mv-nth 4 (g-binds vars x em cnt locs sigs fnames))
                          (subsetp-equal (em-names (mv-nth 2 (g-binds vars x em cnt locs sigs fnames)))
                                         (strip-cars (mv-nth 4 (g-binds vars x em cnt locs sigs fnames))))))
  :hints (("Goal" :use (:instance gs-ok-thm (flag :binds)) )))
