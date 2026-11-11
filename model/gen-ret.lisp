; gen-ret: the body in return position. g-ret's statements, run by fx, end
; in :return with "r" holding what a-ev says the body means (gr-sem); a
; case chain's SELECT picks the arm the if chain takes (gsel-sem), every arm
; testing the same variable (g-chain's invariant, chain-on here).

(in-package "ACL2")

(include-book "gen-proof2")

(set-irrelevant-formals-ok t)

(defthm ge-sem-all
  (ge-sem x em cnt locs sigs fnames env defs n fr cs)
  :rule-classes nil
  :hints (("Goal" :use (:instance ge-sem-thm (flag :expr) (vars nil)))))

(defmacro rty () '(kadr (cdr (lkp self sigs))))

(defun ret-ok (fr2 rt v) (and (equal (cdr (lkp "r" fr2)) (cons rt v)) (scalar-ok rt v)))

; ---- g-ret's recursion, carrying a-ev's env and fuel and the frame

(defun gr-ind (flag x k em cnt locs self sigs fnames env defs cs n fr)
  (declare (xargs :measure (if (eq flag :sel) (1+ (* 2 (acl2-count x))) (* 2 (acl2-count x)))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable g-case-key int-lit-p g-chain acl2-count)))))
  (if (eq flag :sel)
      (if (zp k) (gr-ind :ret x 0 em cnt locs self sigs fnames env defs cs n fr)
        (if (not (and (consp x) (true-listp x) (= (len x) 4))) nil
          (mv-let (e sa cnt1 locs1) (g-ret (caddr x) em cnt locs self sigs fnames)
            (declare (ignore e sa))
            (list (gr-ind :ret (caddr x) 0 em cnt locs self sigs fnames env defs cs (1- n) fr)
                  (gr-ind :sel (cadddr x) (1- k) em cnt1 locs1 self sigs fnames env defs cs (1- n) fr)))))
    (cond
     ((and (consp x) (<= 3 (g-chain x nil nil)))
      (mv-let (e sa cnt1 locs1) (g-ret (caddr x) em cnt locs self sigs fnames)
        (declare (ignore e sa))
        (list (gr-ind :ret (caddr x) 0 em cnt locs self sigs fnames env defs cs (1- n) fr)
              (gr-ind :sel (cadddr x) (1- (g-chain x nil nil)) em cnt1 locs1 self sigs fnames env defs cs (1- n) fr))))
     ((and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4))
      (mv-let (e sc cc tc cnt1 locs1) (g-expr (cadr x) em cnt locs sigs fnames)
        (declare (ignore e cc tc))
        (mv-let (e sa cnt2 locs2) (g-ret (caddr x) em cnt1 locs1 self sigs fnames)
          (declare (ignore e sa))
          (list (gr-ind :ret (caddr x) 0 em cnt1 locs1 self sigs fnames env defs cs (1- n) (fr-after sc fr))
                (gr-ind :ret (cadddr x) 0 em cnt2 locs2 self sigs fnames env defs cs (1- n) (fr-after sc fr))))))
     (t nil))))

; ---- the temporaries only grow

(defmacro gt1 (k) `(mv-nth ,k (g-expr (car xs) em cnt locs sigs fnames)))
(defmacro gtf (k) `(mv-nth ,k (g-fresh (car vars) (gt1 3) (gt1 4) (gt1 5) (append fnames (em-names em)))))

(defun gt-ok (vars xs em cnt locs sigs fnames)
  (declare (xargs :verify-guards nil))
  (mv-let (e s as cnt2 locs2) (g-tail vars xs em cnt locs sigs fnames)
    (declare (ignore s as cnt2))
    (implies (not e) (subsetp-equal locs locs2))))

(in-theory (disable gt-ok))

(defthm g-tail-step
  (implies (and (consp vars) (consp xs) (gt-ok (cdr vars) (cdr xs) em (gtf 2) (gtf 3) sigs fnames))
           (gt-ok vars xs em cnt locs sigs fnames))
  :hints (("Goal" :do-not-induct t :expand ((g-tail vars xs em cnt locs sigs fnames))
           :in-theory (e/d (gt-ok) (g-expr g-tail g-tmp))
           :use ((:instance subsetp-trans (a locs) (b (gt1 5)) (c (gtf 3)))
                 (:instance subsetp-trans (a locs) (b (gtf 3))
                            (c (mv-nth 4 (g-tail (cdr vars) (cdr xs) em (gtf 2) (gtf 3) sigs fnames))))))))

(defthm g-tail-err
  (implies (and (consp vars) (consp xs) (or (gt1 0) (not (equal (gt1 3) :int64)) (gtf 0)))
           (gt-ok vars xs em cnt locs sigs fnames))
  :hints (("Goal" :in-theory (e/d (gt-ok) (g-expr g-fresh)) :expand ((g-tail vars xs em cnt locs sigs fnames)))))

(defthm g-tail-base
  (implies (or (atom vars) (atom xs)) (gt-ok vars xs em cnt locs sigs fnames))
  :hints (("Goal" :in-theory (enable gt-ok) :expand ((g-tail vars xs em cnt locs sigs fnames)))))

(defthm g-tail-locs
  (gt-ok vars xs em cnt locs sigs fnames)
  :rule-classes nil
  :hints (("Goal" :induct (g-tail vars xs em cnt locs sigs fnames) :in-theory (disable gt-ok g-expr g-fresh (:definition g-tail)))))

(defthm g-tail-locs-sub
  (implies (not (car (g-tail vars xs em cnt locs sigs fnames)))
           (subsetp-equal locs (mv-nth 4 (g-tail vars xs em cnt locs sigs fnames))))
  :hints (("Goal" :use g-tail-locs :in-theory (e/d (gt-ok) (g-tail)))))

(defun grl-ok (flag x k em cnt locs self sigs fnames)
  (declare (xargs :verify-guards nil))
  (if (eq flag :sel)
      (mv-let (e arms dflt cnt2 locs2) (g-select x k em cnt locs self sigs fnames)
        (declare (ignore arms dflt cnt2))
        (implies (not e) (subsetp-equal locs locs2)))
    (mv-let (e s cnt2 locs2) (g-ret x em cnt locs self sigs fnames)
      (declare (ignore s cnt2))
      (implies (not e) (subsetp-equal locs locs2)))))

(in-theory (disable grl-ok))

(defmacro gr1 (k) `(mv-nth ,k (g-ret (caddr x) em cnt locs self sigs fnames)))
(defmacro gc1 (k) `(mv-nth ,k (g-expr (cadr x) em cnt locs sigs fnames)))
(defmacro gi1 (k) `(mv-nth ,k (g-ret (caddr x) em (gc1 4) (gc1 5) self sigs fnames)))
(defmacro gsel (k) `(mv-nth ,k (g-select (cadddr x) (1- (g-chain x nil nil)) em (gr1 2) (gr1 3) self sigs fnames)))
(defmacro gsk (k) `(mv-nth ,k (g-select (cadddr x) (1- k) em (gr1 2) (gr1 3) self sigs fnames)))

(defthm grl-chain
  (implies (and (consp x) (<= 3 (g-chain x nil nil))
                (grl-ok :ret (caddr x) 0 em cnt locs self sigs fnames)
                (grl-ok :sel (cadddr x) (1- (g-chain x nil nil)) em (gr1 2) (gr1 3) self sigs fnames))
           (grl-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (grl-ok) (g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p))
           :expand ((g-ret x em cnt locs self sigs fnames))
           :use ((:instance subsetp-trans (a locs) (b (gr1 3)) (c (gsel 4)))))))

(defthm grl-if
  (implies (and (consp x) (not (<= 3 (g-chain x nil nil))) (eq (car x) 'if) (true-listp x) (= (len x) 4)
                (grl-ok :ret (caddr x) 0 em (gc1 4) (gc1 5) self sigs fnames)
                (grl-ok :ret (cadddr x) 0 em (gi1 2) (gi1 3) self sigs fnames))
           (grl-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (grl-ok) (g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p))
           :expand ((g-ret x em cnt locs self sigs fnames))
           :use ((:instance subsetp-trans (a locs) (b (gc1 5)) (c (gi1 3)))
                 (:instance subsetp-trans (a locs) (b (gi1 3))
                            (c (mv-nth 3 (g-ret (cadddr x) em (gi1 2) (gi1 3) self sigs fnames))))))))

(defthm grl-other
  (implies (not (and (consp x) (or (<= 3 (g-chain x nil nil))
                                   (and (eq (car x) 'if) (true-listp x) (= (len x) 4)))))
           (grl-ok :ret x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (grl-ok) (g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p))
           :expand ((g-ret x em cnt locs self sigs fnames)))))

(defthm grl-sel-zp
  (implies (and (zp k) (grl-ok :ret x 0 em cnt locs self sigs fnames))
           (grl-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (grl-ok) (g-ret g-select))
           :expand ((g-select x k em cnt locs self sigs fnames)))))

(defthm grl-sel-bad
  (implies (and (not (zp k)) (not (and (consp x) (true-listp x) (= (len x) 4))))
           (grl-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (grl-ok) (g-ret g-select))
           :expand ((g-select x k em cnt locs self sigs fnames)))))

(defthm grl-sel-cons
  (implies (and (not (zp k))
                (grl-ok :ret (caddr x) 0 em cnt locs self sigs fnames)
                (grl-ok :sel (cadddr x) (1- k) em (gr1 2) (gr1 3) self sigs fnames))
           (grl-ok :sel x k em cnt locs self sigs fnames))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (grl-ok) (g-ret g-select g-case-key int-lit-p))
           :expand ((g-select x k em cnt locs self sigs fnames))
           :use ((:instance subsetp-trans (a locs) (b (gr1 3)) (c (gsk 4)))))))

(defthm grl-ok-flag
  (implies (and (syntaxp (not (equal flag '':ret))) (not (equal flag :sel)))
           (equal (grl-ok flag x k em cnt locs self sigs fnames) (grl-ok :ret x k em cnt locs self sigs fnames)))
  :hints (("Goal" :in-theory (e/d (grl-ok) (g-ret g-select)))))

(defthm grl-ok-thm
  (grl-ok flag x k em cnt locs self sigs fnames)
  :rule-classes nil
  :hints (("Goal" :induct (gr-ind flag x k em cnt locs self sigs fnames env defs cs n fr) :do-not-induct t
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p fr-after))))

(defthm g-ret-locs
  (implies (not (mv-nth 0 (g-ret x em cnt locs self sigs fnames)))
           (subsetp-equal locs (mv-nth 3 (g-ret x em cnt locs self sigs fnames))))
  :hints (("Goal" :use (:instance grl-ok-thm (flag :ret)) :in-theory (e/d (grl-ok) (g-ret)))))

(defthm g-select-locs
  (implies (not (mv-nth 0 (g-select x k em cnt locs self sigs fnames)))
           (subsetp-equal locs (mv-nth 4 (g-select x k em cnt locs self sigs fnames))))
  :hints (("Goal" :use (:instance grl-ok-thm (flag :sel)) :in-theory (e/d (grl-ok) (g-select)))))

(defthm decl-ok-ret-locs
  (implies (and (not (mv-nth 0 (g-ret x em cnt locs self sigs fnames)))
                (decl-ok (mv-nth 3 (g-ret x em cnt locs self sigs fnames)) fr))
           (decl-ok locs fr))
  :hints (("Goal" :in-theory (disable g-ret decl-ok)
           :use ((:instance decl-ok-subset (a locs) (b (mv-nth 3 (g-ret x em cnt locs self sigs fnames))))))))

(defthm decl-ok-sel-locs
  (implies (and (not (mv-nth 0 (g-select x k em cnt locs self sigs fnames)))
                (decl-ok (mv-nth 4 (g-select x k em cnt locs self sigs fnames)) fr))
           (decl-ok locs fr))
  :hints (("Goal" :in-theory (disable g-select decl-ok)
           :use ((:instance decl-ok-subset (a locs) (b (mv-nth 4 (g-select x k em cnt locs self sigs fnames))))))))

; ---- a case chain: every arm tests one variable

(defun chain-v (x) (mv-let (v k) (g-case-key (kadr x)) (declare (ignore k)) v))

(defun chain-on (v x k)
  (if (zp k) t
    (and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4)
         (equal (chain-v x) v)
         (chain-on v (cadddr x) (1- k)))))

(defun gch-ind (x v keys k)
  (if (zp k) (list x v keys)
    (mv-let (kv key) (g-case-key (cadr x))
      (declare (ignore kv))
      (gch-ind (cadddr x) v (cons key keys) (1- k)))))

(defthm g-chain-on
  (implies (and v (<= k (g-chain x v keys))) (chain-on v x k))
  :hints (("Goal" :induct (gch-ind x v keys k) :expand ((g-chain x v keys))
           :in-theory (disable g-case-key))))

(defthm g-chain-first
  (implies (<= 3 (g-chain x nil nil))
           (and (consp x) (equal (car x) 'if) (true-listp x) (equal (len x) 4)
                (chain-v x)
                (equal (g-chain x nil nil)
                       (1+ (g-chain (cadddr x) (chain-v x) (list (mv-nth 1 (g-case-key (cadr x)))))))))
  :rule-classes nil
  :hints (("Goal" :expand ((g-chain x nil nil)) :in-theory (disable g-case-key))))

(defthm a-ev-quote
  (implies (and (consp x) (equal (car x) 'quote))
           (equal (a-ev x env defs n) (if (zp n) (mv :fuel nil) (mv nil (kadr x)))))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

(defthm a-ev-non-sym-atom
  (implies (and (atom x) (not (symbolp x)))
           (equal (a-ev x env defs n) (if (zp n) (mv :fuel nil) (mv :syntax nil))))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

; the test (equal v 'k): true just when v's value is k
(defthm case-key-test
  (implies (and (mv-nth 0 (g-case-key c)) (not (car (a-ev c env defs n))) (no-prim-defs defs))
           (and (consp (lkp (mv-nth 0 (g-case-key c)) env))
                (iff (mv-nth 1 (a-ev c env defs n))
                     (equal (cdr (lkp (mv-nth 0 (g-case-key c)) env)) (mv-nth 1 (g-case-key c))))))
  :hints (("Goal" :in-theory (disable a-ev) :do-not-induct t)))

; ---- fsem's SELECT, one arm at a time (gen-cf's fx-arms-is-lkp off)

(in-theory (disable fx-arms-is-lkp))

(defthm fx-select-stmt
  (implies (and (not (car (fv c fr))) (integerp (mv-nth 1 (fv c fr))))
           (equal (fx (list :select c arms dflt) fr) (fx-arms (mv-nth 1 (fv c fr)) arms dflt fr)))
  :hints (("Goal" :expand ((fx (list :select c arms dflt) fr)) :in-theory (disable fx-arms fv))))

(defthm fx-arms-cons
  (equal (fx-arms v (cons (list key sa) arms) dflt fr)
         (if (equal key v) (fx-list sa fr) (fx-arms v arms dflt fr)))
  :hints (("Goal" :expand ((fx-arms v (cons (list key sa) arms) dflt fr)) :in-theory (disable fx-list))))

(defthm fx-arms-nil
  (equal (fx-arms v nil dflt fr) (fx-list dflt fr))
  :hints (("Goal" :expand ((fx-arms v nil dflt fr)) :in-theory (disable fx-list))))

(defthm fv-var-int
  (implies (and (equal (cdr (lkp nm fr)) (cons :int64 val)) (int64p val))
           (equal (fv (list :var nm) fr) (mv nil val))))

(defthm fx-return (equal (fx '(:return) fr) (mv :return fr)) :hints (("Goal" :expand ((fx '(:return) fr)))))

(defthm g-case-key-none
  (implies (not (mv-nth 0 (g-case-key c))) (equal (mv-nth 1 (g-case-key c)) nil)))

(defthm g-select-zp-arms
  (implies (zp k) (equal (mv-nth 1 (g-select x k em cnt locs self sigs fnames)) nil))
  :hints (("Goal" :expand ((g-select x k em cnt locs self sigs fnames)) :in-theory (disable g-ret))))

; ---- what g-ret's statements do: :return, "r" holding a-ev's value

(defmacro gr-hyps (locs2)
  `(and (no-calls :term x sigs cs) (a-orc defs sigs cs) (not (member-equal self cs)) (consp (lkp self sigs)) (symbolp self) (not (equal self 'quote))
        (em-ok em env fr) (decl-ok ,locs2 fr) (no-prim-defs defs) (equal (dty "r" fr) (list (rty)))))

(defun gr-sem (x em cnt locs self sigs fnames env defs cs n fr)
  (declare (xargs :verify-guards nil))
  (mv-let (e s cnt2 locs2) (g-ret x em cnt locs self sigs fnames)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-ev x env defs n)
      (implies (and (not e) (not ae) (gr-hyps locs2))
               (mv-let (st fr2) (fx-list s fr)
                 (and (equal st :return) (ret-ok fr2 (rty) v)))))))

(defun gsel-sem (x k em cnt locs self sigs fnames env defs cs n fr)
  (declare (xargs :verify-guards nil))
  (mv-let (e arms dflt cnt2 locs2) (g-select x k em cnt locs self sigs fnames)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-ev x env defs n)
      (implies (and (not e) (not ae) (gr-hyps locs2) (chain-on (chain-v x) x k))
               (mv-let (st fr2) (fx-arms (cdr (lkp (chain-v x) env)) arms dflt fr)
                 (and (equal st :return) (ret-ok fr2 (rty) v)))))))

(defmacro gro (k) `(mv-nth ,k (g-ret x em cnt locs self sigs fnames)))
(defmacro gso (j) `(mv-nth ,j (g-select x k em cnt locs self sigs fnames)))

(defthm gr-sem-use
  (implies (and (gr-sem x em cnt locs self sigs fnames env defs cs n fr)
                (not (gro 0)) (not (car (a-ev x env defs n))) (gr-hyps (gro 3)))
           (and (equal (car (fx-list (gro 1) fr)) :return)
                (implies (equal rt (rty)) (ret-ok (mv-nth 1 (fx-list (gro 1) fr)) rt (mv-nth 1 (a-ev x env defs n))))))
  :hints (("Goal" :in-theory (e/d (gr-sem) (g-ret a-ev fx-list ret-ok no-calls em-ok decl-ok dty)))))

(defthm gsel-sem-use
  (implies (and (gsel-sem x k em cnt locs self sigs fnames env defs cs n fr)
                (not (gso 0)) (not (car (a-ev x env defs n))) (gr-hyps (gso 4)) (chain-on (chain-v x) x k)
                (equal val (cdr (lkp (chain-v x) env))))
           (and (equal (car (fx-arms val (gso 1) (gso 2) fr)) :return)
                (implies (equal rt (rty))
                         (ret-ok (mv-nth 1 (fx-arms val (gso 1) (gso 2) fr)) rt (mv-nth 1 (a-ev x env defs n))))))
  :hints (("Goal" :in-theory (e/d (gsel-sem) (g-select a-ev fx-arms ret-ok no-calls em-ok decl-ok dty chain-on chain-v)))))

(defthm gsel-sem-use0
  (implies (and (gsel-sem x k em cnt locs self sigs fnames env defs cs n fr) (zp k)
                (not (gso 0)) (not (car (a-ev x env defs n))) (gr-hyps (gso 4)))
           (and (equal (car (fx-list (gso 2) fr)) :return)
                (implies (equal rt (rty))
                         (ret-ok (mv-nth 1 (fx-list (gso 2) fr)) rt (mv-nth 1 (a-ev x env defs n))))))
  :hints (("Goal" :in-theory (e/d (gsel-sem) (g-select a-ev fx-list ret-ok no-calls em-ok decl-ok dty chain-v)))))

(in-theory (disable gr-sem gsel-sem ret-ok))

(defthm ret-ok-put
  (equal (ret-ok (put "r" v fr) rt val) (and (equal v (cons rt val)) (scalar-ok rt val)))
  :hints (("Goal" :in-theory (enable ret-ok))))

(defthm ret-glue
  (let ((fra (mv-nth 1 (fx-list s fr))))
    (implies (and (equal (dty "r" fr) (list rt)) (equal (car (fx-list s fr)) :normal) (not (car (fv c fra)))
                  (scalar-ok rt (mv-nth 1 (fv c fra))))
             (equal (fx-list (append s (cons (list :assign '(:var "r") c) '((:return)))) fr)
                    (mv :return (put "r" (cons rt (mv-nth 1 (fv c fra))) fra)))))
  :hints (("Goal" :use (:instance bind-glue (tmp "r") (ss '((:return))))
           :in-theory (disable bind-glue fx fv fx-list dty scalar-ok))))

(defthm gr-other
  (implies (not (and (consp x) (or (<= 3 (g-chain x nil nil))
                                   (and (eq (car x) 'if) (true-listp x) (= (len x) 4)))))
           (gr-sem x em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((gr-sem x em cnt locs self sigs fnames env defs cs n fr)
                                            (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p a-ev fx-list fv
                               no-calls em-ok scalar-ok dty fx-list-append)
           :use ((:instance ge-sem-all) ge-sem-use))))

; ---- the chain's variable, kept whole

(defthm chain-v-is
  (implies (consp x) (equal (mv-nth 0 (g-case-key (cadr x))) (chain-v x))))

(defthm chain-v-none
  (implies (and (consp x) (not (chain-v x))) (equal (mv-nth 1 (g-case-key (cadr x))) nil)))

(defthm g-chain-next-v
  (implies (<= 3 (g-chain x nil nil)) (equal (chain-v (cadddr x)) (chain-v x)))
  :hints (("Goal" :expand ((g-chain x nil nil) (g-chain (cadddr x) (mv-nth 0 (g-case-key (cadr x)))
                                                         (list (mv-nth 1 (g-case-key (cadr x))))))
           :in-theory (e/d (chain-v) (g-case-key chain-v-is chain-v-none)))))

(defthm chain-on-v
  (implies (and (chain-on v x k) (syntaxp (not (equal v (list 'chain-v x)))) (not (zp k))) (equal (chain-v x) v)))

(in-theory (disable chain-v))

(defthm gr-if
  (implies (and (consp x) (not (<= 3 (g-chain x nil nil))) (eq (car x) 'if) (true-listp x) (= (len x) 4)
                (gr-sem (caddr x) em (gc1 4) (gc1 5) self sigs fnames env defs cs (1- n) (fr-after (gc1 1) fr))
                (gr-sem (cadddr x) em (gi1 2) (gi1 3) self sigs fnames env defs cs (1- n) (fr-after (gc1 1) fr)))
           (gr-sem x em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((gr-sem x em cnt locs self sigs fnames env defs cs n fr)
                                            (g-ret x em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p a-ev fx-list fv
                               no-calls em-ok scalar-ok dty fx decl-ok-ret-locs)
           :use ((:instance ge-sem-all (x (cadr x)) (n (1- n)))
                 (:instance decl-ok-ret-locs (x (caddr x)) (cnt (gc1 4)) (locs (gc1 5)))
                 (:instance decl-ok-ret-locs (x (cadddr x)) (cnt (gi1 2)) (locs (gi1 3)))))))

(defthm scalar-ok-int64 (equal (scalar-ok :int64 v) (int64p v)))

(defthm gr-chain
  (implies (and (consp x) (<= 3 (g-chain x nil nil))
                (gr-sem (caddr x) em cnt locs self sigs fnames env defs cs (1- n) fr)
                (gsel-sem (cadddr x) (1- (g-chain x nil nil)) em (gr1 2) (gr1 3) self sigs fnames env defs cs (1- n) fr))
           (gr-sem x em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((gr-sem x em cnt locs self sigs fnames env defs cs n fr)
                                            (g-ret x em cnt locs self sigs fnames))
           :in-theory (e/d (var-ok) (g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p a-ev fx-list fv
                                    no-calls em-ok scalar-ok dty fx decl-ok-ret-locs decl-ok-sel-locs em-ok-necc
                                    case-key-test fx-arms))
           :use (g-chain-first
                 (:instance g-chain-on (x (cadddr x)) (v (chain-v x)) (keys (list (mv-nth 1 (g-case-key (cadr x)))))
                            (k (1- (g-chain x nil nil))))
                 (:instance em-ok-necc (x (chain-v x)))
                 (:instance case-key-test (c (cadr x)) (n (1- n)))
                 (:instance decl-ok-sel-locs (x (cadddr x)) (k (1- (g-chain x nil nil))) (cnt (gr1 2)) (locs (gr1 3)))))))

(defthm gsel-zp
  (implies (and (zp k) (gr-sem x em cnt locs self sigs fnames env defs cs n fr))
           (gsel-sem x k em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((gsel-sem x k em cnt locs self sigs fnames env defs cs n fr)
                                            (g-select x k em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select a-ev fx-list no-calls em-ok dty))))

(defthm gsel-bad
  (implies (and (not (zp k)) (not (and (consp x) (true-listp x) (= (len x) 4))))
           (gsel-sem x k em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :expand ((gsel-sem x k em cnt locs self sigs fnames env defs cs n fr)
                                            (g-select x k em cnt locs self sigs fnames))
           :in-theory (disable g-ret g-select a-ev fx-list no-calls em-ok dty))))

(defthm gsel-cons
  (implies (and (not (zp k)) (consp x) (true-listp x) (= (len x) 4)
                (gr-sem (caddr x) em cnt locs self sigs fnames env defs cs (1- n) fr)
                (gsel-sem (cadddr x) (1- k) em (gr1 2) (gr1 3) self sigs fnames env defs cs (1- n) fr))
           (gsel-sem x k em cnt locs self sigs fnames env defs cs n fr))
  :hints (("Goal" :do-not-induct t :cases ((zp (1- k))) :expand ((gsel-sem x k em cnt locs self sigs fnames env defs cs n fr)
                                            (g-select x k em cnt locs self sigs fnames)
                                            (chain-on (chain-v x) x k))
           :in-theory (disable g-ret g-select g-case-key int-lit-p a-ev fx-list fv no-calls em-ok scalar-ok dty fx
                               decl-ok-ret-locs decl-ok-sel-locs case-key-test fx-arms)
           :use ((:instance case-key-test (c (cadr x)) (n (1- n)))
                 (:instance decl-ok-sel-locs (x (cadddr x)) (k (1- k)) (cnt (gr1 2)) (locs (gr1 3)))))))

(defthm gr-sem-thm
  (if (eq flag :sel) (gsel-sem x k em cnt locs self sigs fnames env defs cs n fr)
    (gr-sem x em cnt locs self sigs fnames env defs cs n fr))
  :rule-classes nil
  :hints (("Goal" :induct (gr-ind flag x k em cnt locs self sigs fnames env defs cs n fr) :do-not-induct t
           :in-theory (disable g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p fr-after))))
