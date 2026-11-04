; gen-ret: the body in return position. g-ret's statements, run by fx, end
; in :return with "r" holding what a-ev says the body means (gr-sem); a
; case chain's SELECT picks the arm the if chain takes (gsel-sem), every arm
; testing the same variable (g-chain's invariant, chain-on here).

(in-package "ACL2")

(include-book "gen-proof2")

(set-irrelevant-formals-ok t)

(defthm ge-sem-all
  (ge-sem x em cnt locs sigs fnames env defs n fr)
  :rule-classes nil
  :hints (("Goal" :use (:instance ge-sem-thm (flag :expr) (vars nil)))))

(defmacro rty () '(kadr (cdr (lkp self sigs))))

(defun ret-ok (fr2 rt v) (equal (cdr (lkp "r" fr2)) (cons rt v)))

; ---- g-ret's recursion, carrying a-ev's env and fuel and the frame

(defun gr-ind (flag x k em cnt locs self sigs fnames env defs n fr)
  (declare (xargs :measure (if (eq flag :sel) (1+ (* 2 (acl2-count x))) (* 2 (acl2-count x)))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable g-case-key int-lit-p g-chain acl2-count)))))
  (if (eq flag :sel)
      (if (zp k) (gr-ind :ret x 0 em cnt locs self sigs fnames env defs n fr)
        (if (not (and (consp x) (true-listp x) (= (len x) 4))) nil
          (mv-let (e sa cnt1 locs1) (g-ret (caddr x) em cnt locs self sigs fnames)
            (declare (ignore e sa))
            (list (gr-ind :ret (caddr x) 0 em cnt locs self sigs fnames env defs (1- n) fr)
                  (gr-ind :sel (cadddr x) (1- k) em cnt1 locs1 self sigs fnames env defs (1- n) fr)))))
    (cond
     ((and (consp x) (<= 3 (g-chain x nil nil)))
      (mv-let (e sa cnt1 locs1) (g-ret (caddr x) em cnt locs self sigs fnames)
        (declare (ignore e sa))
        (list (gr-ind :ret (caddr x) 0 em cnt locs self sigs fnames env defs (1- n) fr)
              (gr-ind :sel (cadddr x) (1- (g-chain x nil nil)) em cnt1 locs1 self sigs fnames env defs (1- n) fr))))
     ((and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4))
      (mv-let (e sc cc tc cnt1 locs1) (g-expr (cadr x) em cnt locs sigs fnames)
        (declare (ignore e cc tc))
        (mv-let (e sa cnt2 locs2) (g-ret (caddr x) em cnt1 locs1 self sigs fnames)
          (declare (ignore e sa))
          (list (gr-ind :ret (caddr x) 0 em cnt1 locs1 self sigs fnames env defs (1- n) (fr-after sc fr))
                (gr-ind :ret (cadddr x) 0 em cnt2 locs2 self sigs fnames env defs (1- n) (fr-after sc fr))))))
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
