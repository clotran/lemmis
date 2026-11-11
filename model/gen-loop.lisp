; gen-loop: the loop body, one iteration (GEN.md, layer 3). On source whose
; only calls of translated functions are tail self-calls (tail-only),
; g-ret's statements, run by fx, either answer :return with "r" holding
; a-ev's value of the body (as gen-ret's gr-sem), or answer :cycle with the
; formals' dummies holding new int64 values on which a-ev of the function's
; body, with less fuel, answers the same value (lp-ok). gen-loopfn.lisp
; runs the DO around it.

(in-package "ACL2")

(include-book "gen-tail")
(include-book "gen-fn")

(set-irrelevant-formals-ok t)

(defmacro fsg () '(kar (cdr (lkp self sigs))))
(defmacro bdy () '(kaddr (lkp self defs)))

; ---- the dummies after a CYCLE

(defun dvals (fs fr) (if (atom fs) nil (cons (cddr (lkp (g-formal (car fs)) fr)) (dvals (cdr fs) fr))))

(defun dums-ok (fs fr)
  (if (atom fs) t
    (and (equal (cdr (lkp (g-formal (car fs)) fr)) (cons :int64 (cddr (lkp (g-formal (car fs)) fr))))
         (int64p (cddr (lkp (g-formal (car fs)) fr)))
         (dums-ok (cdr fs) fr))))

; a-ev answers (mv nil v) with some fuel below n
(defun a-ev-below (b env defs n v)
  (if (zp n) nil
    (or (mv-let (e w) (a-ev b env defs (1- n)) (and (not e) (equal w v))) (a-ev-below b env defs (1- n) v))))

(defun lp-ok (st fr2 rt v self sigs defs n)
  (if (eq st :cycle)
      (and (dums-ok (fsg) fr2) (a-ev-below (bdy) (pairlis$ (fsg) (dvals (fsg) fr2)) defs n v))
    (and (equal st :return) (ret-ok fr2 rt v))))

(defun lp-hyps (self sigs defs fnames fr)
  (and (consp (lkp self defs)) (equal (kadr (lkp self defs)) (fsg)) (true-listp (fsg))
       (not (equal self 'if))
       (equal fnames (g-formals (fsg))) (no-duplicatesp-equal fnames) (int-dums (fsg) fr)))

(defthm lp-ok-return
  (implies (and (equal st :return) (ret-ok fr rt v)) (lp-ok st fr rt v self sigs defs n)))

(defthm lp-ok-mono
  (implies (and (lp-ok st fr rt v self sigs defs (+ -1 n)) (not (zp n))) (lp-ok st fr rt v self sigs defs n))
  :hints (("Goal" :expand ((a-ev-below (bdy) (pairlis$ (fsg) (dvals (fsg) fr)) defs n v)))))

(defthm int-dums-after
  (implies (int-dums vars fr) (int-dums vars (mv-nth 1 (fx-list s fr))))
  :hints (("Goal" :induct (int-dums vars fr) :in-theory (disable dty fx-list))))

(defthm lp-hyps-after
  (implies (lp-hyps self sigs defs fnames fr) (lp-hyps self sigs defs fnames (mv-nth 1 (fx-list s fr)))))

(in-theory (disable lp-ok lp-hyps))

(defun alen-ind (xs n) (if (or (zp n) (atom xs)) (list xs n) (alen-ind (cdr xs) (1- n))))

(defthm a-ev-list-len
  (implies (not (car (a-ev-list xs env defs n)))
           (and (true-listp (mv-nth 1 (a-ev-list xs env defs n)))
                (equal (len (mv-nth 1 (a-ev-list xs env defs n))) (len xs))))
  :hints (("Goal" :induct (alen-ind xs n) :in-theory (disable a-ev))))

(defthm tl-ok-int64
  (implies (and (tl-ok as vs fr) (true-listp vs) (equal (len vs) (len as))) (int64-listp vs))
  :hints (("Goal" :induct (as-ind as vs vs fr))))

(defthm dums-are-ok
  (implies (and (dums-are vars vs fr) (int64-listp vs) (equal (len vs) (len vars)))
           (and (dums-ok vars fr) (equal (dvals vars fr) vs)))
  :hints (("Goal" :induct (as-ind vars vars vs fr) :in-theory (disable g-formal))))

; ---- the tail call's statements: the arguments, the formals, CYCLE

(defthm fx-list-cycle (equal (fx-list (list '(:cycle)) fr) (mv :cycle fr))
  :hints (("Goal" :expand ((fx-list (list '(:cycle)) fr) (fx '(:cycle) fr) (fx-list nil fr)))))

(defthm subsetp-append-self (subsetp-equal a (append a b)))

(defthm tail-run
  (implies (and (not (car (g-tail vars xs em cnt locs sigs fnames))) (equal (len xs) (len vars))
                (not (car (a-ev-list xs env defs n))) (no-calls :list xs sigs) (em-ok em env fr)
                (decl-ok (gto 4) fr) (no-prim-defs defs)
                (equal fnames (g-formals vars)) (no-duplicatesp-equal fnames) (int-dums vars fr))
           (let ((r (fx-list (append (gto 1) (append (gto 2) (list '(:cycle)))) fr)))
             (and (equal (car r) :cycle) (dums-ok vars (mv-nth 1 r))
                  (equal (dvals vars (mv-nth 1 r)) (mv-nth 1 (a-ev-list xs env defs n))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (gt-as) (g-tail a-ev-list fx-list em-ok decl-ok no-calls tl-ok as-ok dums-are dums-ok
                                   dvals int-dums gt-as-thm as-run gt-sem-use g-formals))
           :use ((:instance gt-sem-use)
                 (:instance gt-as-thm)
                 (:instance as-run (as (gto 2)) (vs (mv-nth 1 (a-ev-list xs env defs n)))
                            (used (append fnames (em-names em))) (fr (mv-nth 1 (fx-list (gto 1) fr))))
                 (:instance tl-ok-int64 (as (gto 2)) (vs (mv-nth 1 (a-ev-list xs env defs n)))
                            (fr (mv-nth 1 (fx-list (gto 1) fr))))
                 (:instance dums-are-ok (vs (mv-nth 1 (a-ev-list xs env defs n)))
                            (fr (mv-nth 1 (fx-list (gto 2) (mv-nth 1 (fx-list (gto 1) fr))))))))))

; ---- what g-ret's statements do on tail-only source: lp-ok

(defmacro grt-hyps (locs2)
  `(and (tail-only x self sigs) (consp (lkp self sigs)) (symbolp self) (not (equal self 'quote))
        (em-ok em env fr) (decl-ok ,locs2 fr) (no-prim-defs defs) (equal (dty "r" fr) (list (rty)))
        (lp-hyps self sigs defs fnames fr)))

(defun grt-sem (x em cnt locs self sigs fnames env defs n fr)
  (declare (xargs :verify-guards nil))
  (mv-let (e s cnt2 locs2) (g-ret x em cnt locs self sigs fnames)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-ev x env defs n)
      (implies (and (not e) (not ae) (grt-hyps locs2))
               (mv-let (st fr2) (fx-list s fr)
                 (lp-ok st fr2 (rty) v self sigs defs n))))))

(defun gselt-sem (x k em cnt locs self sigs fnames env defs n fr)
  (declare (xargs :verify-guards nil))
  (mv-let (e arms dflt cnt2 locs2) (g-select x k em cnt locs self sigs fnames)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-ev x env defs n)
      (implies (and (not e) (not ae) (grt-hyps locs2) (chain-on (chain-v x) x k))
               (mv-let (st fr2) (fx-arms (cdr (lkp (chain-v x) env)) arms dflt fr)
                 (lp-ok st fr2 (rty) v self sigs defs n))))))

(defthm grt-sem-use
  (implies (and (grt-sem x em cnt locs self sigs fnames env defs n fr)
                (not (gro 0)) (not (car (a-ev x env defs n))) (grt-hyps (gro 3)) (equal rt (rty)))
           (lp-ok (car (fx-list (gro 1) fr)) (mv-nth 1 (fx-list (gro 1) fr)) rt (mv-nth 1 (a-ev x env defs n))
                  self sigs defs n))
  :hints (("Goal" :in-theory (e/d (grt-sem) (g-ret a-ev fx-list tail-only em-ok decl-ok dty)))))

(defthm gselt-sem-use
  (implies (and (gselt-sem x k em cnt locs self sigs fnames env defs n fr)
                (not (gso 0)) (not (car (a-ev x env defs n))) (grt-hyps (gso 4)) (chain-on (chain-v x) x k)
                (equal val (cdr (lkp (chain-v x) env))) (equal rt (rty)))
           (lp-ok (car (fx-arms val (gso 1) (gso 2) fr)) (mv-nth 1 (fx-arms val (gso 1) (gso 2) fr)) rt
                  (mv-nth 1 (a-ev x env defs n)) self sigs defs n))
  :hints (("Goal" :in-theory (e/d (gselt-sem) (g-select a-ev fx-arms tail-only em-ok decl-ok dty chain-on chain-v)))))

(defthm gselt-sem-use0
  (implies (and (gselt-sem x k em cnt locs self sigs fnames env defs n fr) (zp k)
                (not (gso 0)) (not (car (a-ev x env defs n))) (grt-hyps (gso 4)) (equal rt (rty)))
           (lp-ok (car (fx-list (gso 2) fr)) (mv-nth 1 (fx-list (gso 2) fr)) rt
                  (mv-nth 1 (a-ev x env defs n)) self sigs defs n))
  :hints (("Goal" :in-theory (e/d (gselt-sem) (g-select a-ev fx-list tail-only em-ok decl-ok dty chain-v)))))

(in-theory (disable grt-sem gselt-sem))

(defthm tail-only-plain
  (implies (and (tail-only x self sigs)
                (not (and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4)))
                (not (and (consp x) (eq (car x) self))))
           (no-calls :term x sigs)))

(defthm tail-only-if
  (implies (and (tail-only x self sigs) (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4))
           (and (no-calls :term (cadr x) sigs) (tail-only (caddr x) self sigs) (tail-only (cadddr x) self sigs))))

(defthm tail-only-self
  (implies (and (tail-only x self sigs) (consp x) (eq (car x) self) (not (eq self 'if)))
           (no-calls :list (cdr x) sigs)))

(defthm grt-plain
  (implies (and (not (and (consp x) (or (<= 3 (g-chain x nil nil))
                                        (and (eq (car x) 'if) (true-listp x) (= (len x) 4)))))
                (not (and (consp x) (eq (car x) self))))
           (grt-sem x em cnt locs self sigs fnames env defs n fr))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (grt-sem) (g-ret g-select g-expr g-tail g-case-key g-chain int-lit-p a-ev fx-list fv
                               tail-only no-calls em-ok scalar-ok dty gr-sem-use))
           :use ((:instance gr-other) (:instance gr-sem-use (rt (rty)))))))

(defthm g-chain-not-if
  (implies (not (equal (car x) 'if)) (equal (g-chain x v keys) 0))
  :hints (("Goal" :expand ((g-chain x v keys)))))

(defthm g-ret-self
  (implies (and (consp x) (equal (car x) self) (not (equal self 'if)))
           (equal (g-ret x em cnt locs self sigs fnames)
                  (let ((formals (kar (cdr (lkp self sigs)))))
                    (if (not (and (true-listp x) (equal (len (cdr x)) (len formals)))) (mv :arity nil cnt locs)
                      (mv-let (e s as cnt locs) (g-tail formals (cdr x) em cnt locs sigs fnames)
                        (if e (mv e nil cnt locs) (mv nil (append s as (list '(:cycle))) cnt locs)))))))
  :hints (("Goal" :expand ((g-ret x em cnt locs self sigs fnames)) :in-theory (disable g-tail g-expr g-select))))

(defthm grt-tail
  (implies (and (consp x) (eq (car x) self))
           (grt-sem x em cnt locs self sigs fnames env defs n fr))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (a-ev-below grt-sem lp-hyps lp-ok)
                           (g-ret g-select g-expr g-tail g-case-key int-lit-p a-ev fx-list fv tail-run
                            tail-only no-calls em-ok scalar-ok dty a-ev-list dums-ok dvals int-dums g-formals))
           :use ((:instance tail-run (vars (fsg)) (xs (cdr x)) (n (1- n)))))))
