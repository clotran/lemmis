; gen-loopfn: a tail-recursive function (GEN.md, layer 3). g-fn puts the
; body's statements in a DO when they hold a CYCLE. Each iteration is
; gen-loop's lp-ok: :return with "r" = a-ev's value, or :cycle with the
; formals holding arguments on which a-ev of the body answers that value
; with less fuel. So, by induction on a-ev's fuel, the DO answers :return
; with "r" = a-ev's value (do-run), at any fsem fuel past n * K, K the
; statements' size plus 2: the bound m >= n * K. g-fn-sem-loop is
; gen-fn's g-fn-sem for tail-only bodies (the call-free ones included).

(in-package "ACL2")

(include-book "gen-loopcc")

(set-irrelevant-formals-ok t)

(in-theory (disable ge-sem-t))

; ---- the fuel a-ev-below found

(defun below-k (b env defs n v)
  (if (zp n) 0
    (if (mv-let (e w) (a-ev b env defs (1- n)) (and (not e) (equal w v))) (1- n) (below-k b env defs (1- n) v))))

(defthm below-k-facts
  (implies (a-ev-below b env defs n v)
           (and (natp (below-k b env defs n v)) (< (below-k b env defs n v) n)
                (not (car (a-ev b env defs (below-k b env defs n v))))
                (equal (mv-nth 1 (a-ev b env defs (below-k b env defs n v))) v)))
  :hints (("Goal" :in-theory (disable a-ev))))

; ---- the dummies after CYCLE are the next iteration's em-ok frame

(defthm var-ok-dvals
  (implies (dums-ok fs fr) (var-ok x (g-em fs) (pairlis$ fs (dvals fs fr)) fr))
  :hints (("Goal" :induct (dvals fs fr) :in-theory (e/d (var-ok) (g-formal)))))

(defthm em-ok-dvals
  (implies (dums-ok fs fr) (em-ok (g-em fs) (pairlis$ fs (dvals fs fr)) fr))
  :hints (("Goal" :expand ((em-ok (g-em fs) (pairlis$ fs (dvals fs fr)) fr)) :in-theory (disable var-ok dvals dums-ok))))

(defthm lkp-g-em-member
  (implies (member-equal x fs) (equal (lkp x (g-em fs)) (list* x (g-formal x) :int64))))

(defthm lkp-pairlis-member
  (implies (and (member-equal x fs) (equal (len ks) (len fs))) (consp (lkp x (pairlis$ fs ks)))))

(defthm em-ok-dty-formal
  (implies (and (em-ok (g-em fs0) (pairlis$ fs0 ks) fr) (member-equal x fs0) (equal (len ks) (len fs0)))
           (equal (dty (g-formal x) fr) (list :int64)))
  :hints (("Goal" :in-theory (e/d (dty var-ok) (g-formal em-ok em-ok-necc))
           :use ((:instance em-ok-necc (em (g-em fs0)) (env (pairlis$ fs0 ks)))))))

(defthm em-ok-int-dums
  (implies (and (em-ok (g-em fs0) (pairlis$ fs0 ks) fr) (subsetp-equal fs fs0) (equal (len ks) (len fs0)))
           (int-dums fs fr))
  :hints (("Goal" :induct (int-dums fs fr) :in-theory (disable g-formal em-ok dty))))

; ---- no CYCLE statement, no :cycle

(defthm g-has-cycle-parts
  (implies (not (g-has '(:cycle) x))
           (and (not (g-has '(:cycle) (kar x))) (not (g-has '(:cycle) (kdr x)))))
  :hints (("Goal" :expand ((g-has '(:cycle) x)))))

(defthm g-has-car-cdr
  (implies (and (consp x) (or (g-has a (car x)) (g-has a (cdr x)))) (g-has a x))
  :hints (("Goal" :expand ((g-has a x)))))

(defthm g-has-cycle-lkp
  (implies (not (g-has '(:cycle) arms)) (not (g-has '(:cycle) (lkp k arms))))
  :hints (("Goal" :induct (lkp k arms) :expand ((g-has '(:cycle) arms) (g-has '(:cycle) (car arms))))))

(defun nc-stmt (s fr)
  (mv-let (st fr2) (fx s fr) (declare (ignore fr2))
    (implies (and (cc-stmt s) (not (g-has '(:cycle) s))) (not (equal st :cycle)))))

(defun nc-list (ss fr)
  (mv-let (st fr2) (fx-list ss fr) (declare (ignore fr2))
    (implies (and (cc-stmts ss) (not (g-has '(:cycle) ss))) (not (equal st :cycle)))))

(defthm nc-assign
  (implies (eq (kar s) :assign) (nc-stmt s fr))
  :hints (("Goal" :expand ((fx s fr)) :in-theory (disable fv g-has))))

(defthm nc-if
  (implies (and (eq (kar s) :if) (nc-list (kaddr s) fr) (nc-list (kadddr s) fr)) (nc-stmt s fr))
  :hints (("Goal" :expand ((fx s fr)) :in-theory (disable fv fx-list g-has cc-stmts))))

(defthm select-parts
  (implies (and (eq (kar s) :select) (cc-stmt s) (not (g-has '(:cycle) s)))
           (let ((l (if (lkp k (kaddr s)) (kadr (lkp k (kaddr s))) (kadddr s))))
             (and (cc-stmts l) (not (g-has '(:cycle) l)))))
  :hints (("Goal" :in-theory (disable g-has lkp cc-stmt-parts g-has-cycle-lkp g-has-cycle-parts)
           :use ((:instance cc-stmt-parts)
                 (:instance g-has-cycle-parts (x s)) (:instance g-has-cycle-parts (x (kdr s)))
                 (:instance g-has-cycle-parts (x (kdr (kdr s)))) (:instance g-has-cycle-parts (x (kdr (kdr (kdr s)))))
                 (:instance g-has-cycle-lkp (arms (kaddr s)))
                 (:instance g-has-cycle-parts (x (lkp k (kaddr s))))
                 (:instance g-has-cycle-parts (x (kdr (lkp k (kaddr s)))))))))

(defthm fx-select-open
  (implies (and (eq (kar s) :select) (not (car (fv (kadr s) fr))) (integerp (mv-nth 1 (fv (kadr s) fr))))
           (equal (fx s fr)
                  (let ((arm (lkp (mv-nth 1 (fv (kadr s) fr)) (kaddr s))))
                    (fx-list (if arm (kadr arm) (kadddr s)) fr))))
  :hints (("Goal" :expand ((fx s fr)) :in-theory (enable fx-arms-is-lkp))))

(defthm nc-select
  (implies (and (eq (kar s) :select) (nc-list (kadddr s) fr)
                (nc-list (kadr (lkp (mv-nth 1 (fv (kadr s) fr)) (kaddr s))) fr))
           (nc-stmt s fr))
  :hints (("Goal" :in-theory (disable fv fx-list g-has cc-stmts lkp kadr kaddr kadddr cc-stmt select-parts)
           :cases ((and (not (car (fv (kadr s) fr))) (integerp (mv-nth 1 (fv (kadr s) fr)))))
           :use ((:instance select-parts (k (mv-nth 1 (fv (kadr s) fr))))))
          ("Subgoal 2" :expand ((fx s fr)))))

(defthm nc-other
  (implies (not (member-equal (kar s) '(:assign :if :select))) (nc-stmt s fr))
  :hints (("Goal" :expand ((fx s fr) (cc-stmt s) (g-has '(:cycle) s)))))

(defthm nc-nil (implies (atom ss) (nc-list ss fr)) :hints (("Goal" :expand ((fx-list ss fr)))))

(defthm nc-cons
  (implies (and (consp ss) (nc-stmt (car ss) fr) (nc-list (cdr ss) (mv-nth 1 (fx (car ss) fr))))
           (nc-list ss fr))
  :hints (("Goal" :in-theory (disable fx cc-stmt g-has) :expand ((fx-list ss fr) (cc-stmts ss) (g-has '(:cycle) ss)))))

(defthm no-cycle-flag
  (if (eq flag :stmt) (nc-stmt s fr) (nc-list s fr))
  :rule-classes nil
  :hints (("Goal" :induct (asg-ind flag s fr) :do-not-induct t
           :in-theory (disable nc-stmt nc-list fx fx-list kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select))))))

(defthm no-cycle
  (implies (and (cc-stmts s) (not (g-has '(:cycle) s))) (not (equal (car (fx-list s fr)) :cycle)))
  :hints (("Goal" :use (:instance no-cycle-flag (flag :list)))))

; ---- the DO, by induction on a-ev's fuel

(defmacro lr (k) `(mv-nth ,k (g-ret body (g-em fs) 0 nil fn sigs (g-formals fs))))

(defmacro do-hyps ()
  '(and (not (lr 0)) (tail-only body fn sigs cs) (a-orc defs sigs cs) (not (member-equal fn cs)) (consp (lkp fn sigs)) (symbolp fn) (not (equal fn 'quote)) (not (equal fn 'if))
        (no-prim-defs defs) (equal fs (kar (cdr (lkp fn sigs)))) (equal body (kaddr (lkp fn defs)))
        (equal rt (kadr (cdr (lkp fn sigs))))))

(defthm fuel-step
  (implies (and (natp k) (natp n) (< k n) (natp c) (<= 1 c) (integerp m) (< (* n c) m))
           (< (* k c) (+ -1 m)))
  :hints (("Goal" :nonlinearp t)))

(defmacro sok () (quote (and (cc-stmts s) (or (cf-stmts s) (p-orc procs heap b)) (natp b))))

; fx is f-ex: gen-cf's fx-list-is-f-ex-list on call-free statements, else
; gen-callev's fx-list-is-f-ex-list-c under p-orc
; the statements, the oracle and the DO's fuel per iteration c
(defun-nx s-ok (s procs heap b c)
  (and (sok) (natp c) (<= (* (+ 3 b) (+ 2 (acl2-count s))) c)))

(defthm s-ok-c (implies (s-ok s procs heap b c) (and (natp c) (< 1 c) (cc-stmts s))) :rule-classes :forward-chaining
  :hints (("Goal" :nonlinearp t)))

(in-theory (disable s-ok))

(defthm f-ex-list-either
  (implies (and (sok) (integerp k) (< (* (+ 3 b) (acl2-count s)) k) (member-equal (car (fx-list s fr)) (quote (:return :cycle))))
           (equal (f-ex-list s fr heap procs k) (+h (fx-list s fr) heap)))
  :rule-classes nil
  :hints (("Goal" :cases ((cf-stmts s)) :in-theory (disable fx-list f-ex-list fx-list-is-f-ex-list fx-list-is-f-ex-list-c))
          ("Subgoal 2" :use fx-list-is-f-ex-list-c)
          ("Subgoal 1" :nonlinearp t :use (:instance fx-list-is-f-ex-list (ss s)))))

(defthm do-return
  (implies (and (s-ok s procs heap b c) (integerp m) (< c m) (equal (car (fx-list s fr)) :return))
           (equal (f-ex (list :do s) fr heap procs m) (list :return (mv-nth 1 (fx-list s fr)) heap)))
  :hints (("Goal" :expand ((f-ex (list :do s) fr heap procs m)) :in-theory (e/d (s-ok) (fx-list f-ex-list-open))
           :use (:instance f-ex-list-either (k (+ -1 m))))))

(defthm do-cycle
  (implies (and (s-ok s procs heap b c) (integerp m) (< c m) (equal (car (fx-list s fr)) :cycle))
           (equal (f-ex (list :do s) fr heap procs m) (f-ex (list :do s) (mv-nth 1 (fx-list s fr)) heap procs (+ -1 m))))
  :hints (("Goal" :expand ((f-ex (list :do s) fr heap procs m)) :in-theory (e/d (s-ok) (fx-list f-ex-list-open))
           :use (:instance f-ex-list-either (k (+ -1 m))))))

(defmacro inv-hyps ()
  '(and (em-ok (g-em fs) (pairlis$ fs vs) fr) (decl-ok (lr 3) fr) (equal (dty "r" fr) (list rt))
        (lp-hyps fn sigs defs (g-formals fs) fr)
        (not (car (a-ev body (pairlis$ fs vs) defs n))) (equal (mv-nth 1 (a-ev body (pairlis$ fs vs) defs n)) v)))

; one iteration, gen-loop2's theorem on the function's body
(defthm iter-ok
  (implies (and (do-hyps) (inv-hyps))
           (and (cc-stmts (lr 1))
                (lp-ok (car (fx-list (lr 1) fr)) (mv-nth 1 (fx-list (lr 1) fr)) rt v fn sigs defs n)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable g-ret a-ev fx-list tail-only em-ok decl-ok dty lp-hyps lp-ok g-em g-formals
                               grt-sem-use g-ret-tail-cc)
           :use ((:instance grt-sem-thm (flag :ret) (x body) (em (g-em fs)) (cnt 0) (locs nil) (self fn)
                            (fnames (g-formals fs)) (env (pairlis$ fs vs)) (k 0))
                 (:instance grt-sem-use (x body) (em (g-em fs)) (cnt 0) (locs nil) (self fn)
                            (fnames (g-formals fs)) (env (pairlis$ fs vs)))
                 (:instance g-ret-tail-cc (x body) (em (g-em fs)) (cnt 0) (locs nil) (self fn)
                            (fnames (g-formals fs)))))))

(defthm lp-ok-cases
  (implies (lp-ok st fr2 rt v self sigs defs n)
           (or (and (equal st :return) (ret-ok fr2 rt v))
               (and (equal st :cycle) (dums-ok (fsg) fr2) (a-ev-below (bdy) (pairlis$ (fsg) (dvals (fsg) fr2)) defs n v))))
  :rule-classes nil :hints (("Goal" :in-theory (enable lp-ok))))

(defthm count-pos-n
  (implies (not (car (a-ev body env defs n))) (posp n))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((a-ev body env defs n)))))

; the DO on any statement list s whose every iteration is lp-ok (iter-all)
(defun-nx inv (fs fn sigs defs rt locs2 body fr vs n v)
  (and (em-ok (g-em fs) (pairlis$ fs vs) fr) (decl-ok locs2 fr) (equal (dty "r" fr) (list rt))
       (lp-hyps fn sigs defs (g-formals fs) fr)
       (not (car (a-ev body (pairlis$ fs vs) defs n))) (equal (mv-nth 1 (a-ev body (pairlis$ fs vs) defs n)) v)))

(defun-nx iter-one (s fs fn sigs defs rt locs2 body fr vs n v)
  (implies (inv fs fn sigs defs rt locs2 body fr vs n v)
           (lp-ok (car (fx-list s fr)) (mv-nth 1 (fx-list s fr)) rt v fn sigs defs n)))

(defun-sk iter-all (s fs fn sigs defs rt locs2 body)
  (forall (fr vs n v) (iter-one s fs fn sigs defs rt locs2 body fr vs n v)))

(defthm inv-next
  (implies (and (inv fs fn sigs defs rt locs2 body fr vs n v)
                (dums-ok fs (mv-nth 1 (fx-list s fr)))
                (a-ev-below body (pairlis$ fs (dvals fs (mv-nth 1 (fx-list s fr)))) defs n v))
           (let* ((fr2 (mv-nth 1 (fx-list s fr))) (vs2 (dvals fs fr2)) (k (below-k body (pairlis$ fs vs2) defs n v)))
             (and (inv fs fn sigs defs rt locs2 body fr2 vs2 k v) (natp k) (< k n))))
  :hints (("Goal" :in-theory (e/d (inv) (a-ev fx-list em-ok decl-ok dty lp-hyps dvals dums-ok a-ev-below below-k
                                      g-em g-formals)))))

(in-theory (disable inv))

(defun-nx do-ind (s fs body defs v n vs fr m)
  (declare (xargs :measure (nfix n)
                  :hints (("Goal" :in-theory (union-theories '(natp nfix o-p o< o-finp zp) (theory 'minimal-theory))))))
  (if (zp n) (list vs fr m)
    (let* ((fr2 (mv-nth 1 (fx-list s fr))) (vs2 (dvals fs fr2)) (k (below-k body (pairlis$ fs vs2) defs n v)))
      (if (and (natp k) (< k n)) (do-ind s fs body defs v k vs2 fr2 (1- m)) nil))))

(defun-nx do-ok (s fr heap procs m rt v)
  (and (equal (car (f-ex (list :do s) fr heap procs m)) :return)
       (equal (caddr (f-ex (list :do s) fr heap procs m)) heap)
       (ret-ok (mv-nth 1 (f-ex (list :do s) fr heap procs m)) rt v)))

(defthm times-ge (implies (and (posp n) (natp c)) (<= c (* n c))) :hints (("Goal" :nonlinearp t)))

(defthm dr-ret
  (implies (and (s-ok s procs heap b c) (integerp m) (natp c) (< (* n c) m) (posp n)
                (equal (car (fx-list s fr)) :return) (ret-ok (mv-nth 1 (fx-list s fr)) rt v))
           (do-ok s fr heap procs m rt v))
  :hints (("Goal" :in-theory (disable fx-list f-ex ret-ok times-ge do-return do-cycle s-ok) :use (times-ge do-return do-cycle))))

(defthm dr-cyc
  (implies (and (s-ok s procs heap b c) (integerp m) (natp c) (< (* n c) m) (posp n)
                (equal (car (fx-list s fr)) :cycle)
                (do-ok s (mv-nth 1 (fx-list s fr)) heap procs (+ -1 m) rt v))
           (do-ok s fr heap procs m rt v))
  :hints (("Goal" :in-theory (disable fx-list f-ex ret-ok times-ge do-return do-cycle s-ok) :use (times-ge do-return do-cycle))))

(defthm iter-lp
  (implies (and (iter-all s fs fn sigs defs rt locs2 body) (inv fs fn sigs defs rt locs2 body fr vs n v))
           (lp-ok (car (fx-list s fr)) (mv-nth 1 (fx-list s fr)) rt v fn sigs defs n))
  :hints (("Goal" :in-theory (disable iter-all-necc lp-ok fx-list) :use iter-all-necc)))

(defthm inv-posp
  (implies (inv fs fn sigs defs rt locs2 body fr vs n v) (posp n))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable inv) :use (:instance count-pos-n (env (pairlis$ fs vs))))))

(in-theory (disable do-ok iter-all))

(defmacro do-h (fr vs n m)
  `(and (iter-all s fs fn sigs defs rt locs2 body) (s-ok s procs heap b c)
        (equal fs (kar (cdr (lkp fn sigs)))) (equal body (kaddr (lkp fn defs)))
        (inv fs fn sigs defs rt locs2 body ,fr ,vs ,n v)
        (integerp ,m) (natp c) (< (* (nfix ,n) c) ,m)))

(defmacro fr2 () '(mv-nth 1 (fx-list s fr)))
(defmacro kk () '(below-k body (pairlis$ fs (dvals fs (fr2))) defs n v))

(defthm do-step
  (implies (and (do-h fr vs n m)
                (implies (do-h (fr2) (dvals fs (fr2)) (kk) (+ -1 m))
                         (do-ok s (fr2) heap procs (+ -1 m) rt v)))
           (do-ok s fr heap procs m rt v))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable a-ev fx-list f-ex lp-ok inv iter-all do-ok dvals dums-ok a-ev-below below-k ret-ok
                               s-ok em-ok decl-ok lp-hyps acl2-count iter-lp inv-next fuel-step dr-ret dr-cyc)
           :use ((:instance lp-ok-cases (st (car (fx-list s fr))) (fr2 (fr2)) (self fn))
                 (:instance iter-lp)
                 (:instance inv-next)
                 (:instance fuel-step (k (kk)))
                 (:instance dr-ret)
                 (:instance dr-cyc)))))

(defthm do-step2
  (implies (and (do-h fr vs n m) (not (< (kk) n))) (do-ok s fr heap procs m rt v))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable a-ev fx-list f-ex lp-ok inv iter-all do-ok dvals dums-ok a-ev-below below-k ret-ok
                               s-ok em-ok decl-ok lp-hyps acl2-count iter-lp inv-next fuel-step dr-ret dr-cyc)
           :use ((:instance lp-ok-cases (st (car (fx-list s fr))) (fr2 (fr2)) (self fn))
                 (:instance iter-lp) (:instance inv-next) (:instance dr-ret)))))

(defthm do-run-abs
  (implies (do-h fr vs n m) (do-ok s fr heap procs m rt v))
  :hints (("Goal" :induct (do-ind s fs body defs v n vs fr m)
           :in-theory (disable a-ev fx-list f-ex lp-ok inv iter-all do-ok dvals dums-ok a-ev-below below-k ret-ok
                               s-ok em-ok decl-ok lp-hyps acl2-count iter-lp inv-next fuel-step dr-ret dr-cyc
                               lkp kar kdr kaddr))))

; fx is f-ex on s-ok statements, at fuel past c
(defthm s-ok-f-ex-list
  (implies (and (s-ok s procs heap b c) (integerp k) (< c k) (member-equal (car (fx-list s fr)) '(:return :cycle)))
           (equal (f-ex-list s fr heap procs k) (+h (fx-list s fr) heap)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (s-ok) (fx-list f-ex-list)) :use f-ex-list-either)))
