; gen-stexp: g-sexpr against a-sx, on sv/sx-list (gen-stx), per case
; (GEN.md "What remains" 4 (a), step (1)). As gen-proof does for g-expr,
; each case is its own lemma taking its parts' results as hypotheses.
; Here first: what sx-list keeps (the frame outside its assignments, the
; declared types), and what sv reads (sv-names), sx's analogues of gen-cf's
; fx-list-keeps and fv-agree.

(in-package "ACL2")

(include-book "gen-stx")
(include-book "gen-stsem")
(include-book "gen-cfout")

; ---- what sx-list keeps

(defun sxk-ind (flag s fr heap)
  (declare (xargs :measure (acl2-count s) :verify-guards nil))
  (if (atom s) (list fr heap)
    (if (eq flag :stmt)
        (mv-let (err v) (sv (kadr s) fr heap)
          (declare (ignore err))
          (list (sxk-ind :list (kaddr s) fr heap) (sxk-ind :list (kadddr s) fr heap)
                (sxk-ind :list (kadr (lkp v (kaddr s))) fr heap)))
      (mv-let (st fr2 h2) (sx (car s) fr heap)
        (declare (ignore st))
        (list (sxk-ind :stmt (car s) fr heap) (sxk-ind :list (cdr s) fr2 h2))))))

(defun skp-stmt (n s fr heap)
  (mv-let (st fr2 h2) (sx s fr heap)
    (declare (ignore st h2))
    (and (implies (not (member-equal n (asg :list (list s)))) (equal (lkp n fr2) (lkp n fr)))
         (equal (dty n fr2) (dty n fr)))))

(defun skp-list (n ss fr heap)
  (mv-let (st fr2 h2) (sx-list ss fr heap)
    (declare (ignore st h2))
    (and (implies (not (member-equal n (asg :list ss))) (equal (lkp n fr2) (lkp n fr)))
         (equal (dty n fr2) (dty n fr)))))

(defthm skp-assign
  (implies (eq (kar s) :assign) (skp-stmt n s fr heap))
  :hints (("Goal" :expand ((sx s fr heap) (asg :list (list s))))))

(defthm skp-if
  (implies (and (eq (kar s) :if) (skp-list n (kaddr s) fr heap) (skp-list n (kadddr s) fr heap))
           (skp-stmt n s fr heap))
  :hints (("Goal" :in-theory (disable dty sx-list) :expand ((sx s fr heap) (asg :list (list s))))))

(defthm skp-select
  (implies (and (eq (kar s) :select) (skp-list n (kadddr s) fr heap)
                (skp-list n (kadr (lkp (mv-nth 1 (sv (kadr s) fr heap)) (kaddr s))) fr heap))
           (skp-stmt n s fr heap))
  :hints (("Goal" :in-theory (disable dty sx-list) :expand ((sx s fr heap) (asg :list (list s)))
           :use ((:instance asg-lkp-arm (k (mv-nth 1 (sv (kadr s) fr heap))) (arms (kaddr s)))))))

(defthm skp-other
  (implies (not (member-equal (kar s) '(:assign :if :select))) (skp-stmt n s fr heap))
  :hints (("Goal" :in-theory (disable dty) :expand ((sx s fr heap)))))

(defthm skp-nil
  (implies (atom ss) (skp-list n ss fr heap))
  :hints (("Goal" :expand ((sx-list ss fr heap)))))

(defthm skp-cons
  (implies (and (consp ss) (skp-stmt n (car ss) fr heap)
                (skp-list n (cdr ss) (mv-nth 1 (sx (car ss) fr heap)) (mv-nth 2 (sx (car ss) fr heap))))
           (skp-list n ss fr heap))
  :hints (("Goal" :in-theory (disable dty sx) :expand ((sx-list ss fr heap) (asg :list ss)))))

(defthm skp-flag
  (if (eq flag :stmt) (skp-stmt n s fr heap) (skp-list n s fr heap))
  :rule-classes nil
  :hints (("Goal" :induct (sxk-ind flag s fr heap) :do-not-induct t
           :in-theory (disable skp-stmt skp-list sx sx-list kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select))))))

(defthm sx-list-keeps
  (and (implies (not (member-equal n (asg :list s)))
                (equal (lkp n (mv-nth 1 (sx-list s fr heap))) (lkp n fr)))
       (equal (dty n (mv-nth 1 (sx-list s fr heap))) (dty n fr)))
  :hints (("Goal" :use (:instance skp-flag (flag :list)))))

(defthm sx-list-agree
  (implies (not (intersectp-equal ns (asg :list s)))
           (lkp-agree ns fr (mv-nth 1 (sx-list s fr heap))))
  :hints (("Goal" :induct (lkp-agree-ind ns))))

(defthm decl-ok-after-sx
  (equal (decl-ok locs (mv-nth 1 (sx-list s fr heap))) (decl-ok locs fr))
  :hints (("Goal" :induct (len locs))))

(defthm em-ok-after-sx
  (implies (and (em-ok em env fr) (not (intersectp-equal (asg :list s) (em-names em))))
           (em-ok em env (mv-nth 1 (sx-list s fr heap))))
  :hints (("Goal" :do-not-induct t :expand ((em-ok em env (mv-nth 1 (sx-list s fr heap))))
           :in-theory (e/d (var-ok) (em-ok-necc sx-list sx-list-keeps not-member-intersect))
           :use ((:instance em-ok-necc (x (em-ok-witness em env (mv-nth 1 (sx-list s fr heap)))))
                 (:instance sx-list-keeps (n (cadr (lkp (em-ok-witness em env (mv-nth 1 (sx-list s fr heap))) em))))
                 (:instance not-member-intersect (y (cadr (lkp (em-ok-witness em env (mv-nth 1 (sx-list s fr heap))) em)))
                            (a (em-names em)) (b (asg :list s)))))))

; an object's binding: no assignment changes it (a variable assignment
; needs a scalar)
(defun sko-stmt (o s fr heap)
  (mv-let (st fr2 h2) (sx s fr heap)
    (declare (ignore st h2))
    (implies (equal (cadr (lkp o fr)) :obj) (equal (lkp o fr2) (lkp o fr)))))

(defun sko-list (o ss fr heap)
  (mv-let (st fr2 h2) (sx-list ss fr heap)
    (declare (ignore st h2))
    (implies (equal (cadr (lkp o fr)) :obj) (equal (lkp o fr2) (lkp o fr)))))

(defthm sko-assign
  (implies (eq (kar s) :assign) (sko-stmt o s fr heap))
  :hints (("Goal" :expand ((sx s fr heap)))))

(defthm sko-if
  (implies (and (eq (kar s) :if) (sko-list o (kaddr s) fr heap) (sko-list o (kadddr s) fr heap))
           (sko-stmt o s fr heap))
  :hints (("Goal" :in-theory (disable sx-list) :expand ((sx s fr heap)))))

(defthm sko-select
  (implies (and (eq (kar s) :select) (sko-list o (kadddr s) fr heap)
                (sko-list o (kadr (lkp (mv-nth 1 (sv (kadr s) fr heap)) (kaddr s))) fr heap))
           (sko-stmt o s fr heap))
  :hints (("Goal" :in-theory (disable sx-list) :expand ((sx s fr heap)))))

(defthm sko-other
  (implies (not (member-equal (kar s) '(:assign :if :select))) (sko-stmt o s fr heap))
  :hints (("Goal" :expand ((sx s fr heap)))))

(defthm sko-nil
  (implies (atom ss) (sko-list o ss fr heap))
  :hints (("Goal" :expand ((sx-list ss fr heap)))))

(defthm sko-cons
  (implies (and (consp ss) (sko-stmt o (car ss) fr heap)
                (sko-list o (cdr ss) (mv-nth 1 (sx (car ss) fr heap)) (mv-nth 2 (sx (car ss) fr heap))))
           (sko-list o ss fr heap))
  :hints (("Goal" :in-theory (disable sx) :expand ((sx-list ss fr heap)))))

(defthm sko-flag
  (if (eq flag :stmt) (sko-stmt o s fr heap) (sko-list o s fr heap))
  :rule-classes nil
  :hints (("Goal" :induct (sxk-ind flag s fr heap) :do-not-induct t
           :in-theory (disable sko-stmt sko-list sx sx-list kar kadr kaddr kadddr))
          (and stable-under-simplificationp
               '(:cases ((eq (kar s) :assign) (eq (kar s) :if) (eq (kar s) :select))))))

(defthm sx-list-keeps-obj
  (implies (equal (cadr (lkp o fr)) :obj) (equal (lkp o (mv-nth 1 (sx-list ss fr heap))) (lkp o fr)))
  :hints (("Goal" :use (:instance sko-flag (flag :list) (s ss)))))

(defun sapp-ind (a fr heap)
  (if (atom a) (list fr heap)
    (mv-let (st fr2 h2) (sx (car a) fr heap) (declare (ignore st)) (sapp-ind (cdr a) fr2 h2))))

(defthm sx-list-append
  (equal (sx-list (append a b) fr heap)
         (mv-let (st fr2 h2) (sx-list a fr heap)
           (if (eq st :normal) (sx-list b fr2 h2) (mv st fr2 h2))))
  :hints (("Goal" :induct (sapp-ind a fr heap) :in-theory (disable sx)
           :expand ((sx-list a fr heap) (sx-list (cons (car a) (append (cdr a) b)) fr heap) (sx-list b fr heap)))))

; ---- what sv reads: its variables and its objects

(defun sv-names (e)
  (declare (xargs :guard t))
  (case (kar e)
    ((:var :comp :size) (list (kadr e)))
    (:elem (cons (kadr e) (sv-names (kadddr e))))
    ((:neg :not) (sv-names (kadr e)))
    ((:add :sub :mul :eq :lt :le :ge :max) (append (sv-names (kadr e)) (sv-names (kaddr e))))
    (otherwise nil)))

(defthm sv-agree
  (implies (lkp-agree (sv-names e) fr fr2) (equal (sv e fr2 heap) (sv e fr heap)))
  :hints (("Goal" :induct (sv e fr heap) :in-theory (e/d ((:induction sv)) (binop arith read-elem))
           :expand ((sv e fr heap) (sv e fr2 heap) (sv-names e)))))

(defthm cf-sv-names (implies (cf-expr e) (equal (sv-names e) (ev-names e))))

; ---- the invariants: the stobj S is the components of the frame's object o
;
; obj-is: o names, in the frame, an object whose heap entry is S. st-ok:
; every stobj role in st names o (one stobj, as a-st threads one), a field
; S has is an int64, an array's length is an int64.

(defun obj-is (o s fr heap)
  (let ((b (cdr (lkp o fr))))
    (and (consp b) (eq (car b) :obj) (consp (cdr b)) (equal (cdr (lkp (cddr b) heap)) s))))

(defthm obj-is-after-sx
  (implies (obj-is o s fr heap) (obj-is o s (mv-nth 1 (sx-list ss fr heap)) heap)))

(defun-sk st-ok (st o s)
  (forall x (implies (member-eq (g-role x st) '(:field :size :elem :set :seti :stobj))
                     (and (equal (g-obj x st) o)
                          (implies (and (eq (g-role x st) :field) (consp (lkp (g-comp x st) s)))
                                   (int64p (cdr (lkp (g-comp x st) s))))
                          (implies (eq (g-role x st) :size) (int64p (len (cddr (lkp (g-comp x st) s)))))))))

(in-theory (disable st-ok))

; what is proved of g-sexpr: run by sx-list, its statements answer :normal,
; leave the heap as it was, and its code's sv is a-sx's value, of g-sexpr's
; type. Call-free (no-calls ... nil); mv-nth undefined in defs, so a-sx
; answers an error on (mv-nth 'k mv), which g-sexpr's mv lambda case takes.
(defun gs-sem (x em cnt locs sigs fnames st env s defs n fr heap o)
  (mv-let (e ss c ty cnt2 locs2) (g-sexpr x em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae v) (a-sx x env s st defs n)
      (implies (and (not e) (not ae) (no-calls :term x sigs nil) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (obj-is o s fr heap))
               (mv-let (stt fr2 h2) (sx-list ss fr heap)
                 (mv-let (fe fvv) (sv c fr2 heap)
                   (and (equal stt :normal) (equal h2 heap) (not fe) (equal fvv v) (scalar-ok ty v))))))))

; ---- the cases with no stobj in them: g-expr's, by ge-sem

(defthm a-ev-mv-nth
  (implies (and (g-mvnth x) (not (consp (lkp 'mv-nth defs)))) (mv-nth 0 (a-ev x env defs n)))
  :hints (("Goal" :expand ((a-ev x env defs n) (a-ev-list (cdr x) env defs (1- n))
                           (a-ev-list (cddr x) env defs (+ -1 -1 n))))))

(defthm g-mvnth-free
  (implies (and (g-mvnth x) (not (g-role 'mv-nth st)) (not (g-role 'mv st))) (g-st-free x st))
  :hints (("Goal" :expand ((g-st-free x st) (g-st-free-list (cdr x) st) (g-st-free-list (cddr x) st)
                           (g-st-free-list (cdddr x) st) (g-st-free (cadr x) st) (g-st-free (caddr x) st)))))

(defthm gs-mvnth
  (implies (g-mvnth x) (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable a-ev g-mvnth g-st-free g-sexpr a-ev-mv-nth g-mvnth-free)
           :expand ((a-sx x env s st defs n))
           :use (g-mvnth-free a-ev-mv-nth))))

(defthm gs-free
  (implies (and (g-st-free x st) (not (g-mvnth x))) (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-expr a-ev g-st-free g-mvnth ge-sem fx-list fv)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (a-sx x env s st defs n))
           :use ((:instance ge-sem-thm (flag :expr) (vars nil) (cs nil))
                 (:instance g-expr-cf)))
          (and stable-under-simplificationp '(:in-theory (e/d (ge-sem) (g-expr a-ev g-st-free g-mvnth fx-list fv))))))

; ---- the stobj reads: hs%f, size(hs%a), hs%a(i)

(defthm g-role-symbolp (implies (not (symbolp x)) (not (g-role x st))))
(defthm g-role-quote (implies (g-role x st) (symbolp x)) :rule-classes :forward-chaining)

(defthm gs-field
  (implies (and (consp x) (eq (g-role (car x) st) :field))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-obj g-comp g-role)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (a-sx x env s st defs n) (g-st-free x st)
                    (sv (list :comp (g-obj (car x) st) (g-comp (car x) st)) fr heap) (sx-list nil fr heap))
           :use ((:instance st-ok-necc (x (car x)))))))

(defthm gs-size
  (implies (and (consp x) (eq (g-role (car x) st) :size))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-obj g-comp g-role)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (a-sx x env s st defs n) (g-st-free x st)
                    (sv (list :size (g-obj (car x) st) (g-comp (car x) st)) fr heap) (sx-list nil fr heap))
           :use ((:instance st-ok-necc (x (car x)))))))

(defthm read-elem-int64
  (implies (not (mv-nth 0 (read-elem v i)))
           (and (integerp (mv-nth 1 (read-elem v i)))
                (<= -9223372036854775808 (mv-nth 1 (read-elem v i)))
                (<= (mv-nth 1 (read-elem v i)) 9223372036854775807))))

(defthm read-elem-consp
  (implies (not (car (read-elem v i))) (consp v))
  :rule-classes ((:forward-chaining :trigger-terms ((car (read-elem v i))))))

(defthm read-elem-bounds-consp
  (implies (equal (car (read-elem v i)) :bounds) (consp v))
  :rule-classes :forward-chaining)

(defthm consp-cdr-lkp (implies (consp (cdr (lkp k al))) (consp (lkp k al))))

(defthm no-calls-elem
  (implies (and (consp x) (not (equal (car x) 'quote)) (not (consp (car x))) (no-calls :term x sigs cs))
           (no-calls :term (cadr x) sigs cs))
  :hints (("Goal" :expand ((no-calls :term x sigs cs) (no-calls :list (cdr x) sigs cs)))))

(defthm gs-elem
  (implies (and (consp x) (eq (g-role (car x) st) :elem)
                (gs-sem (cadr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-sexpr a-sx sx-list read-elem g-obj g-comp g-role)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (a-sx x env s st defs n) (g-st-free x st)
                    (:free (c fr) (sv (list :elem (g-obj (car x) st) (g-comp (car x) st) c) fr heap)))
           :use ((:instance st-ok-necc (x (car x)))))))

; the element read's :bounds, both sides: the index answering, a-sx's
; :bounds is the code's
(defthm gs-elem-bounds
  (implies (and (consp x) (eq (g-role (car x) st) :elem)
                (gs-sem (cadr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (not (mv-nth 0 (g-sexpr x em cnt locs sigs fnames st)))
                (not (mv-nth 0 (a-sx (cadr x) env s st defs (1- n))))
                (equal (mv-nth 0 (a-sx x env s st defs n)) :bounds)
                (no-calls :term x sigs nil) (em-ok em env fr)
                (decl-ok (mv-nth 5 (g-sexpr x em cnt locs sigs fnames st)) fr)
                (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                (not (equal (car x) 'quote)) (st-ok st o s) (obj-is o s fr heap))
           (mv-let (stt fr2 h2) (sx-list (mv-nth 1 (g-sexpr x em cnt locs sigs fnames st)) fr heap)
             (and (equal stt :normal) (equal h2 heap)
                  (equal (mv-nth 0 (sv (mv-nth 2 (g-sexpr x em cnt locs sigs fnames st)) fr2 heap)) :bounds))))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-sexpr a-sx sx-list read-elem g-obj g-comp g-role)
           :expand ((g-sexpr x em cnt locs sigs fnames st) (:free (s) (a-sx x env s st defs n)) (g-st-free x st)
                    (:free (c fr) (sv (list :elem (g-obj (car x) st) (g-comp (car x) st) c) fr heap)))
           :use ((:instance st-ok-necc (x (car x)))))
          (and stable-under-simplificationp '(:in-theory (e/d (read-elem) (g-sexpr a-sx sx-list g-obj g-comp g-role))))))
