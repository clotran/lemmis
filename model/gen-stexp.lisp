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

; ---- a primitive on arguments reading the stobj

(defun svs-ok (cs ts vs fr heap)
  (if (atom cs) (atom vs)
    (mv-let (err v) (sv (car cs) fr heap)
      (and (consp vs) (not err) (equal v (car vs)) (scalar-ok (car ts) (car vs))
           (svs-ok (cdr cs) (cdr ts) (cdr vs) fr heap)))))

(defun gsa-sem (xs em cnt locs sigs fnames st env s defs n fr heap o)
  (mv-let (e ss cs ts cnt2 locs2) (g-sargs xs em cnt locs sigs fnames st)
    (declare (ignore cnt2))
    (mv-let (ae vs) (a-sx-list xs env s st defs n)
      (implies (and (not e) (not ae) (no-calls :list xs sigs nil) (em-ok em env fr) (decl-ok locs2 fr)
                    (no-prim-defs defs) (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st))
                    (st-ok st o s) (obj-is o s fr heap))
               (mv-let (stt fr2 h2) (sx-list ss fr heap)
                 (and (equal stt :normal) (equal h2 heap) (svs-ok cs ts vs fr2 heap)))))))

(defthm g-unop-sem-sv
  (implies (and (not (car (g-unop op c ty))) (not (car (a-prim op vs)))
                (not (car (sv c fr heap))) (equal (mv-nth 1 (sv c fr heap)) (car vs)) (scalar-ok ty (car vs)))
           (and (not (car (sv (mv-nth 1 (g-unop op c ty)) fr heap)))
                (equal (mv-nth 1 (sv (mv-nth 1 (g-unop op c ty)) fr heap)) (mv-nth 1 (a-prim op vs)))
                (scalar-ok (mv-nth 2 (g-unop op c ty)) (mv-nth 1 (a-prim op vs)))))
  :hints (("Goal" :expand ((sv (list :neg c) fr heap) (sv (list :not c) fr heap) (sv (list :max '(:int 0) c) fr heap)
                           (sv '(:int 0) fr heap)
                           (sv (list :le c '(:int 0)) fr heap) (sv (list :ge c '(:int 0)) fr heap)))))

(defthm g-binop-sem-sv
  (implies (and (not (car (g-binop op a ta b tb))) (not (car (a-prim op vs)))
                (not (car (sv a fr heap))) (equal (mv-nth 1 (sv a fr heap)) (car vs)) (scalar-ok ta (car vs))
                (not (car (sv b fr heap))) (equal (mv-nth 1 (sv b fr heap)) (cadr vs)) (scalar-ok tb (cadr vs)))
           (and (not (car (sv (mv-nth 1 (g-binop op a ta b tb)) fr heap)))
                (equal (mv-nth 1 (sv (mv-nth 1 (g-binop op a ta b tb)) fr heap)) (mv-nth 1 (a-prim op vs)))
                (scalar-ok (mv-nth 2 (g-binop op a ta b tb)) (mv-nth 1 (a-prim op vs)))))
  :hints (("Goal" :expand ((sv (list :add a b) fr heap) (sv (list :mul a b) fr heap) (sv (list :eq a b) fr heap)
                           (sv (list :lt a b) fr heap)))))

(defthm svs-ok-cons
  (implies (consp cs)
           (equal (svs-ok cs ts vs fr heap)
                  (and (consp vs) (not (car (sv (car cs) fr heap))) (equal (mv-nth 1 (sv (car cs) fr heap)) (car vs))
                       (scalar-ok (car ts) (car vs)) (svs-ok (cdr cs) (cdr ts) (cdr vs) fr heap)))))

; g-sexpr's primitive case, as its cond picks it
(defun gs-primp (x sigs st)
  (and (consp x) (true-listp x) (not (g-mvnth x)) (not (g-st-free x st)) (not (g-role (car x) st))
       (not (member-eq (car x) '(quote if implies the-check))) (not (consp (car x)))
       (not (consp (lkp (car x) sigs)))))

(defthm g-sexpr-prim
  (implies (gs-primp x sigs st)
           (equal (g-sexpr x em cnt locs sigs fnames st)
                  (mv-let (e s cs ts cnt locs) (g-sargs (cdr x) em cnt locs sigs fnames st)
                    (cond (e (mv e nil nil nil cnt locs))
                          ((= (len cs) 1) (mv-let (e c ty) (g-unop (car x) (car cs) (car ts)) (mv e s c ty cnt locs)))
                          ((= (len cs) 2) (mv-let (e c ty) (g-binop (car x) (car cs) (car ts) (cadr cs) (cadr ts))
                                            (mv e s c ty cnt locs)))
                          (t (mv :unknown nil nil nil cnt locs))))))
  :hints (("Goal" :in-theory (disable g-sargs g-st-free g-mvnth g-role) :expand ((g-sexpr x em cnt locs sigs fnames st)))))

(defthm a-sx-prim
  (implies (and (gs-primp x sigs st) (no-prim-defs defs))
           (equal (a-sx x env s st defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e vs) (a-sx-list (cdr x) env s st defs (1- n))
                      (if e (mv e nil) (a-prim (car x) vs))))))
  :hints (("Goal" :in-theory (disable a-sx-list g-st-free g-mvnth g-role a-prim) :expand ((a-sx x env s st defs n)))))

(defthm no-calls-prim
  (implies (gs-primp x sigs st) (equal (no-calls :term x sigs cs) (no-calls :list (cdr x) sigs cs)))
  :hints (("Goal" :expand ((no-calls :term x sigs cs)))))

(defthm svs-ok-len (implies (svs-ok cs ts vs fr heap) (equal (len vs) (len cs))) :rule-classes nil)

(defthm gs-prim
  (implies (and (gs-primp x sigs st) (gsa-sem (cdr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable gs-primp g-sexpr g-sargs a-sx a-sx-list no-calls g-unop g-binop a-prim sv scalar-ok)
           :use ((:instance svs-ok-len (cs (mv-nth 2 (g-sargs (cdr x) em cnt locs sigs fnames st)))
                            (ts (mv-nth 3 (g-sargs (cdr x) em cnt locs sigs fnames st)))
                            (vs (mv-nth 1 (a-sx-list (cdr x) env s st defs (1- n))))
                            (fr (mv-nth 1 (sx-list (mv-nth 1 (g-sargs (cdr x) em cnt locs sigs fnames st)) fr heap))))))))

; ---- the names g-sexpr uses, as gen-names' gs-ok has them for g-expr:
; its statements assign only new temporaries, and its code reads em's
; variables, its temporaries and names of fnames (the objects, the dummies'
; names, among them). Taken here as hypotheses of the glue cases; their
; own induction is to come.

(defun svs-names (cs) (if (atom cs) nil (append (sv-names (car cs)) (svs-names (cdr cs)))))

(defun sn-ok (x em cnt locs sigs fnames st)
  (mv-let (e ss c ty cnt2 locs2) (g-sexpr x em cnt locs sigs fnames st)
    (declare (ignore ty cnt2))
    (implies (not e)
             (and (subsetp-equal locs locs2)
                  (subsetp-equal (asg :list ss) (strip-cars locs2))
                  (not (intersectp-equal (asg :list ss) (append fnames (em-names em) (strip-cars locs))))
                  (subsetp-equal (sv-names c) (append fnames (em-names em) (strip-cars locs2)))))))

(defun sna-ok (xs em cnt locs sigs fnames st)
  (mv-let (e ss cs ts cnt2 locs2) (g-sargs xs em cnt locs sigs fnames st)
    (declare (ignore ts cnt2))
    (implies (not e)
             (and (subsetp-equal locs locs2)
                  (subsetp-equal (asg :list ss) (strip-cars locs2))
                  (not (intersectp-equal (asg :list ss) (append fnames (em-names em) (strip-cars locs))))
                  (subsetp-equal (svs-names cs) (append fnames (em-names em) (strip-cars locs2)))))))

; the facts used by backchaining (gen-proof2's ge-sem-use), so a glue
; case's proof does not split on each part's hypotheses
(defmacro gsx (k) `(mv-nth ,k (g-sexpr x em cnt locs sigs fnames st)))
(defmacro gsl (k) `(mv-nth ,k (g-sargs xs em cnt locs sigs fnames st)))

(defthm gs-sem-use
  (implies (and (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o)
                (not (gsx 0)) (not (car (a-sx x env s st defs n))) (no-calls :term x sigs nil) (em-ok em env fr)
                (decl-ok (gsx 5) fr) (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap))
           (and (equal (car (sx-list (gsx 1) fr heap)) :normal)
                (equal (mv-nth 2 (sx-list (gsx 1) fr heap)) heap)
                (not (car (sv (gsx 2) (mv-nth 1 (sx-list (gsx 1) fr heap)) heap)))
                (equal (mv-nth 1 (sv (gsx 2) (mv-nth 1 (sx-list (gsx 1) fr heap)) heap)) (mv-nth 1 (a-sx x env s st defs n)))
                (scalar-ok (gsx 3) (mv-nth 1 (a-sx x env s st defs n)))
                (implies (equal (gsx 3) :logical) (booleanp (mv-nth 1 (a-sx x env s st defs n))))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (gs-sem) (g-sexpr a-sx sx-list sv no-calls em-ok decl-ok scalar-ok st-ok obj-is)))))

(defthm gsa-sem-use
  (implies (and (gsa-sem xs em cnt locs sigs fnames st env s defs n fr heap o)
                (not (gsl 0)) (not (car (a-sx-list xs env s st defs n))) (no-calls :list xs sigs nil) (em-ok em env fr)
                (decl-ok (gsl 5) fr) (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap))
           (and (equal (car (sx-list (gsl 1) fr heap)) :normal)
                (equal (mv-nth 2 (sx-list (gsl 1) fr heap)) heap)
                (svs-ok (gsl 2) (gsl 3) (mv-nth 1 (a-sx-list xs env s st defs n)) (mv-nth 1 (sx-list (gsl 1) fr heap)) heap)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (gsa-sem) (g-sargs a-sx-list sx-list svs-ok no-calls em-ok decl-ok st-ok obj-is)))))

(defthm sn-ok-use
  (implies (and (sn-ok x em cnt locs sigs fnames st) (not (gsx 0)))
           (and (subsetp-equal locs (gsx 5))
                (subsetp-equal (asg :list (gsx 1)) (strip-cars (gsx 5)))
                (not (intersectp-equal (asg :list (gsx 1)) fnames))
                (not (intersectp-equal (asg :list (gsx 1)) (em-names em)))
                (not (intersectp-equal (asg :list (gsx 1)) (strip-cars locs)))
                (subsetp-equal (sv-names (gsx 2)) (append fnames (em-names em) (strip-cars (gsx 5))))))
  :hints (("Goal" :in-theory (disable g-sexpr g-sargs))))

(defthm sna-ok-use
  (implies (and (sna-ok xs em cnt locs sigs fnames st) (not (gsl 0)))
           (and (subsetp-equal locs (gsl 5))
                (subsetp-equal (asg :list (gsl 1)) (strip-cars (gsl 5)))
                (not (intersectp-equal (asg :list (gsl 1)) fnames))
                (not (intersectp-equal (asg :list (gsl 1)) (em-names em)))
                (not (intersectp-equal (asg :list (gsl 1)) (strip-cars locs)))
                (subsetp-equal (svs-names (gsl 2)) (append fnames (em-names em) (strip-cars (gsl 5))))))
  :hints (("Goal" :in-theory (disable g-sexpr g-sargs))))

(in-theory (disable gs-sem gsa-sem sn-ok sna-ok))

(defthm gsa-nil
  (implies (atom xs) (gsa-sem xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :in-theory (enable gsa-sem) :expand ((g-sargs xs em cnt locs sigs fnames st) (sx-list nil fr heap)))))

(defmacro sa1 (k) `(mv-nth ,k (g-sexpr (car xs) em cnt locs sigs fnames st)))
(defmacro sa2 (k) `(mv-nth ,k (g-sargs (cdr xs) em (sa1 4) (sa1 5) sigs fnames st)))

(defthm gsa-cons
  (implies (and (consp xs)
                (gs-sem (car xs) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gsa-sem (cdr xs) em (sa1 4) (sa1 5) sigs fnames st env s defs (1- n)
                         (mv-nth 1 (sx-list (sa1 1) fr heap)) heap o)
                (sn-ok (car xs) em cnt locs sigs fnames st)
                (sna-ok (cdr xs) em (sa1 4) (sa1 5) sigs fnames st))
           (gsa-sem xs em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t
           :expand ((gsa-sem xs em cnt locs sigs fnames st env s defs n fr heap o)
                    (g-sargs xs em cnt locs sigs fnames st) (a-sx-list xs env s st defs n))
           :in-theory (disable g-sexpr g-sargs a-sx a-sx-list no-calls sv sv-agree sx-list-agree sx-list
                               decl-ok-subset disjoint-via-subset obj-is st-ok scalar-ok em-ok decl-ok g-role g-mvnth)
           :use ((:instance sv-agree (e (sa1 2)) (fr (mv-nth 1 (sx-list (sa1 1) fr heap)))
                            (fr2 (mv-nth 1 (sx-list (sa2 1) (mv-nth 1 (sx-list (sa1 1) fr heap)) heap))))
                 (:instance sx-list-agree (ns (sv-names (sa1 2))) (s (sa2 1)) (fr (mv-nth 1 (sx-list (sa1 1) fr heap))))
                 (:instance decl-ok-subset (a (sa1 5)) (b (sa2 5)))
                 (:instance disjoint-via-subset (a (sv-names (sa1 2))) (b fnames)
                            (c (append (em-names em) (strip-cars (sa1 5)))) (d (asg :list (sa2 1))))))))

; ---- if: g-if's temporary gets the branch's value (gen-proof2's if-glue on sx)

(defthm sv-var-put
  (implies (scalar-ok ty v) (equal (sv (list :var k) (put k (cons ty v) fr) heap) (mv nil v)))
  :hints (("Goal" :expand ((sv (list :var k) (put k (cons ty v) fr) heap)))))

(defthm sx-assign-run
  (implies (and (not (car (sv ca fr heap))) (consp (dty tmp fr)) (scalar-ok (car (dty tmp fr)) (mv-nth 1 (sv ca fr heap))))
           (equal (sx (list :assign (list :var tmp) ca) fr heap)
                  (mv :normal (put tmp (cons (car (dty tmp fr)) (mv-nth 1 (sv ca fr heap))) fr) heap)))
  :hints (("Goal" :in-theory (e/d (dty) (sv)) :expand ((sx (list :assign (list :var tmp) ca) fr heap)))))

(defthm sx-if-stmt
  (implies (and (not (car (sv c fr heap))) (booleanp (mv-nth 1 (sv c fr heap))))
           (equal (sx (list :if c a b) fr heap)
                  (if (mv-nth 1 (sv c fr heap)) (sx-list a fr heap) (sx-list b fr heap))))
  :hints (("Goal" :expand ((sx (list :if c a b) fr heap)) :in-theory (disable sx-list sv))))

(defthm sx-list-one
  (equal (sx-list (list a) fr heap) (mv-let (st fr2 h2) (sx a fr heap) (mv st fr2 h2)))
  :hints (("Goal" :expand ((sx-list (list a) fr heap) (:free (fr heap) (sx-list nil fr heap))))))

(defthm sif-glue
  (let ((fr1 (mv-nth 1 (sx-list sc fr heap))))
    (implies (and (equal (car (sx-list sc fr heap)) :normal) (equal (mv-nth 2 (sx-list sc fr heap)) heap)
                  (not (car (sv cc fr1 heap))) (equal (mv-nth 1 (sv cc fr1 heap)) c) (booleanp c)
                  (equal (dty tmp fr) (list ta))
                  (if c (and (equal (car (sx-list sa fr1 heap)) :normal) (equal (mv-nth 2 (sx-list sa fr1 heap)) heap)
                             (not (car (sv ca (mv-nth 1 (sx-list sa fr1 heap)) heap)))
                             (equal (mv-nth 1 (sv ca (mv-nth 1 (sx-list sa fr1 heap)) heap)) v) (scalar-ok ta v))
                    (and (equal (car (sx-list sb fr1 heap)) :normal) (equal (mv-nth 2 (sx-list sb fr1 heap)) heap)
                         (not (car (sv cb (mv-nth 1 (sx-list sb fr1 heap)) heap)))
                         (equal (mv-nth 1 (sv cb (mv-nth 1 (sx-list sb fr1 heap)) heap)) v) (scalar-ok ta v))))
             (and (equal (car (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) :normal)
                  (equal (mv-nth 2 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)
                  (not (car (sv (list :var tmp) (mv-nth 1 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)))
                  (equal (mv-nth 1 (sv (list :var tmp) (mv-nth 1 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap))
                         v))))
  :hints (("Goal" :do-not-induct t :in-theory (disable sx sv sx-list dty))))

(defmacro j1 (k) `(mv-nth ,k (g-sexpr (cadr x) em cnt locs sigs fnames st)))
(defmacro j2 (k) `(mv-nth ,k (g-sexpr (caddr x) em (j1 4) (j1 5) sigs fnames st)))
(defmacro j3 (k) `(mv-nth ,k (g-sexpr (cadddr x) em (j2 4) (j2 5) sigs fnames st)))

; g-sexpr's if, as its cond picks it
(defun gs-ifp (x st)
  (and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4) (not (g-st-free x st)) (not (g-role 'if st))))

(defthm g-sexpr-if
  (implies (gs-ifp x st)
           (equal (g-sexpr x em cnt locs sigs fnames st)
                  (if (j1 0) (mv (j1 0) nil nil nil (j1 4) (j1 5))
                    (if (j2 0) (mv (j2 0) nil nil nil (j2 4) (j2 5))
                      (if (j3 0) (mv (j3 0) nil nil nil (j3 4) (j3 5))
                        (g-if (j1 1) (j1 2) (j1 3) (j2 1) (j2 2) (j2 3) (j3 1) (j3 2) (j3 3) (j3 4) (j3 5)
                              (append fnames (em-names em))))))))
  :hints (("Goal" :in-theory (disable g-st-free g-if g-mvnth g-expr g-sargs g-scall-args g-svals g-unop g-binop
                                      g-st-ident g-role g-obj g-comp em-names)
           :expand ((g-sexpr x em cnt locs sigs fnames st)))
          (and stable-under-simplificationp '(:in-theory (e/d (g-mvnth) (g-st-free g-if g-expr g-sargs g-scall-args g-svals
                                                                      g-unop g-binop g-st-ident g-role g-obj g-comp em-names))))))

(defthm a-sx-if
  (implies (gs-ifp x st)
           (equal (a-sx x env s st defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e c) (a-sx (cadr x) env s st defs (1- n))
                      (cond (e (mv e nil))
                            (c (a-sx (caddr x) env s st defs (1- n)))
                            (t (a-sx (cadddr x) env s st defs (1- n))))))))
  :hints (("Goal" :in-theory (disable g-st-free g-role a-ev a-sx-list) :expand ((a-sx x env s st defs n)))))

(defthm no-calls-if
  (implies (and (gs-ifp x st) (no-calls :term x sigs cs))
           (and (no-calls :term (cadr x) sigs cs) (no-calls :term (caddr x) sigs cs)
                (no-calls :term (cadddr x) sigs cs)))
  :hints (("Goal" :in-theory (disable g-st-free) :expand ((no-calls :term x sigs cs) (no-calls :list (cdr x) sigs cs)
                           (no-calls :list (cddr x) sigs cs) (no-calls :list (cdddr x) sigs cs)
                           (no-calls :list (cddddr x) sigs cs)))))

(defthm g-sexpr-if-out
  (implies (and (gs-ifp x st) (not (gsx 0)))
           (let ((tmp (g-tmp 't (1+ (nfix (j3 4))))))
             (and (not (j1 0)) (not (j2 0)) (not (j3 0)) (equal (j1 3) :logical) (equal (j3 3) (j2 3))
                  (equal (gsx 1) (if-stmts (j1 1) (j1 2) (j2 1) (j2 2) (j3 1) (j3 2) tmp))
                  (equal (gsx 2) (list :var tmp))
                  (equal (gsx 3) (j2 3))
                  (equal (gsx 5) (cons (cons tmp (j2 3)) (true-list-fix (j3 5)))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable g-if g-sexpr gs-ifp if-stmts g-tmp)
           :use ((:instance g-if-out (sc (j1 1)) (cc (j1 2)) (tc (j1 3)) (sa (j2 1)) (ca (j2 2)) (ta (j2 3))
                            (sb (j3 1)) (cb (j3 2)) (tb (j3 3)) (cnt (j3 4)) (locs (j3 5)) (used (append fnames (em-names em))))
                 (:instance g-if-types (sc (j1 1)) (cc (j1 2)) (tc (j1 3)) (sa (j2 1)) (ca (j2 2)) (ta (j2 3))
                            (sb (j3 1)) (cb (j3 2)) (tb (j3 3)) (cnt (j3 4)) (locs (j3 5)) (used (append fnames (em-names em))))))))

; sif-glue split by the test's value, the branch's type read off the frame
; (no free variable), so the if case uses them by rewriting, not :use
(defthm sif-then
  (let ((fr1 (mv-nth 1 (sx-list sc fr heap))))
    (implies (and (equal (car (sx-list sc fr heap)) :normal) (equal (mv-nth 2 (sx-list sc fr heap)) heap)
                  (not (car (sv cc fr1 heap))) (mv-nth 1 (sv cc fr1 heap)) (booleanp (mv-nth 1 (sv cc fr1 heap)))
                  (consp (dty tmp fr))
                  (equal (car (sx-list sa fr1 heap)) :normal) (equal (mv-nth 2 (sx-list sa fr1 heap)) heap)
                  (not (car (sv ca (mv-nth 1 (sx-list sa fr1 heap)) heap)))
                  (scalar-ok (car (dty tmp fr)) (mv-nth 1 (sv ca (mv-nth 1 (sx-list sa fr1 heap)) heap))))
             (and (equal (car (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) :normal)
                  (equal (mv-nth 2 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)
                  (not (car (sv (list :var tmp) (mv-nth 1 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)))
                  (equal (mv-nth 1 (sv (list :var tmp) (mv-nth 1 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap))
                         (mv-nth 1 (sv ca (mv-nth 1 (sx-list sa fr1 heap)) heap))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable sx sv sx-list sif-glue if-stmts)
           :use (:instance sif-glue (ta (car (dty tmp fr))) (c t)
                           (v (mv-nth 1 (sv ca (mv-nth 1 (sx-list sa (mv-nth 1 (sx-list sc fr heap)) heap)) heap)))))))

(defthm sif-else
  (let ((fr1 (mv-nth 1 (sx-list sc fr heap))))
    (implies (and (equal (car (sx-list sc fr heap)) :normal) (equal (mv-nth 2 (sx-list sc fr heap)) heap)
                  (not (car (sv cc fr1 heap))) (not (mv-nth 1 (sv cc fr1 heap)))
                  (consp (dty tmp fr))
                  (equal (car (sx-list sb fr1 heap)) :normal) (equal (mv-nth 2 (sx-list sb fr1 heap)) heap)
                  (not (car (sv cb (mv-nth 1 (sx-list sb fr1 heap)) heap)))
                  (scalar-ok (car (dty tmp fr)) (mv-nth 1 (sv cb (mv-nth 1 (sx-list sb fr1 heap)) heap))))
             (and (equal (car (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) :normal)
                  (equal (mv-nth 2 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)
                  (not (car (sv (list :var tmp) (mv-nth 1 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap)))
                  (equal (mv-nth 1 (sv (list :var tmp) (mv-nth 1 (sx-list (if-stmts sc cc sa ca sb cb tmp) fr heap)) heap))
                         (mv-nth 1 (sv cb (mv-nth 1 (sx-list sb fr1 heap)) heap))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable sx sv sx-list sif-glue if-stmts)
           :use (:instance sif-glue (ta (car (dty tmp fr))) (c nil)
                           (v (mv-nth 1 (sv cb (mv-nth 1 (sx-list sb (mv-nth 1 (sx-list sc fr heap)) heap)) heap)))))))

(in-theory (disable sif-glue))

; the else branch's value has the then branch's type (g-if wants them equal);
; stated on (j2 3) so the if case finds it by rewriting
(defthm gs-sem-else-type
  (implies (and (gs-ifp x st) (not (gsx 0))
                (gs-sem (cadddr x) em (j2 4) (j2 5) sigs fnames st env s defs n fr heap o)
                (not (car (a-sx (cadddr x) env s st defs n))) (no-calls :term (cadddr x) sigs nil) (em-ok em env fr)
                (decl-ok (j3 5) fr) (no-prim-defs defs) (not (consp (lkp 'mv-nth defs)))
                (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (st-ok st o s) (obj-is o s fr heap))
           (scalar-ok (j2 3) (mv-nth 1 (a-sx (cadddr x) env s st defs n))))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)
           :use ((:instance gs-sem-use (x (cadddr x)) (cnt (j2 4)) (locs (j2 5))) g-sexpr-if-out))))

(defmacro fr1 () '(mv-nth 1 (sx-list (j1 1) fr heap)))

; the if case: its test's and branches' gs-sem and names facts give its own
(defthm gsx-if
  (implies (and (gs-ifp x st)
                (gs-sem (cadr x) em cnt locs sigs fnames st env s defs (1- n) fr heap o)
                (gs-sem (caddr x) em (j1 4) (j1 5) sigs fnames st env s defs (1- n) (fr1) heap o)
                (gs-sem (cadddr x) em (j2 4) (j2 5) sigs fnames st env s defs (1- n) (fr1) heap o)
                (sn-ok (cadr x) em cnt locs sigs fnames st)
                (sn-ok (caddr x) em (j1 4) (j1 5) sigs fnames st)
                (sn-ok (cadddr x) em (j2 4) (j2 5) sigs fnames st))
           (gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
  :hints (("Goal" :do-not-induct t :expand ((gs-sem x em cnt locs sigs fnames st env s defs n fr heap o))
           :cases ((mv-nth 1 (a-sx (cadr x) env s st defs (1- n))))
           :in-theory (disable g-sexpr a-sx sx-list sx sv no-calls em-ok scalar-ok st-ok obj-is gs-ifp
                               g-sexpr-if if-stmts g-tmp nfix dty decl-ok-subset sif-glue sv-is-fv fv
                               sx-list-is-fx-list fx-list)
           :do-not (quote (eliminate-destructors generalize))
           :use ((:instance decl-ok-subset (a (j1 5)) (b (j2 5)))
                 (:instance decl-ok-subset (a (j2 5)) (b (j3 5)))))))
