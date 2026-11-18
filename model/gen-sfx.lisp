; gen-sfx: sv and sx plus calls of value functions given the stobj (GEN.md
; "What remains" 4b, for hpg-next-tail/hpg-seq-op). svf is sv plus
; `(:fcall f ((:var ob) . cs))`, answered by an oracle, s-fn-val, on f, the
; heap entry of ob's object and the codes' values (svlf): (mv err v). sxf is
; sx on svf. The other events are gen-stx's, copied by clone.py with sv/sx
; renamed. Under p-sforc -- "the oracle is what the procedures answer":
; wherever svf answers no error on an :fcall, f-ev at any fuel past b + its
; size answers the same -- f-ev is svf and f-ex-list is sxf-list wherever
; they answer no error (svf-ok-is-f-ev, sxf-ok-is-f-ex-list), as gen-stcall's
; sxc-ok-is-f-ex-list is for CALL. A new evaluator, not a case added to sv:
; sv's theorems would otherwise need p-sforc.

(in-package "ACL2")

(include-book "gen-stok")

(encapsulate (((s-fn-val * * *) => (mv * *)))
  (local (defun s-fn-val (name s ks) (declare (ignore name s ks)) (mv :unknown nil))))

(mutual-recursion
 (defun svf (e fr heap)
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
    (:elem (mv-let (err i) (svf (kadddr e) fr heap)
             (if err (mv err nil)
               (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
                 (if err (mv err nil) (read-elem v i))))))
    (:neg (mv-let (err a) (svf (kadr e) fr heap) (if err (mv err nil) (arith :sub 0 a))))
    (:not (mv-let (err a) (svf (kadr e) fr heap)
            (cond (err (mv err nil)) ((booleanp a) (mv nil (not a))) (t (mv :type nil)))))
    ((:add :sub :mul :eq :lt :le :ge :max)
     (mv-let (err a) (svf (kadr e) fr heap)
       (if err (mv err nil)
         (mv-let (err b) (svf (kaddr e) fr heap)
           (if err (mv err nil) (binop (kar e) a b))))))
    (:fcall (let ((a (kaddr e)))
              (mv-let (err key intent) (obj-of (kadr (kar a)) fr)
                (declare (ignore intent))
                (cond ((not (eq (kar (kar a)) :var)) (mv :syntax nil))
                      (err (mv err nil))
                      (t (mv-let (err ks) (svlf (kdr a) fr heap)
                           (if err (mv err nil)
                             (mv-let (err v) (s-fn-val (kadr e) (cdr (lkp key heap)) ks) (mv err v)))))))))
    (otherwise (mv :syntax nil))))
 ; the codes' values
 (defun svlf (cs fr heap)
  (declare (xargs :guard t :measure (acl2-count cs)))
  (if (atom cs) (mv nil nil)
    (mv-let (err v) (svf (car cs) fr heap)
      (if err (mv err nil)
        (mv-let (err vs) (svlf (cdr cs) fr heap)
          (if err (mv err nil) (mv nil (cons v vs)))))))))

(in-theory (disable svf svlf))

;; on cs-expr (no :fcall), svf is sv
(defthm svf-is-sv
  (implies (cs-expr e) (equal (svf e fr heap) (sv e fr heap)))
  :hints (("Goal" :induct (sv e fr heap) :in-theory (e/d ((:induction sv)) (binop arith read-elem comp-of obj-of))
           :expand ((svf e fr heap) (sv e fr heap) (cs-expr e)))))

(defthm sv-is-fv-f
  (implies (cf-expr e) (equal (svf e fr heap) (fv e fr))))

(mutual-recursion
 (defun sxf (x frame heap)
   (declare (xargs :guard t :measure (acl2-count x)))
   (case (kar x)
     (:assign
      (mv-let (err v) (svf (kaddr x) frame heap)
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
                                  (t (mv-let (err i) (svf (kadddr d) frame heap)
                                       (cond (err (mv (errst err) frame heap))
                                             ((not (and (farrayp (cdr p)) (integerp i))) (mv (errst :type) frame heap))
                                             ((not (and (<= 0 i) (< i (len (cddr p))))) (mv (errst :bounds) frame heap))
                                             (t (mv :normal frame
                                                    (put key (put (kaddr d) (cons :array (update-nth i v (cddr p))) comps)
                                                         heap))))))))))))
              (otherwise (mv (errst :syntax) frame heap)))))))
     (:if (mv-let (err c) (svf (kadr x) frame heap)
            (cond (err (mv (errst err) frame heap))
                  ((not (booleanp c)) (mv (errst :type) frame heap))
                  (c (sxf-list (kaddr x) frame heap))
                  (t (sxf-list (kadddr x) frame heap)))))
     (:select (mv-let (err k) (svf (kadr x) frame heap)
                (cond (err (mv (errst err) frame heap))
                      ((not (integerp k)) (mv (errst :type) frame heap))
                      (t (let ((arm (lkp k (kaddr x))))
                           (sxf-list (if arm (kadr arm) (kadddr x)) frame heap))))))
     ((:cycle :exit :return) (mv (kar x) frame heap))
     (otherwise (mv (errst :syntax) frame heap))))
 (defun sxf-list (ss frame heap)
   (declare (xargs :guard t :measure (acl2-count ss)))
   (if (atom ss) (mv :normal frame heap)
     (mv-let (st fr2 h2) (sxf (car ss) frame heap)
       (if (eq st :normal) (sxf-list (cdr ss) fr2 h2) (mv st fr2 h2))))))

(in-theory (disable sxf sxf-list))

(defun sx-ind-f (flag s fr heap k)
  (declare (xargs :measure (acl2-count s) :verify-guards nil))
  (if (or (zp k) (atom s)) (list fr heap k)
    (if (eq flag :stmt)
        (mv-let (err v) (svf (kadr s) fr heap)
          (declare (ignore err))
          (list (sx-ind-f :list (kaddr s) fr heap (1- k))
                (sx-ind-f :list (kadddr s) fr heap (1- k))
                (sx-ind-f :list (kadr (lkp v (kaddr s))) fr heap (1- k))))
      (mv-let (st fr2 h2) (sxf (car s) fr heap)
        (declare (ignore st))
        (list (sx-ind-f :stmt (car s) fr heap (1- k))
              (sx-ind-f :list (cdr s) fr2 h2 (1- k)))))))

;; on cs-stmts, sxf is sx
(defthm sxf-assign-sx
  (implies (and (equal (kar s) :assign) (cs-stmt s)) (equal (sxf s fr heap) (sx s fr heap)))
  :hints (("Goal" :expand ((sxf s fr heap) (sx s fr heap) (cs-stmt s)) :in-theory (disable svf sv obj-of comp-of))))

(defthm sxf-sx-ctl
  (implies (and (member-eq (kar s) '(:if :select)) (cs-expr (kadr s)))
           (equal (sxf s fr heap)
                  (mv-let (err v) (sv (kadr s) fr heap)
                    (cond (err (mv (errst err) fr heap))
                          ((eq (kar s) :if)
                           (cond ((not (booleanp v)) (mv (errst :type) fr heap))
                                 (v (sxf-list (kaddr s) fr heap))
                                 (t (sxf-list (kadddr s) fr heap))))
                          ((not (integerp v)) (mv (errst :type) fr heap))
                          (t (sxf-list (if (lkp v (kaddr s)) (kadr (lkp v (kaddr s))) (kadddr s)) fr heap))))))
  :hints (("Goal" :in-theory (disable sv svf) :expand ((sxf s fr heap)))))

(defthm sx-ctl
  (implies (member-eq (kar s) '(:if :select))
           (equal (sx s fr heap)
                  (mv-let (err v) (sv (kadr s) fr heap)
                    (cond (err (mv (errst err) fr heap))
                          ((eq (kar s) :if)
                           (cond ((not (booleanp v)) (mv (errst :type) fr heap))
                                 (v (sx-list (kaddr s) fr heap))
                                 (t (sx-list (kadddr s) fr heap))))
                          ((not (integerp v)) (mv (errst :type) fr heap))
                          (t (sx-list (if (lkp v (kaddr s)) (kadr (lkp v (kaddr s))) (kadddr s)) fr heap))))))
  :hints (("Goal" :in-theory (disable sv) :expand ((sx s fr heap)))))

(defthm sxf-sx-jump
  (implies (member-eq (kar s) '(:cycle :exit :return))
           (and (equal (sxf s fr heap) (mv (kar s) fr heap)) (equal (sx s fr heap) (mv (kar s) fr heap))))
  :hints (("Goal" :expand ((sxf s fr heap) (sx s fr heap)))))

(defthm sxf-sx-list-cons
  (implies (consp ss)
           (and (equal (sxf-list ss fr heap)
                       (mv-let (st fr2 h2) (sxf (car ss) fr heap)
                         (if (eq st :normal) (sxf-list (cdr ss) fr2 h2) (mv st fr2 h2))))
                (equal (sx-list ss fr heap)
                       (mv-let (st fr2 h2) (sx (car ss) fr heap)
                         (if (eq st :normal) (sx-list (cdr ss) fr2 h2) (mv st fr2 h2))))))
  :hints (("Goal" :expand ((sxf-list ss fr heap) (sx-list ss fr heap)))))

(defthm sxf-sx-list-atom
  (implies (atom ss) (and (equal (sxf-list ss fr heap) (mv :normal fr heap)) (equal (sx-list ss fr heap) (mv :normal fr heap))))
  :hints (("Goal" :expand ((sxf-list ss fr heap) (sx-list ss fr heap)))))

(defthm cs-stmt-parts
  (implies (cs-stmt s)
           (and (member-eq (kar s) '(:assign :if :select :return :cycle :exit))
                (implies (member-eq (kar s) '(:if :select)) (cs-expr (kadr s)))
                (implies (eq (kar s) :if) (and (cs-stmts (kaddr s)) (cs-stmts (kadddr s))))
                (implies (eq (kar s) :select) (and (cs-arms (kaddr s)) (cs-stmts (kadddr s))))))
  :hints (("Goal" :expand ((cs-stmt s)))))

(defthm cs-stmts-parts
  (implies (and (cs-stmts ss) (consp ss)) (and (cs-stmt (car ss)) (cs-stmts (cdr ss))))
  :hints (("Goal" :expand ((cs-stmts ss)))))

(defthm sxf-is-sx-flag
  (implies (and (integerp k) (< (acl2-count s) k))
           (if (eq flag :stmt)
               (implies (cs-stmt s) (equal (sxf s fr heap) (sx s fr heap)))
             (implies (cs-stmts s) (equal (sxf-list s fr heap) (sx-list s fr heap)))))
  :rule-classes nil
  :hints (("Goal" :induct (sx-ind-f flag s fr heap k) :do-not-induct t
           :in-theory (disable sv svf sx sxf sx-list sxf-list cs-stmt cs-stmts cs-arms svf-is-sv))
          (and stable-under-simplificationp
               '(:in-theory (disable sv sx sxf sx-list sxf-list cs-stmts cs-arms) :expand ((cs-stmt s))
                 :cases ((equal (kar s) :assign) (equal (kar s) :if) (equal (kar s) :select)
                         (member-eq (kar s) '(:cycle :exit :return)))))))

(defthm sxf-list-is-sx-list
  (implies (cs-stmts ss) (equal (sxf-list ss fr heap) (sx-list ss fr heap)))
  :hints (("Goal" :use (:instance sxf-is-sx-flag (flag :list) (s ss) (k (1+ (acl2-count ss)))))))

(defthm sx-list-is-fx-list-f
  (implies (cf-stmts ss) (equal (sxf-list ss fr heap) (+h (fx-list ss fr) heap))))

; ---- the oracle is what the procedures answer

(defun-sk p-sforc (procs b)
  (forall (x fr heap fuel)
    (implies (and (eq (kar x) :fcall) (not (mv-nth 0 (svf x fr heap)))
                  (integerp fuel) (< (+ b (acl2-count x)) fuel))
             (equal (f-ev x fr heap procs fuel) (svf x fr heap)))))

(in-theory (disable p-sforc))

; openers, one per kind of node, so the induction below splits by kind only
(defthm f-ev-svf-un
  (implies (and (posp k) (member-eq (kar e) '(:neg :not)))
           (and (equal (f-ev e fr heap procs k)
                       (mv-let (err a) (f-ev (kadr e) fr heap procs (1- k))
                         (cond (err (mv err nil))
                               ((eq (kar e) :neg) (arith :sub 0 a))
                               ((booleanp a) (mv nil (not a)))
                               (t (mv :type nil)))))
                (equal (svf e fr heap)
                       (mv-let (err a) (svf (kadr e) fr heap)
                         (cond (err (mv err nil))
                               ((eq (kar e) :neg) (arith :sub 0 a))
                               ((booleanp a) (mv nil (not a)))
                               (t (mv :type nil)))))))
  :hints (("Goal" :in-theory (union-theories (quote (member-equal eql posp)) (theory (quote minimal-theory))) :expand ((f-ev e fr heap procs k) (svf e fr heap)))))

(defthm f-ev-svf-bin
  (implies (and (posp k) (member-eq (kar e) '(:add :sub :mul :eq :lt :le :ge :max)))
           (and (equal (f-ev e fr heap procs k)
                       (mv-let (err a) (f-ev (kadr e) fr heap procs (1- k))
                         (if err (mv err nil)
                           (mv-let (err b) (f-ev (kaddr e) fr heap procs (1- k))
                             (if err (mv err nil) (binop (kar e) a b))))))
                (equal (svf e fr heap)
                       (mv-let (err a) (svf (kadr e) fr heap)
                         (if err (mv err nil)
                           (mv-let (err b) (svf (kaddr e) fr heap)
                             (if err (mv err nil) (binop (kar e) a b))))))))
  :hints (("Goal" :in-theory (union-theories (quote (member-equal eql posp)) (theory (quote minimal-theory))) :expand ((f-ev e fr heap procs k) (svf e fr heap)))))

(defthm f-ev-svf-elem
  (implies (and (posp k) (eq (kar e) :elem))
           (and (equal (f-ev e fr heap procs k)
                       (mv-let (err i) (f-ev (kadddr e) fr heap procs (1- k))
                         (if err (mv err nil)
                           (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
                             (if err (mv err nil) (read-elem v i))))))
                (equal (svf e fr heap)
                       (mv-let (err i) (svf (kadddr e) fr heap)
                         (if err (mv err nil)
                           (mv-let (err v) (comp-of (kadr e) (kaddr e) fr heap)
                             (if err (mv err nil) (read-elem v i))))))))
  :hints (("Goal" :in-theory (union-theories (quote (member-equal eql posp)) (theory (quote minimal-theory))) :expand ((f-ev e fr heap procs k) (svf e fr heap)))))

(defthm svf-other-err
  (implies (not (member-eq (kar e) '(:int :true :false :huge :var :comp :size :neg :not :add :sub :mul :eq :lt :le :ge :max
                                     :elem :fcall)))
           (equal (svf e fr heap) (mv :syntax nil)))
  :hints (("Goal" :expand ((svf e fr heap)))))

(defthm svf-fcall-bad
  (implies (and (equal (kar e) :fcall) (not (equal (kar (kar (kaddr e))) :var)))
           (equal (svf e fr heap) (mv :syntax nil)))
  :hints (("Goal" :expand ((svf e fr heap)))))

(defthm svf-leaf-f-ev
  (implies (and (member-eq (kar e) '(:int :true :false :huge :var :comp :size)) (integerp k) (< (acl2-count e) k))
           (equal (f-ev e fr heap procs k) (svf e fr heap)))
  :hints (("Goal" :in-theory (disable sv-is-f-ev svf-is-sv f-ev svf sv)
           :use (sv-is-f-ev svf-is-sv) :expand ((cs-expr e)))))

(defthm svf-fcall-f-ev
  (implies (and (p-sforc procs b) (eq (kar e) :fcall) (not (mv-nth 0 (svf e fr heap))) (integerp k) (< (+ b (acl2-count e)) k))
           (equal (f-ev e fr heap procs k) (svf e fr heap)))
  :hints (("Goal" :in-theory (disable p-sforc-necc f-ev svf) :use (:instance p-sforc-necc (x e) (fuel k)))))

(defthm svf-ok-is-f-ev
  (implies (and (p-sforc procs b) (natp b) (not (mv-nth 0 (svf e fr heap))) (integerp k) (< (+ b (acl2-count e)) k))
           (equal (f-ev e fr heap procs k) (svf e fr heap)))
  :hints (("Goal" :induct (sv-ind e k) :do-not-induct t
           :in-theory (disable p-sforc-necc binop arith read-elem comp-of obj-of f-ev svf f-invoke find-proc
                               svf-is-sv sv-is-fv-f cs-expr cf-expr fv int-lit-p))
          (and stable-under-simplificationp
               '(:cases ((member-eq (kar e) '(:int :true :false :huge :var :comp :size)) (member-eq (kar e) '(:neg :not))
                         (member-eq (kar e) '(:add :sub :mul :eq :lt :le :ge :max)) (eq (kar e) :elem) (eq (kar e) :fcall))
                 :use (svf-fcall-f-ev)))))

(defthm sxf-assign-f-ex
  (implies (and (p-sforc procs b) (natp b) (equal (kar s) :assign) (not (errstp (mv-nth 0 (sxf s fr heap))))
                (integerp k) (< (+ b (acl2-count s)) k))
           (equal (f-ex s fr heap procs k) (sxf s fr heap)))
  :hints (("Goal" :in-theory (disable f-ev f-ex-assign-obj svf obj-of comp-of)
           :expand ((f-ex s fr heap procs k) (sxf s fr heap)))))

; sxf's :if/:select and other cases, one opener each, so the flag proof never expands sxf
(defthm sxf-ctl-open
  (implies (member-eq (kar s) '(:if :select))
           (equal (sxf s fr heap)
                  (mv-let (err v) (svf (kadr s) fr heap)
                    (cond (err (mv (errst err) fr heap))
                          ((eq (kar s) :if)
                           (cond ((not (booleanp v)) (mv (errst :type) fr heap))
                                 (v (sxf-list (kaddr s) fr heap))
                                 (t (sxf-list (kadddr s) fr heap))))
                          ((not (integerp v)) (mv (errst :type) fr heap))
                          (t (sxf-list (if (lkp v (kaddr s)) (kadr (lkp v (kaddr s))) (kadddr s)) fr heap))))))
  :hints (("Goal" :in-theory (disable svf) :expand ((sxf s fr heap)))))

(defthm sxf-other-open
  (implies (not (member-eq (kar s) '(:assign :if :select :cycle :exit :return)))
           (equal (sxf s fr heap) (mv (errst :syntax) fr heap)))
  :hints (("Goal" :in-theory (disable svf) :expand ((sxf s fr heap)))))

; the statement and list claims, named, so the induction below only chains step lemmas
(defun-nx sxs-ok (s fr heap procs k)
  (implies (and (not (equal (kar s) :assign)) (not (errstp (mv-nth 0 (sxf s fr heap)))))
           (equal (f-ex s fr heap procs k) (sxf s fr heap))))

(defun-nx sxl-ok (ss fr heap procs k)
  (implies (not (errstp (mv-nth 0 (sxf-list ss fr heap))))
           (equal (f-ex-list ss fr heap procs k) (sxf-list ss fr heap))))

(defmacro sxs-thy ()
  '(disable f-ex f-ex-list f-ex-return svf sv-ok-is-f-ev sxf-list-is-sx-list sx-list-is-fx-list-f svf-is-sv
            sv-is-fv-f sxf-assign-sx sxf-sx-ctl sx-ctl cs-stmt cs-stmts cf-stmt cf-stmts sxf-list sxf))

(defthm sxs-if-step
  (implies (and (p-sforc procs b) (natp b) (integerp k) (< (+ b (acl2-count s)) k) (eq (kar s) :if)
                (sxl-ok (kaddr s) fr heap procs (1- k)) (sxl-ok (kadddr s) fr heap procs (1- k)))
           (sxs-ok s fr heap procs k))
  :hints (("Goal" :do-not-induct t :in-theory (sxs-thy))))

(defthm sxs-select-step
  (implies (and (p-sforc procs b) (natp b) (integerp k) (< (+ b (acl2-count s)) k) (eq (kar s) :select)
                (sxl-ok (kadr (lkp (mv-nth 1 (svf (kadr s) fr heap)) (kaddr s))) fr heap procs (1- k))
                (sxl-ok (kadddr s) fr heap procs (1- k)))
           (sxs-ok s fr heap procs k))
  :hints (("Goal" :do-not-induct t :in-theory (sxs-thy))))

(defthm sxs-other-step
  (implies (and (integerp k) (< 0 k) (not (member-eq (kar s) '(:if :select))))
           (sxs-ok s fr heap procs k))
  :hints (("Goal" :do-not-induct t :in-theory (sxs-thy) :cases ((member-eq (kar s) (quote (:cycle :exit :return)))))))

(defthm sxl-step
  (implies (and (p-sforc procs b) (natp b) (integerp k) (< (+ b (acl2-count ss)) k)
                (implies (consp ss)
                         (and (sxs-ok (car ss) fr heap procs (1- k))
                              (sxl-ok (cdr ss) (mv-nth 1 (sxf (car ss) fr heap)) (mv-nth 2 (sxf (car ss) fr heap))
                                      procs (1- k)))))
           (sxl-ok ss fr heap procs k))
  :hints (("Goal" :do-not-induct t :in-theory (sxs-thy)
           :cases ((and (consp ss) (equal (kar (car ss)) :assign))))))

(in-theory (disable sxs-ok sxl-ok))

(defthm sfx-count-parts
  (implies (consp s)
           (and (< (acl2-count (car s)) (acl2-count s)) (< (acl2-count (cdr s)) (acl2-count s))
                (< (acl2-count (kaddr s)) (acl2-count s)) (< (acl2-count (kadddr s)) (acl2-count s))))
  :rule-classes :linear)

(defthm sfx-count-arm
  (<= (acl2-count (kadr (lkp v arms))) (acl2-count arms))
  :rule-classes :linear)

(defthm sxf-ok-is-f-ex-flag
  (implies (and (p-sforc procs b) (natp b) (integerp k) (< (+ b (acl2-count s)) k))
           (if (eq flag :stmt) (sxs-ok s fr heap procs k) (sxl-ok s fr heap procs k)))
  :rule-classes nil
  :hints (("Goal" :induct (sx-ind-f flag s fr heap k) :do-not-induct t
           :in-theory (union-theories '((:induction sx-ind-f) sxs-if-step sxs-select-step sxs-other-step sxl-step natp zp atom
                                        eq member-equal kar-atom sfx-count-parts sfx-count-arm (:type-prescription acl2-count))
                                      (theory 'minimal-theory)))
          (and stable-under-simplificationp '(:cases ((eq (kar s) :if) (eq (kar s) :select))))))

(defthm sxf-ok-is-f-ex-list
  (implies (and (p-sforc procs b) (natp b) (not (errstp (mv-nth 0 (sxf-list ss fr heap))))
                (integerp k) (< (+ b (acl2-count ss)) k))
           (equal (f-ex-list ss fr heap procs k) (sxf-list ss fr heap)))
  :hints (("Goal" :in-theory (enable sxl-ok) :use (:instance sxf-ok-is-f-ex-flag (flag :list) (s ss)))))
