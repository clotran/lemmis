; gen-tail: the tail call, layer 3's loop (GEN.md). g-tail's statements put
; each argument's value into a fresh temporary, then its assignments copy
; the temporaries into the formals' dummies; CYCLE follows (g-ret). Here:
; the source shape the loop theorem takes (tail-only: no call of a
; translated function but self-calls in tail position), what g-tail's
; statements write and that they are fsem's call-free statements (gtc-ok),
; their run (gt-sem: each temporary holds its argument's a-ev value), and
; the assignments' run (as-run: each formal's dummy then holds it).

(in-package "ACL2")

(include-book "gen-retout")

(set-irrelevant-formals-ok t)

; ---- the source: calls of translated functions only as a tail self-call

(defun tail-only (x self sigs)
  (declare (xargs :measure (acl2-count x)))
  (cond ((and (consp x) (eq (car x) 'if) (true-listp x) (= (len x) 4))
         (and (no-calls :term (cadr x) sigs) (tail-only (caddr x) self sigs) (tail-only (cadddr x) self sigs)))
        ((and (consp x) (eq (car x) self)) (no-calls :list (cdr x) sigs))
        (t (no-calls :term x sigs))))

; a-ev of a call of a defined function
(defthm a-ev-defined-call
  (implies (and (consp x) (symbolp (car x)) (not (eq (car x) 'quote)) (not (eq (car x) 'if))
                (consp (lkp (car x) defs)))
           (equal (a-ev x env defs n)
                  (if (zp n) (mv :fuel nil)
                    (mv-let (e vs) (a-ev-list (cdr x) env defs (1- n))
                      (if e (mv e nil)
                        (a-ev (kaddr (lkp (car x) defs)) (pairlis$ (true-list-fix (kadr (lkp (car x) defs))) vs)
                              defs (1- n)))))))
  :hints (("Goal" :expand ((a-ev x env defs n)))))

; ---- the assignments: formal i's dummy from a temporary, none a formal

(defun as-ok (as vars fnames)
  (if (atom as) t
    (and (consp vars)
         (equal (car as) (list :assign (list :var (g-formal (car vars))) (list :var (kadr (kaddr (car as))))))
         (not (member-equal (kadr (kaddr (car as))) fnames))
         (as-ok (cdr as) (cdr vars) fnames))))

(defun as-srcs (as) (if (atom as) nil (cons (kadr (kaddr (car as))) (as-srcs (cdr as)))))

(defthm g-fresh-facts
  (implies (not (car (g-fresh base ty cnt locs used)))
           (and (equal (mv-nth 3 (g-fresh base ty cnt locs used))
                       (cons (cons (mv-nth 1 (g-fresh base ty cnt locs used)) ty) (true-list-fix locs)))
                (not (member-equal (mv-nth 1 (g-fresh base ty cnt locs used)) used))
                (not (member-equal (mv-nth 1 (g-fresh base ty cnt locs used)) (strip-cars locs)))
                (not (equal (mv-nth 1 (g-fresh base ty cnt locs used)) "r"))))
  :hints (("Goal" :in-theory (disable g-tmp))))

(defthm g-fresh-app
  (implies (not (car (g-fresh base ty cnt locs (append a b))))
           (and (not (member-equal (mv-nth 1 (g-fresh base ty cnt locs (append a b))) a))
                (not (member-equal (mv-nth 1 (g-fresh base ty cnt locs (append a b))) b))))
  :hints (("Goal" :in-theory (disable g-fresh-facts) :use (:instance g-fresh-facts (used (append a b))))))

(defthm cf-stmts-assign-var
  (equal (cf-stmts (cons (list :assign (list :var a) c) ss)) (and (cf-expr c) (cf-stmts ss)))
  :hints (("Goal" :expand ((cf-stmts (cons (list :assign (list :var a) c) ss))
                           (cf-stmt (list :assign (list :var a) c))))))

(defthm no-calls-list-cons
  (implies (consp xs)
           (equal (no-calls :list xs sigs) (and (no-calls :term (car xs) sigs) (no-calls :list (cdr xs) sigs))))
  :hints (("Goal" :expand ((no-calls :list xs sigs)))))

(defthm as-srcs-strip
  (implies (subsetp-equal (as-srcs as) (strip-cars l)) (subsetp-equal (as-srcs as) (strip-cars (cons p l)))))

(defmacro gtr (k) `(mv-nth ,k (g-tail (cdr vars) (cdr xs) em (gtf 2) (gtf 3) sigs fnames)))

; g-tail's step, opened once: its parts' results
(defthm g-tail-open
  (implies (and (consp vars) (consp xs) (not (car (g-tail vars xs em cnt locs sigs fnames))))
           (and (not (gt1 0)) (equal (gt1 3) :int64) (not (gtf 0)) (not (gtr 0))
                (equal (g-tail vars xs em cnt locs sigs fnames)
                       (list nil (append (gt1 1) (cons (list :assign (list :var (gtf 1)) (gt1 2)) (gtr 1)))
                             (cons (list :assign (list :var (g-formal (car vars))) (list :var (gtf 1))) (gtr 2))
                             (gtr 3) (gtr 4)))))
  :hints (("Goal" :expand ((g-tail vars xs em cnt locs sigs fnames)) :in-theory (disable g-expr g-fresh))))

(defthm gt-locs-glue
  (implies (and (subsetp-equal (asg :list s1) (strip-cars l1)) (subsetp-equal l l1)
                (subsetp-equal (cons (cons tmp ty) (true-list-fix l1)) l2)
                (subsetp-equal (asg :list ss) (strip-cars l2)) (subsetp-equal (as-srcs as) (strip-cars l2)))
           (and (subsetp-equal l l2)
                (subsetp-equal (asg :list (append s1 (cons (list :assign (list :var tmp) c) ss))) (strip-cars l2))
                (subsetp-equal (as-srcs (cons (list :assign (list :var f) (list :var tmp)) as)) (strip-cars l2))))
  :hints (("Goal" :in-theory (disable subsetp-strip-cars-trans subsetp-strip-cars)
           :use ((:instance subsetp-trans (a l) (b l1) (c l2))
                 (:instance subsetp-trans (a l1) (b (cons (cons tmp ty) (true-list-fix l1))) (c l2))
                 (:instance subsetp-strip-cars-trans (a (asg :list s1)) (b l1) (c l2))
                 (:instance subsetp-strip-cars (a (cons (cons tmp ty) (true-list-fix l1))) (b l2))))))

(defthm gt-new-glue
  (implies (and (not (intersectp-equal (asg :list s1) (append fs ems (strip-cars l))))
                (not (member-equal tmp fs)) (not (member-equal tmp ems)) (not (member-equal tmp (strip-cars l1)))
                (subsetp-equal l l1)
                (not (intersectp-equal (asg :list ss) (append fs ems (strip-cars (cons (cons tmp ty) (true-list-fix l1)))))))
           (not (intersectp-equal (asg :list (append s1 (cons (list :assign (list :var tmp) c) ss)))
                                  (append fs ems (strip-cars l)))))
  :hints (("Goal" :in-theory (disable intersectp-subset-r subsetp-strip-cars not-member-strip-cars-sub)
           :use ((:instance subsetp-strip-cars (a l) (b l1))
                 (:instance not-member-strip-cars-sub (x tmp) (a l) (b l1))
                 (:instance intersectp-subset-r (a (asg :list ss)) (b (strip-cars l)) (c (strip-cars l1)))))))

; each fact about g-tail by its own induction on g-tail: base, error, step
(defmacro gt-fact (name body &key use)
  (let ((thm (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-THM") name))
        (base (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BASE") name))
        (err (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-ERR") name))
        (step (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-STEP") name)))
    `(progn
       (defun ,name (vars xs em cnt locs sigs fnames)
         (declare (xargs :verify-guards nil))
         (mv-let (e s as cnt2 locs2) (g-tail vars xs em cnt locs sigs fnames)
           (declare (ignorable s as cnt2 locs2))
           (implies (not e) ,body)))
       (defthm ,base
         (implies (or (atom vars) (atom xs)) (,name vars xs em cnt locs sigs fnames))
         :hints (("Goal" :expand ((g-tail vars xs em cnt locs sigs fnames) (cf-stmts nil)))))
       (defthm ,err
         (implies (and (consp vars) (consp xs) (or (gt1 0) (not (equal (gt1 3) :int64)) (gtf 0)))
                  (,name vars xs em cnt locs sigs fnames))
         :hints (("Goal" :expand ((g-tail vars xs em cnt locs sigs fnames)) :in-theory (disable g-expr g-fresh))))
       (defthm ,step
         (implies (and (consp vars) (consp xs) (,name (cdr vars) (cdr xs) em (gtf 2) (gtf 3) sigs fnames))
                  (,name vars xs em cnt locs sigs fnames))
         :hints (("Goal" :do-not-induct t
                  :in-theory (disable g-expr g-tail g-tmp g-fresh lf-ok cf-stmts no-calls g-formal
                                      gt-locs-glue gt-new-glue g-fresh-facts g-expr-names)
                  :use ((:instance g-tail-open)
                        (:instance g-fresh-facts (base (car vars)) (ty (gt1 3)) (cnt (gt1 4)) (locs (gt1 5))
                                   (used (append fnames (em-names em))))
                        (:instance g-expr-names (x (car xs)))
                        ,@use))))
       (defthm ,thm
         (,name vars xs em cnt locs sigs fnames)
         :hints (("Goal" :induct (g-tail vars xs em cnt locs sigs fnames)
                  :in-theory (disable ,name g-expr g-fresh (:definition g-tail)))))
       (in-theory (disable ,name)))))

(gt-fact gt-locs (and (subsetp-equal locs locs2) (subsetp-equal (asg :list s) (strip-cars locs2))
                      (subsetp-equal (as-srcs as) (strip-cars locs2)))
         :use ((:instance gt-locs-glue (s1 (gt1 1)) (l locs) (l1 (gt1 5)) (tmp (gtf 1)) (ty (gt1 3)) (c (gt1 2))
                          (ss (gtr 1)) (as (gtr 2)) (l2 (gtr 4)) (f (g-formal (car vars))))))

(gt-fact gt-new (not (intersectp-equal (asg :list s) (append fnames (em-names em) (strip-cars locs))))
         :use ((:instance gt-locs-thm (vars (cdr vars)) (xs (cdr xs)) (cnt (gtf 2)) (locs (gtf 3)))
               (:instance gt-new-glue (s1 (gt1 1)) (fs fnames) (ems (em-names em)) (l locs) (l1 (gt1 5))
                          (tmp (gtf 1)) (ty (gt1 3)) (c (gt1 2)) (ss (gtr 1)))))

(gt-fact gt-as (and (as-ok as vars (append fnames (em-names em)))
                    (implies (equal (len vars) (len xs)) (equal (len as) (len vars)))))

(gt-fact gt-cf (implies (no-calls :list xs sigs) (and (cf-stmts s) (cf-stmts as)))
         :use ((:instance g-expr-cf (x (car xs)))))

(gt-fact gt-lf (implies (lf-ok locs fnames) (lf-ok locs2 fnames))
         :use ((:instance g-expr-fresh (x (car xs)))
               (:instance lf-ok-g-fresh (base (car vars)) (ty (gt1 3)) (cnt (gt1 4)) (locs (gt1 5))
                          (rest (em-names em)))))

; ---- the assignments' run: each formal's dummy gets its temporary's value

(defun tl-ok (as vs fr)
  ; each assignment's temporary holds its value, an int64
  (if (atom as) t
    (and (consp vs) (int64p (car vs)) (equal (cdr (lkp (kadr (kaddr (car as))) fr)) (cons :int64 (car vs)))
         (tl-ok (cdr as) (cdr vs) fr))))

(defun dums-are (vars vs fr)
  (if (atom vars) t
    (and (equal (cdr (lkp (g-formal (car vars)) fr)) (cons :int64 (car vs))) (dums-are (cdr vars) (cdr vs) fr))))

(defun int-dums (vars fr)
  (if (atom vars) t (and (equal (dty (g-formal (car vars)) fr) (list :int64)) (int-dums (cdr vars) fr))))

(defthm tl-ok-put
  (implies (and (tl-ok as vs fr) (not (member-equal k (as-srcs as)))) (tl-ok as vs (put k v fr))))

(defthm int-dums-put
  (implies (and (int-dums vars fr) (consp v) (equal (car v) :int64)) (int-dums vars (put k v fr))))

(defthm as-ok-srcs
  (implies (and (as-ok as vars used) (member-equal k used)) (not (member-equal k (as-srcs as)))))

(defthm as-ok-asg
  (implies (as-ok as vars used) (subsetp-equal (asg :list as) (g-formals vars)))
  :hints (("Goal" :induct (as-ok as vars used) :expand ((asg :list as)))))

(defthm as-ok-not-asg
  (implies (and (as-ok as vars used) (not (member-equal k (g-formals vars)))) (not (member-equal k (asg :list as))))
  :hints (("Goal" :use as-ok-asg :in-theory (disable as-ok-asg))))

(defthm member-g-formals-sub
  (implies (and (subsetp-equal (g-formals vars) used) (consp vars)) (member-equal (g-formal (car vars)) used)))

(defthm as-step
  (implies (and (equal (cdr (lkp tmp fr)) (cons :int64 v)) (int64p v) (equal (dty f fr) (list :int64)))
           (equal (fx (list :assign (list :var f) (list :var tmp)) fr) (mv :normal (put f (cons :int64 v) fr))))
  :hints (("Goal" :in-theory (enable dty) :expand ((fx (list :assign (list :var f) (list :var tmp)) fr)))))

(defun as-ind (as vars vs fr)
  (if (atom as) (list vars vs fr)
    (as-ind (cdr as) (cdr vars) (cdr vs) (put (g-formal (car vars)) (cons :int64 (car vs)) fr))))

(defthm as-run
  (implies (and (as-ok as vars used) (subsetp-equal (g-formals vars) used) (no-duplicatesp-equal (g-formals vars))
                (equal (len as) (len vars)) (tl-ok as vs fr) (int-dums vars fr))
           (and (equal (car (fx-list as fr)) :normal) (dums-are vars vs (mv-nth 1 (fx-list as fr)))))
  :hints (("Goal" :induct (as-ind as vars vs fr) :in-theory (disable fv fx put dty g-formal)
           :expand ((fx-list as fr) (as-ok as vars used) (tl-ok as vs fr) (int-dums vars fr)))))

; ---- g-tail's statements' run: each temporary holds its argument's value

(defun gt-sem (vars xs em cnt locs sigs fnames env defs n fr)
  (declare (xargs :verify-guards nil))
  (mv-let (e s as cnt2 locs2) (g-tail vars xs em cnt locs sigs fnames)
    (declare (ignore cnt2))
    (mv-let (ae vs) (a-ev-list xs env defs n)
      (implies (and (not e) (not ae) (no-calls :list xs sigs) (em-ok em env fr) (decl-ok locs2 fr) (no-prim-defs defs))
               (mv-let (st fr2) (fx-list s fr)
                 (and (equal st :normal) (em-ok em env fr2) (tl-ok as vs fr2)))))))

(defun-nx gt-ind (vars xs em cnt locs sigs fnames env defs n fr)
  (declare (xargs :measure (acl2-count xs) :verify-guards nil))
  (if (or (atom vars) (atom xs)) (list fr n)
    (gt-ind (cdr vars) (cdr xs) em (gtf 2) (gtf 3) sigs fnames env defs (1- n)
            (fr-after (append (gt1 1) (list (list :assign (list :var (gtf 1)) (gt1 2)))) fr))))

(defthm ge-sem-int
  (implies (and (ge-sem x em cnt locs sigs fnames env defs n fr) (equal (ge 3) :int64)
                (not (ge 0)) (not (car (a-ev x env defs n))) (no-calls :term x sigs) (em-ok em env fr)
                (decl-ok (ge 5) fr) (no-prim-defs defs))
           (int64p (mv-nth 1 (a-ev x env defs n))))
  :hints (("Goal" :use ge-sem-use :in-theory (disable ge-sem-use g-expr a-ev fx-list fv no-calls em-ok decl-ok))))

(defmacro gto (k) `(mv-nth ,k (g-tail vars xs em cnt locs sigs fnames)))

(defthm gt-sem-use
  (implies (and (gt-sem vars xs em cnt locs sigs fnames env defs n fr)
                (not (gto 0)) (not (car (a-ev-list xs env defs n))) (no-calls :list xs sigs) (em-ok em env fr)
                (decl-ok (gto 4) fr) (no-prim-defs defs))
           (and (equal (car (fx-list (gto 1) fr)) :normal)
                (em-ok em env (mv-nth 1 (fx-list (gto 1) fr)))
                (tl-ok (gto 2) (mv-nth 1 (a-ev-list xs env defs n)) (mv-nth 1 (fx-list (gto 1) fr)))))
  :hints (("Goal" :in-theory (e/d (gt-sem) (g-tail a-ev-list fx-list em-ok decl-ok no-calls tl-ok)))))

(defthm gt-sem-base
  (implies (or (atom vars) (atom xs)) (gt-sem vars xs em cnt locs sigs fnames env defs n fr))
  :hints (("Goal" :expand ((g-tail vars xs em cnt locs sigs fnames) (fx-list nil fr)))))

(defthm gt-sem-step
  (implies (and (consp vars) (consp xs)
                (ge-sem (car xs) em cnt locs sigs fnames env defs (1- n) fr)
                (gt-sem (cdr vars) (cdr xs) em (gtf 2) (gtf 3) sigs fnames env defs (1- n)
                        (fr-after (append (gt1 1) (list (list :assign (list :var (gtf 1)) (gt1 2)))) fr)))
           (gt-sem vars xs em cnt locs sigs fnames env defs n fr))
  :hints (("Goal" :do-not-induct t :expand ((gt-sem vars xs em cnt locs sigs fnames env defs n fr))
           :in-theory (e/d (gt-new gt-locs)
                           (g-expr g-tail g-fresh a-ev fx-list fv no-calls em-ok decl-ok-subset fx-list-append
                               g-tmp nfix scalar-ok dty gt-sem g-expr-names tl-ok-put gt-new-thm gt-locs-thm))
           :use ((:instance g-tail-open)
                 (:instance subsetp-trans (a (gt1 5)) (b (gtf 3)) (c (gtr 4)))
                 (:instance g-fresh-facts (base (car vars)) (ty (gt1 3)) (cnt (gt1 4)) (locs (gt1 5))
                            (used (append fnames (em-names em))))
                 (:instance g-expr-names (x (car xs)))
                 (:instance gt-locs-thm (vars (cdr vars)) (xs (cdr xs)) (cnt (gtf 2)) (locs (gtf 3)))
                 (:instance gt-new-thm (vars (cdr vars)) (xs (cdr xs)) (cnt (gtf 2)) (locs (gtf 3)))
                 (:instance decl-ok-subset (a (gtf 3)) (b (gtr 4)))
                 (:instance decl-ok-subset (a (gt1 5)) (b (gtr 4)))))))

(defthm ge-sem-t (ge-sem x em cnt locs sigs fnames env defs n fr) :hints (("Goal" :use ge-sem-all)))

(defthm gt-sem-thm
  (gt-sem vars xs em cnt locs sigs fnames env defs n fr)
  :hints (("Goal" :induct (gt-ind vars xs em cnt locs sigs fnames env defs n fr)
           :in-theory (disable gt-sem g-expr g-tail g-fresh fr-after))))
