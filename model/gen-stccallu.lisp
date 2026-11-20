; gen-stccallu: a-stc's :sub call with updated stobj arguments is
; gen-stcallu's a-stcall-u (GEN.md 4 (4a)), as gen-stccall's
; a-stc-sub-is-a-stcall is for calls without updates. The stobj arguments'
; updates are st-plain, where a-stc is a-st wherever a-st answers (gen-stc's
; a-stc-is-a-st), so, given that a-sacts answers no error (gst-callst-u
; assumes it anyway), a-stc-args' thread is a-sacts'; the values are
; a-sx-list's by a-sx-mono. (The converse, a-st from a-stc answering, fails:
; an (mv-nth 'k mv) argument of a nested lambda reads mv under a-stc only.)

(in-package "ACL2")

(include-book "gen-stcallu")

; ---- a-stc's :sub call with updated stobj arguments is a-stcall-u

(defun-nx stcu-ind (vars xs env s st defs n m)
  (declare (xargs :measure (acl2-count xs)))
  (if (or (zp n) (atom xs)) (list vars m)
    (if (eq (g-role (car vars) st) :stobj)
        (stcu-ind (cdr vars) (cdr xs) env (mv-nth 1 (a-st (car xs) env s st defs (1- n))) st defs (1- n) m)
      (stcu-ind (cdr vars) (cdr xs) env s st defs (1- n) (1- m)))))

(defthm st-plain-acts-car
  (implies (and (st-plain :acts xs vars st) (consp xs) (consp vars) (eq (g-role (car vars) st) :stobj) (not (g-mvnth (car xs)))
                (symbolp (car vars)))
           (st-plain :term (car xs) nil st))
  :hints (("Goal" :expand ((st-plain :acts xs vars st) (st-plain :term (car vars) nil st)) :in-theory (disable g-role g-mvnth))))

(defthm a-stc-args-upd
  (implies (and (st-plain :acts xs vars st) (no-mvnth xs) (not (member-equal 'mv vars)) (equal (len xs) (len vars))
                (symbol-listp vars)
                (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (not (g-role nil st))
                (not (car (a-stc-args vars xs env s0 s nil st defs n))) (not (car (a-sacts vars xs env s st defs n)))
                (integerp m) (<= n m))
           (and (equal (mv-nth 2 (a-stc-args vars xs env s0 s nil st defs n)) (mv-nth 1 (a-sacts vars xs env s st defs n)))
                (not (car (a-sx-list (g-cvals vars xs st) env s0 st defs m)))
                (equal (mv-nth 1 (a-sx-list (g-cvals vars xs st) env s0 st defs m))
                       (g-cvals vars (mv-nth 1 (a-stc-args vars xs env s0 s nil st defs n)) st))))
  :rule-classes nil
  :hints (("Goal" :induct (stcu-ind vars xs env s st defs n m)
           :in-theory (disable a-sx a-stc a-st g-mvnth g-role)
           :expand ((a-stc-args vars xs env s0 s nil st defs n) (a-sx-list (g-cvals vars xs st) env s0 st defs m)
                    (a-sacts vars xs env s st defs n) (g-cvals vars xs st) (no-mvnth xs) (st-plain :acts xs vars st)
                    (:free (v vs) (g-cvals vars (cons v vs) st))))
          (and stable-under-simplificationp
               '(:use ((:instance a-sx-mono (x (car xs)) (env env) (s s0) (n (+ -1 n)) (m (+ -1 m)))
                       (:instance a-stc-is-a-st (x (car xs)) (n (+ -1 n))))))))

(defthm a-stc-call-is-a-stcall-u
  (implies (and (consp x) (eq (g-role (car x) st) :sub) (equal (len (cdr x)) (len (g-obj (car x) st)))
                (symbol-listp (g-obj (car x) st)) (not (member-equal 'mv (g-obj (car x) st))) (no-mvnth (cdr x))
                (st-plain :acts (cdr x) (g-obj (car x) st) st)
                (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (not (g-role nil st))
                (not (car (a-stc-call x env s st defs n))) (not (car (a-sacts (g-obj (car x) st) (cdr x) env s st defs (1- n)))))
           (and (not (car (a-stcall-u x env s st defs (1- n))))
                (equal (mv-nth 1 (a-stcall-u x env s st defs (1- n))) (mv-nth 2 (a-stc-call x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable a-stc-args a-sx-list a-sacts g-cvals g-upd g-role)
           :expand ((a-stc-call x env s st defs n))
           :use ((:instance a-stc-args-upd (vars (g-obj (car x) st)) (xs (cdr x)) (s0 s) (n (+ -1 n)) (m (+ -1 n)))))))

; a-stc on the call: a-stcall-u's S', two fuel units down
(defthm a-stc-sub-is-a-stcall-u
  (implies (and (consp x) (eq (g-role (car x) st) :sub) (equal (len (cdr x)) (len (g-obj (car x) st)))
                (symbol-listp (g-obj (car x) st)) (not (member-equal 'mv (g-obj (car x) st))) (no-mvnth (cdr x))
                (st-plain :acts (cdr x) (g-obj (car x) st) st)
                (not (consp (lkp 'mv-nth defs))) (not (g-role 'mv-nth st)) (not (g-role 'mv st)) (not (g-role nil st))
                (not (g-role 'if st)) (not (car (a-stc x env s st defs n)))
                (not (car (a-sacts (g-obj (car x) st) (cdr x) env s st defs (- n 2)))))
           (and (not (car (a-stcall-u x env s st defs (- n 2))))
                (equal (a-stc x env s st defs n) (mv nil (mv-nth 1 (a-stcall-u x env s st defs (- n 2)))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable a-stc-call a-stcall-u g-upd g-obj)
           :expand ((a-stc x env s st defs n))
           :use ((:instance a-stc-call-is-a-stcall-u (n (1- n)))))))
