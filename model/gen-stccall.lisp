; gen-stccall: a-stc's :sub call is gen-stcallst's a-stcall (GEN.md 4 (4a)).
; For x = (f . xs), f a :sub of st, no stobj argument an update (each is
; f's formal itself), as many arguments as formals, no formal named mv and
; no argument an (mv-nth 'k mv): wherever a-stc answers no error, a-stcall
; at one less fuel answers no error and the same S'. a-stc-args spends
; fuel on the stobj arguments too, so the value arguments are compared by
; a-sx-mono (gen-stmono).

(in-package "ACL2")

(include-book "gen-stc")
(include-book "gen-stmono")

(defun no-mvnth (xs) (if (atom xs) t (and (not (g-mvnth (car xs))) (no-mvnth (cdr xs)))))

(defun stca-ind (vars xs st n m)
  (declare (xargs :measure (acl2-count xs)))
  (if (or (zp n) (atom xs)) (list vars m)
    (stca-ind (cdr vars) (cdr xs) st (1- n) (if (eq (g-role (car vars) st) :stobj) m (1- m)))))

(defthm a-stc-args-zp
  (implies (zp n) (equal (a-stc-args vars xs env s0 s mvv st defs n) (mv :fuel nil s)))
  :hints (("Goal" :expand ((a-stc-args vars xs env s0 s mvv st defs n)))))

(defthm a-sx-list-zp
  (implies (zp n) (equal (a-sx-list xs env s st defs n) (mv :fuel nil)))
  :hints (("Goal" :expand ((a-sx-list xs env s st defs n)))))

(defthm a-stc-stobj-var
  (implies (eq (g-role v st) :stobj) (equal (a-stc v env s st defs n) (if (zp n) (mv :fuel s) (mv nil s))))
  :hints (("Goal" :expand ((a-stc v env s st defs n)))))

; a-stc-args on such arguments: S unchanged, the value results a-sx-list's
(defthm a-stc-args-noupd
  (implies (and (not (g-upd vars xs st)) (no-mvnth xs) (not (member-equal 'mv vars)) (equal (len xs) (len vars))
                (not (car (a-stc-args vars xs env s0 s nil st defs n))) (integerp m) (<= n m))
           (and (equal (mv-nth 2 (a-stc-args vars xs env s0 s nil st defs n)) s)
                (not (car (a-sx-list (g-cvals vars xs st) env s0 st defs m)))
                (equal (mv-nth 1 (a-sx-list (g-cvals vars xs st) env s0 st defs m))
                       (g-cvals vars (mv-nth 1 (a-stc-args vars xs env s0 s nil st defs n)) st))))
  :rule-classes nil
  :hints (("Goal" :induct (stca-ind vars xs st n m)
           :in-theory (disable a-sx a-stc g-mvnth g-role)
           :expand ((a-stc-args vars xs env s0 s nil st defs n) (a-sx-list (g-cvals vars xs st) env s0 st defs m)
                    (a-stc (car xs) env s st defs (+ -1 n)) (g-cvals vars xs st) (g-upd vars xs st)
                    (:free (v vs) (g-cvals vars (cons v vs) st))))
          (and stable-under-simplificationp
               '(:use ((:instance a-sx-mono (x (car xs)) (env env) (s s0) (n (+ -1 n)) (m (+ -1 m))))))))

(defthm a-stc-call-is-a-stcall
  (implies (and (consp x) (eq (g-role (car x) st) :sub) (not (g-upd (g-obj (car x) st) (cdr x) st))
                (equal (len (cdr x)) (len (g-obj (car x) st))) (not (member-equal 'mv (g-obj (car x) st))) (no-mvnth (cdr x))
                (not (car (a-stc-call x env s st defs n))))
           (and (not (car (a-stcall x env s st defs n)))
                (equal (mv-nth 1 (a-stcall x env s st defs n)) (mv-nth 2 (a-stc-call x env s st defs n)))
                (equal (mv-nth 2 (a-stcall x env s st defs n)) (mv-nth 1 (a-stc-call x env s st defs n)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable a-stc-args a-sx-list g-cvals g-upd g-role)
           :expand ((a-stc-call x env s st defs n))
           :use ((:instance a-stc-args-noupd (vars (g-obj (car x) st)) (xs (cdr x)) (s0 s) (n (+ -1 n)) (m n))))))

; a-stc on the call: a-stcall's S', at one less fuel
(defthm a-stc-sub-is-a-stcall
  (implies (and (consp x) (eq (g-role (car x) st) :sub) (not (g-upd (g-obj (car x) st) (cdr x) st))
                (equal (len (cdr x)) (len (g-obj (car x) st))) (not (member-equal 'mv (g-obj (car x) st))) (no-mvnth (cdr x))
                (not (g-role 'if st)) (not (car (a-stc x env s st defs n))))
           (and (not (car (a-stcall x env s st defs (1- n))))
                (equal (a-stc x env s st defs n) (mv nil (mv-nth 1 (a-stcall x env s st defs (1- n)))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable a-stc-call a-stcall g-upd g-obj)
           :expand ((a-stc x env s st defs n))
           :use ((:instance a-stc-call-is-a-stcall (n (1- n)))))))
