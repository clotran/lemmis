; gen-stopen: g-stmt's openers with dests and tself free (gen-stfn's
; tsx: the tail position does not matter on st-plain statements).

(in-package "ACL2")

(include-book "gen-stind")

; ---- g-stmt's tself and dests do not matter on st-plain statements

; the function in tail position: not a role a st-plain statement heads
(defun tself-ok (tself st)
  (or (null tself) (and (symbolp tself) (not (eq tself 'if)) (not (member-eq (g-role tself st) '(:set :seti))))))

(defun-sk tsx (x sigs fnames st)
  (forall (em cnt locs outs dests tself)
          (implies (tself-ok tself st)
                   (equal (g-stmt x em cnt locs sigs fnames st outs dests tself)
                          (g-stmt x em cnt locs sigs fnames st outs nil nil)))))

(in-theory (disable tsx tself-ok))

;; openers with dests and tself free (gen-stst/gen-stcase/gen-stlst's, with nil nil)
(defthm g-stmt-set-t
  (implies (and (tself-ok tself st) (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :set))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests tself)
                  (if (not (and (= (len x) 3) (equal outs (list (caddr x))) (equal (g-obj (car x) st) (g-obj (caddr x) st))))
                      (mv :stobj nil cnt locs)
                    (mv-let (e s c ty cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                      (if (or e (not (eq ty :int64))) (mv (or e :type) nil cnt locs)
                        (mv-let (e s cs cnt locs) (if (symbolp (caddr x)) (mv nil s (list c) cnt locs)
                                                    (g-settle (list s) (list c) cnt locs (append fnames (em-names em))))
                          (if e (mv e nil cnt locs)
                            (mv-let (e si cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs dests nil)
                              (if e (mv e nil cnt locs)
                                (mv nil (append s si (list (list :assign (list :comp (g-obj (car x) st) (g-comp (car x) st)) (car cs))))
                                    cnt locs))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) '(tself-ok)) (gst-dis)) :expand ((g-stmt x em cnt locs sigs fnames st outs dests tself)))))

(defthm g-stmt-seti-t
  (implies (and (tself-ok tself st) (consp x) (true-listp x) (not (eq (car x) 'cons)) (eq (g-role (car x) st) :seti))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests tself)
                  (if (not (and (= (len x) 4) (equal outs (list (cadddr x))) (equal (g-obj (car x) st) (g-obj (cadddr x) st))))
                      (mv :stobj nil cnt locs)
                    (mv-let (e si ci ti cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                      (if (or e (not (eq ti :int64))) (mv (or e :type) nil cnt locs)
                        (mv-let (e sv cv tv cnt locs) (g-sexpr (caddr x) em cnt locs sigs fnames st)
                          (if (or e (not (eq tv :int64))) (mv (or e :type) nil cnt locs)
                            (mv-let (e tmi cnt locs) (g-fresh 'i :int64 cnt locs (append fnames (em-names em)))
                              (if e (mv e nil cnt locs)
                                (mv-let (e tmv cnt locs) (g-fresh 'v :int64 cnt locs (append fnames (em-names em)))
                                  (if e (mv e nil cnt locs)
                                    (mv-let (e ss cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs dests nil)
                                      (if e (mv e nil cnt locs)
                                        (mv nil (append si (list (list :assign (list :var tmi) ci)) sv
                                                        (list (list :assign (list :var tmv) cv)) ss
                                                        (list (list :assign (list :elem (g-obj (car x) st) (g-comp (car x) st)
                                                                                    (list :var tmi))
                                                                    (list :var tmv))))
                                            cnt locs))))))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) '(tself-ok)) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs dests tself)))))

(defthm g-stmt-if-t
  (implies (and (tself-ok tself st) (consp x) (true-listp x) (eq (car x) 'if) (not (g-role 'if st)))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests tself)
                  (if (or (not (= (len x) 4)) (<= 3 (g-chain x nil nil))) (mv :stobj nil cnt locs)
                    (mv-let (e sc cc tc cnt locs) (g-sexpr (cadr x) em cnt locs sigs fnames st)
                      (if (or e (not (eq tc :logical))) (mv (or e :type) nil cnt locs)
                        (mv-let (e sa cnt locs) (g-stmt (caddr x) em cnt locs sigs fnames st outs dests tself)
                          (if e (mv e nil cnt locs)
                            (mv-let (e sb cnt locs) (g-stmt (cadddr x) em cnt locs sigs fnames st outs dests tself)
                              (if e (mv e nil cnt locs)
                                (mv nil (append sc (list (list :if cc sa sb))) cnt locs))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) '(tself-ok)) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs dests tself)))))

(defthm g-stmt-lam-t
  (implies (and (tself-ok tself st) (consp x) (consp (car x)) (true-listp x) (not (member-equal 'mv (cadr (car x)))))
           (equal (g-stmt x em cnt locs sigs fnames st outs dests tself)
                  (let ((vars (cadr (car x))) (body (caddr (car x))))
                    (if (not (and (true-listp (car x)) (= (len (car x)) 3) (eq (caar x) 'lambda) (symbol-listp vars)
                                  (no-duplicatesp-eq vars) (= (len vars) (len (cdr x)))))
                        (mv :stobj nil cnt locs)
                      (mv-let (e s binds cnt locs) (g-svals vars (cdr x) em cnt locs sigs fnames st)
                        (if e (mv e nil cnt locs)
                          (if (not (g-acts-place vars (cdr x) em st)) (mv :mv nil cnt locs)
                            (mv-let (e sa cnt locs) (g-sacts vars (cdr x) em cnt locs sigs fnames st)
                              (if e (mv e nil cnt locs)
                                (mv-let (e sb cnt locs) (g-stmt body (append binds em) cnt locs sigs fnames st outs dests tself)
                                  (if e (mv e nil cnt locs)
                                    (mv nil (append s sa sb) cnt locs))))))))))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (union-theories (current-theory :here) '(tself-ok)) '(kadr kaddr kar)) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs dests tself)))))

(defthm g-stmt-sym-t
  (implies (symbolp x)
           (equal (g-stmt x em cnt locs sigs fnames st outs dests tself)
                  (if (equal (list x) outs) (mv nil nil cnt locs) (mv :stobj nil cnt locs))))
  :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (gst-dis))
           :expand ((g-stmt x em cnt locs sigs fnames st outs dests tself)))))

