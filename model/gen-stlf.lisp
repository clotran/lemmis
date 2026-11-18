; gen-stlf: g-sexpr and g-stmt (st-plain, call-free) keep lf-ok: every
; temporary they add is g-fresh's, checked against fnames, so the locals
; never shadow a dummy or an object, nor "r". g-st-fn-sem's side condition
; (lf-ok locs fnames) on g-stmt's output, proved (gen-fresh's gf-ok-thm,
; for g-sexpr and g-stmt).

(in-package "ACL2")

(include-book "gen-stind")
(include-book "gen-fresh")

(defun sl-ok (flag x vars em cnt locs sigs fnames st)
  (case flag
    (:args (mv-let (e ss cs ts cnt2 locs2) (g-sargs x em cnt locs sigs fnames st)
             (declare (ignore ss cs ts cnt2))
             (implies (and (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames))))
    (:vals (mv-let (e ss binds cnt2 locs2) (g-svals vars x em cnt locs sigs fnames st)
             (declare (ignore ss binds cnt2))
             (implies (and (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames))))
    (otherwise (mv-let (e ss c ty cnt2 locs2) (g-sexpr x em cnt locs sigs fnames st)
                 (declare (ignore ss c ty cnt2))
                 (implies (and (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames))))))

(defthm sl-ok-thm
  (implies (if (member-eq flag '(:args :vals)) (no-calls :list x sigs nil) (no-calls :term x sigs nil))
           (sl-ok flag x vars em cnt locs sigs fnames st))
  :rule-classes nil
  :hints (("Goal" :induct (sn-ind flag x vars em cnt locs sigs fnames st env s defs n fr heap) :do-not-induct t
           :in-theory (disable g-st-free g-mvnth g-role g-obj g-comp g-fresh g-if g-expr g-unop g-binop lf-ok
                               g-st-ident em-names sx-fr a-svs a-sv no-calls g-fresh-out g-tmp))
          (and stable-under-simplificationp
               '(:expand ((g-sexpr x em cnt locs sigs fnames st) (g-sargs x em cnt locs sigs fnames st)
                          (g-svals vars x em cnt locs sigs fnames st))))))

(defthm sl-sexpr
  (implies (and (no-calls :term x sigs nil) (not (mv-nth 0 (g-sexpr x em cnt locs sigs fnames st))) (lf-ok locs fnames))
           (lf-ok (mv-nth 5 (g-sexpr x em cnt locs sigs fnames st)) fnames))
  :hints (("Goal" :use (:instance sl-ok-thm (flag :expr)))))

(defthm sl-svals
  (implies (and (no-calls :list x sigs nil) (not (mv-nth 0 (g-svals vars x em cnt locs sigs fnames st))) (lf-ok locs fnames))
           (lf-ok (mv-nth 4 (g-svals vars x em cnt locs sigs fnames st)) fnames))
  :hints (("Goal" :use (:instance sl-ok-thm (flag :vals)))))

(in-theory (disable sl-ok))

; ---- g-stmt, on st-plain statements (gst-ind)

(defun stl-ok (flag x vars em cnt locs sigs fnames st outs)
  (if (eq flag :acts)
      (mv-let (e ss cnt2 locs2) (g-sacts vars x em cnt locs sigs fnames st)
        (declare (ignore ss cnt2))
        (implies (and (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames)))
    (mv-let (e ss cnt2 locs2) (g-stmt x em cnt locs sigs fnames st outs nil nil)
      (declare (ignore ss cnt2))
      (implies (and (not e) (lf-ok locs fnames)) (lf-ok locs2 fnames)))))

(defthm lf-ok-alistp (implies (lf-ok l f) (alistp l)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable lf-ok))))

(defthm lf-ok-tlf (implies (lf-ok l f) (lf-ok (true-list-fix l) f)))

(defthm lf-ok-g-fresh-tmp
  (implies (and (lf-ok locs fnames) (not (car (g-fresh b ty2 cnt locs (append fnames rest))))
                (equal nm (g-tmp b (1+ (nfix cnt)))))
           (lf-ok (cons (cons nm ty) locs) fnames))
  :hints (("Goal" :in-theory (e/d (lf-ok g-fresh g-used) (g-tmp)))))

(defthm lf-ok-g-fresh-tmp-tlf
  (implies (and (lf-ok locs fnames) (not (car (g-fresh b ty2 cnt locs (append fnames rest))))
                (equal nm (g-tmp b (1+ (nfix cnt)))))
           (lf-ok (cons (cons nm ty) (true-list-fix locs)) fnames))
  :hints (("Goal" :in-theory (e/d (lf-ok g-fresh g-used) (g-tmp)))))

(defthm stl-ok-thm
  (implies (not (g-role 'if st))
           (if (eq flag :acts)
               (implies (and (st-plain :acts x vars st) (no-calls :list x sigs nil)) (stl-ok :acts x vars em cnt locs sigs fnames st outs))
             (implies (and (st-plain :term x nil st) (no-calls :term x sigs nil)) (stl-ok :term x vars em cnt locs sigs fnames st outs))))
  :rule-classes nil
  :hints (("Goal" :induct (gst-ind flag x vars em cnt locs sigs fnames st outs env s defs n fr heap o) :do-not-induct t
           :expand ((st-plain :term x nil st) (st-plain :acts x vars st))
           :in-theory (disable g-stmt g-sacts g-sexpr g-svals g-st-free g-mvnth g-role g-obj g-comp g-fresh lf-ok g-stable
                               em-names no-calls (:definition gst-ind) st-plain g-tmp))))

(defthm stl-holds
  (implies (and (not (g-role 'if st)) (st-plain :term x nil st) (no-calls :term x sigs nil)
                (not (mv-nth 0 (g-stmt x em cnt locs sigs fnames st outs nil nil))) (lf-ok locs fnames))
           (lf-ok (mv-nth 3 (g-stmt x em cnt locs sigs fnames st outs nil nil)) fnames))
  :hints (("Goal" :in-theory (disable g-stmt g-sacts st-plain no-calls lf-ok g-role) :use (:instance stl-ok-thm (flag :term)))))
