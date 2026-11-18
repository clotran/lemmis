; gen-stok: sx is f-ex wherever sx answers without error, no cs-stmts
; needed (sv answers :syntax outside cs-expr, sx (errst :syntax) outside
; cs-stmt, and only the branch taken is run by either); and a DO around
; statements that answer :normal, then EXIT, answers :normal. So
; g-st-fn-sem needs neither (cs-stmts stmts) nor (not (g-has '(:cycle) stmts)).

(in-package "ACL2")

(include-book "gen-stexp")

(defthm sv-ok-cs
  (implies (not (mv-nth 0 (sv e fr heap))) (cs-expr e))
  :hints (("Goal" :induct (sv e fr heap) :in-theory (enable sv))))

(defthm sv-ok-is-f-ev
  (implies (and (not (mv-nth 0 (sv e fr heap))) (< (acl2-count e) k) (integerp k))
           (equal (f-ev e fr heap procs k) (sv e fr heap)))
  :hints (("Goal" :in-theory (disable sv-is-f-ev sv-ok-cs cs-expr f-ev) :use (sv-ok-cs sv-is-f-ev))))

(in-theory (disable sv-ok-cs))

(defthm sv-atom (implies (atom e) (equal (sv e fr heap) (mv :syntax nil))) :hints (("Goal" :in-theory (enable sv))))

; an assignment sx runs without error is a cs-stmt (sx never recurses into one)
(defthm sx-assign-ok-cs
  (implies (and (equal (kar s) :assign) (not (errstp (mv-nth 0 (sx s fr heap))))) (cs-stmt s))
  :hints (("Goal" :in-theory (disable sv obj-of comp-of) :expand ((sx s fr heap) (cs-stmt s))
           :use ((:instance sv-ok-cs (e (kaddr s))) (:instance sv-ok-cs (e (kadddr (kadr s))))))))

(defthm sx-ok-assign-f-ex
  (implies (and (equal (kar s) :assign) (not (errstp (mv-nth 0 (sx s fr heap)))) (integerp k) (< (acl2-count s) k))
           (equal (f-ex s fr heap procs k) (sx s fr heap)))
  :hints (("Goal" :in-theory (disable sx-assign-ok-cs sx-is-f-ex sx f-ex) :use (sx-assign-ok-cs sx-is-f-ex))))

(defthm sx-ok-is-f-ex-flag
  (implies (and (integerp k) (< (acl2-count s) k))
           (if (eq flag :stmt)
               (implies (and (not (equal (kar s) :assign)) (not (errstp (mv-nth 0 (sx s fr heap)))))
                        (equal (f-ex s fr heap procs k) (sx s fr heap)))
             (implies (not (errstp (mv-nth 0 (sx-list s fr heap)))) (equal (f-ex-list s fr heap procs k) (sx-list s fr heap)))))
  :rule-classes nil
  :hints (("Goal" :induct (sx-ind flag s fr heap k) :do-not-induct t
           :in-theory (disable f-ex f-ex-list f-ex-return sv-is-f-ev sx-is-f-ex sx-assign-ok-cs))
          (and stable-under-simplificationp
               '(:expand ((sx s fr heap) (sx-list s fr heap))))))

(defthm sx-ok-is-f-ex-list
  (implies (and (not (errstp (mv-nth 0 (sx-list ss fr heap)))) (integerp k) (< (acl2-count ss) k))
           (equal (f-ex-list ss fr heap procs k) (sx-list ss fr heap)))
  :hints (("Goal" :use (:instance sx-ok-is-f-ex-flag (flag :list) (s ss)))))

(defthm acl2-count-append-le
  (<= (acl2-count (append a b)) (+ (acl2-count a) (acl2-count b)))
  :rule-classes :linear)

; the DO g-st-fn puts around a body with a CYCLE in it
(defthm sx-list-exit
  (equal (sx-list '((:exit)) fr heap) (mv :exit fr heap))
  :hints (("Goal" :expand ((sx-list '((:exit)) fr heap) (sx '(:exit) fr heap) (sx-list nil fr heap)))))

(defthm f-ex-list-exit-tail
  (implies (and (equal (mv-nth 0 (sx-list ss fr heap)) :normal) (integerp k) (< (acl2-count (append ss '((:exit)))) k))
           (equal (f-ex-list (append ss '((:exit))) fr heap procs k)
                  (mv :exit (mv-nth 1 (sx-list ss fr heap)) (mv-nth 2 (sx-list ss fr heap)))))
  :hints (("Goal" :in-theory (disable f-ex f-ex-list sx-list sx-ok-is-f-ex-list)
           :use (:instance sx-ok-is-f-ex-list (ss (append ss '((:exit))))))))

(defthm f-ex-do-exit
  (implies (and (posp j) (equal (f-ex-list body fr heap procs (1- j)) (mv :exit a b)))
           (equal (f-ex (list :do body) fr heap procs j) (mv :normal a b)))
  :hints (("Goal" :in-theory (disable f-ex f-ex-list) :expand ((f-ex (list :do body) fr heap procs j)))))

(defthm f-ex-list-one-normal
  (implies (and (integerp k) (< 1 k) (equal (f-ex x fr heap procs (1- k)) (mv :normal a b)))
           (equal (f-ex-list (list x) fr heap procs k) (mv :normal a b)))
  :hints (("Goal" :in-theory (disable f-ex f-ex-list)
           :expand ((f-ex-list (list x) fr heap procs k) (f-ex-list nil a b procs (1- k))))))

(defthm f-ex-list-do-exit
  (implies (and (equal (mv-nth 0 (sx-list ss fr heap)) :normal) (integerp k) (< (+ 3 (acl2-count (append ss '((:exit))))) k))
           (equal (f-ex-list (list (list :do (append ss '((:exit))))) fr heap procs k)
                  (mv :normal (mv-nth 1 (sx-list ss fr heap)) (mv-nth 2 (sx-list ss fr heap)))))
  :hints (("Goal" :in-theory (disable f-ex f-ex-list sx-list f-ex-list-exit-tail f-ex-do-exit f-ex-list-one-normal)
           :use ((:instance f-ex-list-exit-tail (k (+ -2 k)))
                 (:instance f-ex-do-exit (body (append ss '((:exit)))) (j (+ -1 k))
                            (a (mv-nth 1 (sx-list ss fr heap))) (b (mv-nth 2 (sx-list ss fr heap))))
                 (:instance f-ex-list-one-normal (x (list :do (append ss '((:exit)))))
                            (a (mv-nth 1 (sx-list ss fr heap))) (b (mv-nth 2 (sx-list ss fr heap))))))))
