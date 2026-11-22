;; test/two_path_gen.clj, loaded by test/two_path.bb: (gen-program name seed) is a random
;; tier-A Lemmis module of version 0's subset, from the seed. Type-directed: every expression
;; is built knowing its Fortran kind (the generator's own promote, 10.1.5.2.1), a bound on its
;; magnitude, and, for reals, its granularity q (the value is a multiple of 2^-q; nil when
;; unknown), so nothing the standard leaves to the processor is ever asked for: no integer
;; overflow (bounds), no inexact complex product (q and bounds), no real power but x**2, no
;; complex division, no NaN, no signed zero reaching max/min/sign (+ 0.0 first), no
;; elementary function but sqrt (libm accuracy is the processor's). Covers integer(1) (2) (4)
;; (8), real(4) (8), complex(4) (8), logical, character; mixed-mode arithmetic, the kinded
;; intrinsics, relations, val, ->> pipelines over arrays, IF/DO/DO WHILE/EXIT/CYCLE, CALL with
;; intent(inout)/(out), PRINT.
(require '[clojure.string :as str])

(def ^:dynamic *rnd* nil)
(defn- r [n] (.nextInt *rnd* n))
(defn- pick [xs] (nth xs (r (count xs))))
(defn- chance [n] (zero? (r n)))

(def ikind? #{:int1 :int2 :int4 :int8})
(def rkind? #{:real4 :real8})
(def ckind? #{:complex4 :complex8})
(def kbits {:int1 8 :int2 16 :int4 32 :int8 64 :real4 32 :real8 64})
(def kpart {:complex4 :real4 :complex8 :real8})
(def kn {:int1 1 :int2 2 :int4 4 :int8 8 :real4 4 :real8 8 :complex4 4 :complex8 8})
(def imax {:int1 127 :int2 32767 :int4 2147483647 :int8 9.0e18})
(def mant {:real4 24 :real8 53})

(defn promote [a b]
  (cond (or (ckind? a) (ckind? b))
        (let [p (fn [k] (cond (ckind? k) (kpart k) (rkind? k) k)) ps (remove nil? [(p a) (p b)])]
          ({:real4 :complex4 :real8 :complex8} (reduce #(if (>= (kbits %1) (kbits %2)) %1 %2) ps)))
        (and (ikind? a) (ikind? b)) (if (>= (kbits a) (kbits b)) a b)
        (and (rkind? a) (rkind? b)) (if (>= (kbits a) (kbits b)) a b)
        (ikind? a) b :else a))

(defn- part-k [k] (if (ckind? k) (kpart k) k))
(defn- exact-in?
  "Is every value of bound b and granularity q exact in the real kind k?"
  [k b q] (and q (< (* b (Math/pow 2 q)) (Math/pow 2 (- (mant k) 1)))))

;; an expression: {:s text :k kind :b bound :q granularity}
(defn- atom? [e] (re-matches #"[a-z0-9_]+(\([^()]*\))?|\d+(\.\d*)?(_\d|d0)?" (:s e)))
(defn- paren [e] (if (atom? e) (:s e) (str "(" (:s e) ")")))

(def scalars {"b1" :int1 "h2" :int2 "i" :int4 "j" :int4 "k" :int4 "m8" :int8 "s" :real4 "x" :real8 "y" :real8 "z" :complex4 "w" :complex8})
(def bound {:int1 100 :int2 1000 :int4 1000 :int8 1000000 :real4 100 :real8 100 :complex4 100 :complex8 100})
(defn- var-e [n] (let [k (scalars n)] {:s n :k k :b (bound k) :q (when (ckind? k) 0) :var n}))

(defn- sfx [k] (case k :int4 "" :real4 "" (str "_" (kn k))))
(defn- ilit [k v] (let [t (str (Math/abs (long v)) (sfx k))] {:s (if (neg? v) (str "(-" t ")") t) :k k :b (Math/abs (long v)) :q 0}))
(defn- rlit [k text v q] {:s (str text (sfx k)) :k k :b (Math/abs (double v)) :q q})

(defn- literal []
  (case (r 6)
    (0 1) (ilit (pick [:int4 :int4 :int1 :int2 :int8]) (- (r 41) 20))
    2 (let [[t v q] (pick [["0.5" 0.5 1] ["1.25" 1.25 2] ["3.0" 3.0 0] ["0.1" 0.1 nil] ["2.5" 2.5 1] ["7.0" 7.0 0]])] (rlit :real4 t v q))
    3 (let [[t v q] (pick [["0.5d0" 0.5 1] ["1.25d0" 1.25 2] ["0.1d0" 0.1 nil] ["3.0d0" 3.0 0] ["0.375d0" 0.375 3]])] {:s t :k :real8 :b v :q q})
    4 (pick [{:s "(1.0, 2.0)" :k :complex4 :b 2 :q 0} {:s "(0.5_8, -1)" :k :complex8 :b 1 :q 1} {:s "(3, 4)" :k :complex4 :b 4 :q 0}])
    5 (ilit :int4 (inc (r 9)))))

(declare num-e int-e real-e)

(defn- arr-e [env]
  (pick [{:s (str "ia(" (pick ["1" "5" "modulo(i, 5) + 1" "3"]) ")") :k :int4 :b 1000 :q 0}
         {:s (str "ra(" (pick ["0" "4" "modulo(j, 5)" "2"]) ")") :k :real8 :b 100 :q nil}
         {:s (str "sa(" (pick ["1" "3" "modulo(k, 3) + 1"]) ")") :k :real4 :b 100 :q nil}]))

(defn- leaf [env]
  (case (r 5)
    (0 1) (var-e (pick (keys scalars)))
    2 (literal)
    3 (arr-e env)
    4 (if-let [vs (seq (filter #(#{:int1 :int2 :int4 :int8 :real4 :real8 :complex4 :complex8} (:k %)) (:vals env)))]
        (pick vs) (literal))))

(defn- conv-int
  "e as an integer of kind k, |value| <= 1000 (mod first, in e's own kind)."
  [e k]
  (let [m (min 1000 (dec (long (imax k))) (if (ikind? (:k e)) (dec (long (imax (:k e)))) 1000))
        inner (cond (ikind? (:k e)) (str "mod(" (:s e) ", " m (sfx (:k e)) ")")
                    (rkind? (:k e)) (str "mod(" (:s e) ", " m ".0" (sfx (:k e)) ")")
                    :else (str "mod(real(" (:s e) "), " m ".0" (sfx (kpart (:k e))) ")"))]
    {:s (str "int(" inner ", " (kn k) ")") :k k :b m :q 0}))

(defn- conv-real [e k]
  (let [inner (cond (ckind? (:k e)) (str "real(" (:s e) ", " (kn k) ")") :else (str "real(" (:s e) ", " (kn k) ")"))]
    ;; + 0.0 turns a -0.0 into 0.0 (max, min and sign of a signed zero are the processor's); an integer has none
    {:s (if (ikind? (:k e)) inner (str inner " + 0.0" (sfx k))) :k k :b (:b e) :q (when (exact-in? k (:b e) (:q e)) (:q e))}))

(defn- too-big? [e]
  (let [k (:k e)]
    (or (and (ikind? k) (> (:b e) (imax k))) (> (:b e) 1.0e7))))

(defn- binop [env d]
  (let [a (num-e env (dec d)) b (num-e env (dec d)) o (pick ["+" "-" "*" "/" "**"])
        k (promote (:k a) (:k b))
        q2 (fn [f] (when (and (:q a) (:q b)) (f (:q a) (:q b))))]
    (case o
      ("+" "-") (let [e {:s (str (paren a) " " o " " (paren b)) :k k :b (+ (:b a) (:b b)) :q (q2 max)}]
                  (when-not (and (rkind? (part-k k)) (:q e) (not (exact-in? (part-k k) (:b e) (:q e)))) e))
      "*" (let [e {:s (str (paren a) " * " (paren b)) :k k :b (* (:b a) (:b b)) :q (q2 +)}]
            (cond (ckind? k) (when (and (:q e) (exact-in? (kpart k) (* 2 (:b e)) (:q e))) e)
                  :else (update e :q #(when (and % (or (ikind? k) (exact-in? k (:b e) %))) %))))
      "/" (when-not (ckind? k)
            (let [lit (pick [(ilit (:k a) (pick [2 3 5 -7])) (rlit (if (rkind? (:k a)) (:k a) :real8) (pick ["2.0" "4.0" "0.5"]) 2.0 nil)])
                  k (promote (:k a) (:k lit))]
              {:s (str (paren a) " / " (paren lit)) :k k :b (:b a) :q nil}))
      "**" (cond (ikind? (:k a)) (let [n (r 4)] {:s (str (paren a) " ** " n) :k (promote (:k a) :int4) :b (Math/pow (max 1 (:b a)) n) :q 0})
                 (rkind? (:k a)) {:s (str (paren a) " ** 2") :k (:k a) :b (* (:b a) (:b a)) :q (when (:q a) (* 2 (:q a)))}
                 :else nil))))

(defn- intrinsic [env d]
  (let [e (num-e env (dec d)) k (:k e)]
    (case (r 14)
      0 (when-not (ckind? k) (assoc e :s (str "abs(" (:s e) ")")))
      1 (when-not (ckind? k) (let [m (if (ikind? k) (str "7" (sfx k)) (str "7.0" (sfx k)))]
                               {:s (str (pick ["mod" "modulo"]) "(" (:s e) ", " m ")") :k k :b 7 :q (:q e)}))
      2 (let [kk (pick [:int1 :int2 :int4 :int8])] (conv-int e kk))
      3 (when (rkind? k) (let [kk (pick [:int4 :int8 :int2])]
                           {:s (str (pick ["nint" "floor" "ceiling" "int"]) "(mod(" (:s e) ", 1000.0" (sfx k) "), " (kn kk) ")") :k kk :b 1000 :q 0}))
      4 (conv-real e (pick [:real4 :real8]))
      5 (when-not (ckind? k) {:s (str "dble(" (:s e) ")") :k :real8 :b (:b e) :q (:q e)})
      6 (let [a (conv-int e :int4) b (conv-int (num-e env (dec d)) :int2) ck (pick [:complex4 :complex8])]
          {:s (str "cmplx(" (:s a) ", " (:s b) ", " (kn ck) ")") :k ck :b 1000 :q 0})
      7 (when (ckind? k) (pick [{:s (str "conjg(" (:s e) ")") :k k :b (:b e) :q (:q e)}
                               {:s (str "aimag(" (:s e) ")") :k (kpart k) :b (:b e) :q (:q e)}
                               {:s (str "real(" (:s e) ")") :k (kpart k) :b (:b e) :q (:q e)}]))
      8 (when (rkind? k) {:s (str "sqrt(abs(" (:s e) "))") :k k :b (inc (Math/sqrt (:b e))) :q nil})
      9 (let [kk (pick [:int1 :int2 :int4 :int8 :real4 :real8])
                f (pick ["min" "max"]) a (if (ikind? kk) (conv-int e kk) (conv-real e kk))
                b (let [e2 (num-e env (dec d))] (if (ikind? kk) (conv-int e2 kk) (conv-real e2 kk)))]
            {:s (str f "(" (:s a) ", " (:s b) ")") :k kk :b (max (:b a) (:b b)) :q (when (and (:q a) (:q b)) (max (:q a) (:q b)))})
      10 (let [kk (pick [:int1 :int2 :int4 :int8]) a (conv-int e kk) b (conv-int (num-e env (dec d)) kk)]
           {:s (str "sign(" (:s a) ", " (:s b) ")") :k kk :b (:b a) :q 0})
      11 (pick [{:s "sum(ia)" :k :int4 :b 5000 :q 0} {:s "maxval(ra)" :k :real8 :b 100 :q nil} {:s "minval(sa)" :k :real4 :b 100 :q nil}
                {:s "size(ra)" :k :int4 :b 5 :q 0} {:s "product(sa(1:1))" :k :real4 :b 100 :q nil}])
      12 (pick [{:s "(->> ra map(fr) sum)" :k :real8 :b 500 :q nil}
                {:s "(->> ia map(fi) filter(ipos) sum)" :k :int4 :b 500 :q 0}
                {:s "(->> sa map(fs) maxval)" :k :real4 :b 51 :q nil}
                {:s "(->> ia filter(ipos) map(fi) sum)" :k :int4 :b 500 :q 0}
                ;; not a filter over reals into sum: an empty one differs (test/fortran-cases/empty_sum.lms)
                {:s "(->> ia map(fi) filter(fl) sum)" :k :int4 :b 500 :q 0}])
      13 (pick [{:s (str "fi(" (:s (conv-int e :int4)) ")") :k :int4 :b 96 :q 0}
                {:s (str "fr(" (:s (conv-real e :real8)) ")") :k :real8 :b 100 :q nil}
                {:s (str "fk(" (:s (conv-int e :int2)) ")") :k :int8 :b 1000000 :q 0}
                {:s (str "fs(" (:s (conv-real e :real4)) ")") :k :real4 :b 51 :q nil}
                {:s (str "kind(" (:s e) ")") :k :int4 :b 8 :q 0}
                {:s (str "digits(" (:s (conv-int e :int2)) ")") :k :int4 :b 64 :q 0}]))))

(defn num-e
  "A numeric expression of some kind."
  [env d]
  (loop [tries 0]
    (let [e (if (or (<= d 0) (> tries 6)) (leaf env)
                (case (r 6) (0 1) (leaf env) (2 3) (binop env d) 4 (intrinsic env d)
                      5 (let [a (num-e env (dec d))] (assoc a :s (str "-" (paren a))))))]
      (if (or (nil? e) (too-big? e) (and (= "product(sa(1:1))" (:s e)))) (recur (inc tries)) e))))

(defn- logic-e [env d]
  (case (r (if (pos? d) 7 4))
    0 (let [a (num-e env 1) b (num-e env 1) cx (or (ckind? (:k a)) (ckind? (:k b)))]
        {:s (str (paren a) " " (if cx (pick ["==" "/="]) (pick ["<" "<=" ">" ">=" "==" "/=" ".lt." ".ge."])) " " (paren b))})
    1 {:s (pick ["p" "q"])}
    2 {:s (str "t " (pick ["==" "<" ">=" "/="]) " " (pick ["'ab'" "'abc'" "'b'" "''" "'ab      '"]))}
    3 (if-let [vs (seq (filter #(= :logical (:k %)) (:vals env)))] (pick vs) {:s (pick [".true." ".false."])})
    4 {:s (str "(" (:s (logic-e env (dec d))) ") " (pick [".and." ".or." ".eqv." ".neqv."]) " (" (:s (logic-e env (dec d))) ")")}
    5 {:s (str ".not. (" (:s (logic-e env (dec d))) ")")}
    6 {:s (str "fl(" (:s (conv-int (num-e env 1) :int4)) ")")}))

(defn- char-e [env]
  (case (r 6)
    0 {:s (pick ["'ab'" "'xyz'" "''" "'hello world'" "'it''s'"])}
    1 {:s "t"}
    2 {:s (str "trim(t) // " (pick ["'!'" "'ab'" "t"]))}
    3 {:s "adjustl(t)"}
    4 {:s (str "'<' // t // '>'")}
    5 (if-let [vs (seq (filter #(= :char (:k %)) (:vals env)))] (pick vs) {:s "t"})))

(defn- assign-to [env n e]
  (let [k (scalars n)]
    (cond (ikind? k) (:s (conv-int e k))
          (rkind? k) (let [inner (cond (ikind? (:k e)) (str "mod(" (:s e) ", 100" (sfx (:k e)) ")")
                                       (rkind? (:k e)) (str "mod(" (:s e) ", 100.0" (sfx (:k e)) ") + 0.0" (sfx (:k e)))
                                       :else (str "mod(real(" (:s e) "), 100.0" (sfx (kpart (:k e))) ")"))]
                       inner)
          :else (let [b (num-e env 1)]
                  (str "cmplx(" (:s (conv-int e :int4)) ", " (:s (conv-int b :int1)) ", " (kn k) ")")))))

(defn- ind [d] (apply str (repeat (* 2 d) " ")))
(def ^:dynamic *val-n* nil)

(declare block)

(defn- print-item [env]
  (case (r 9)
    (0 1 2) (:s (num-e env 2))
    3 (:s (logic-e env 1))
    4 (:s (char-e env))
    5 (pick ["ia" "ra" "sa" "b1" "h2" "m8" "z" "w" "s" "t"])
    6 (pick ["huge(b1)" "huge(h2)" "epsilon(s)" "tiny(x)" "huge(m8)" "epsilon(1.0d0)" "digits(x)"])
    7 (if-let [vs (seq (:vals env))] (:s (pick vs)) "i")
    8 (pick ["len(t)" "len_trim(t)" "merge(i, j, p)" "merge(t, 'zzzzzzzz', q)"])))

(defn- stmt
  "[text env]: one statement at depth d (busy: the active DO variables, never assigned)."
  [env d k loop?]
  (let [I (ind k) busy (:busy env)
        free (remove busy ["i" "j" "k"])
        target (fn [] (pick (remove busy (keys scalars))))]
    (case (r (if (pos? d) 17 11))
      (0 1 2) (let [n (target) e (num-e env 2)] [(str I n " = " (assign-to env n e)) env])
      3 [(str I "ia(" (pick ["1" "modulo(i, 5) + 1" "5"]) ") = " (:s (conv-int (num-e env 2) :int4))) env]
      4 [(str I "ra(" (pick ["0" "modulo(j, 5)" "4"]) ") = mod(" (:s (conv-real (num-e env 2) :real8)) ", 100.0d0) + 0.0d0") env]
      5 [(str I (pick ["p" "q"]) " = " (:s (logic-e env 2))) env]
      6 [(str I "t = " (:s (char-e env))) env]
      7 [(str I "print *, " (str/join ", " (repeatedly (inc (r 4)) #(print-item env)))) env]
      8 (let [nm (str "v" (swap! *val-n* inc))
                [e kind] (case (r 4) (0 1) (let [e (num-e env 2)] [e (:k e)]) 2 [(logic-e env 1) :logical] 3 [(char-e env) :char])]
            [(str I "val " nm " = " (:s e)) (update env :vals conj (assoc (dissoc e :var) :s nm :k kind))])
      9 (if loop? [(str I "if (" (:s (logic-e env 1)) ") " (pick ["exit" "cycle"])) env]
            (let [u (pick ["i" "j" "k"]) vs (remove (conj busy u) ["i" "j" "k"])]
              (if (seq vs) [(str I "call sb(" u ", " (pick vs) ", " (pick ["x" "y"]) ")") env] [(str I "continue") env])))
      10 (let [n (first (remove busy ["k" "j" "i"]))]
           (if n [(str I "call sc(" (pick ["w" "z"]) ", " (pick ["b1" "3_1"]) ", " n ")") env]
               [(str I "continue") env]))
      (11 12) (let [c (logic-e env 2)]
                [(str I "if (" (:s c) ") then\n" (block env (dec d) (inc k) loop?)
                      (when (chance 2) (str I "else if (" (:s (logic-e env 1)) ") then\n" (block env (dec d) (inc k) loop?)))
                      (when (chance 2) (str I "else\n" (block env (dec d) (inc k) loop?)))
                      I "end if") env])
      (13 14) (if-let [v (first (shuffle free))]
                (let [a (- (r 9) 3) b (- (r 13) 3) st (pick ["" ", 2" ", -1" ", 3" ", -2"])]
                  [(str I "do " v " = " a ", " b st "\n" (block (update env :busy conj v) (dec d) (inc k) true)
                        I "end do\n" I "print *, " v) env])
                [(str I "continue") env])
      15 (if (busy "nw") [(str I "continue") env] [(str I "nw = 0\n" I "do while (nw < " (inc (r 5)) ")\n" I "  nw = nw + 1\n"
               (block (update env :busy conj "nw") (dec d) (inc k) false) I "end do") env])
      16 [(str I "do\n" (block env (dec d) (inc k) false) I "  if (" (:s (logic-e env 1)) ") exit\n" I "  exit\n" I "end do") env])))

(defn block [env d k loop?]
  (loop [n (inc (r 4)) env env out []]
    (if (zero? n) (str/join (map #(str % "\n") out))
        (let [[s env2] (stmt env d k loop?)] (recur (dec n) env2 (conj out s))))))

(def ^:private procs
  (str "  pure integer function fi(u)\n    integer, intent(in) :: u\n    fi = mod(u * 3 + 1, 97)\n  end function fi\n"
       "  pure real(8) function fr(t)\n    real(8), intent(in) :: t\n    fr = mod(t * 0.5d0 + 1.0d0, 100.0d0) + 0.0d0\n  end function fr\n"
       "  pure integer(8) function fk(v)\n    integer(2), intent(in) :: v\n    fk = int(v, 8) * 1000_8\n  end function fk\n"
       "  pure real function fs(r)\n    real, intent(in) :: r\n    fs = mod(r, 100.0) * 0.5 + 1.0\n  end function fs\n"
       "  pure logical function ipos(u)\n    integer, intent(in) :: u\n    ipos = u > 0\n  end function ipos\n"
       "  pure logical function rpos(t)\n    real(8), intent(in) :: t\n    rpos = t > 0.0d0\n  end function rpos\n"
       "  pure logical function fl(u)\n    integer, intent(in) :: u\n    fl = mod(u, 3) == 0\n  end function fl\n"
       "  subroutine sb(u, v, t)\n    integer, intent(in) :: u\n    integer, intent(inout) :: v\n    real(8), intent(out) :: t\n"
       "    v = mod(v + u, 97)\n    t = 0.5d0 * u\n  end subroutine sb\n"
       "  subroutine sc(c, n, m)\n    complex(8), intent(inout) :: c\n    integer(1), intent(in) :: n\n    integer, intent(out) :: m\n"
       "    c = cmplx(mod(int(real(c)) + n, 100), mod(int(aimag(c)) - n, 100), 8)\n    m = int(n) * 2\n  end subroutine sc\n"))

(defn gen-program [nm seed]
  (binding [*rnd* (java.util.Random. seed) *val-n* (atom 0)]
    (let [body (block {:busy #{} :vals []} 3 2 false)
          body (str/replace body #"call sc\((w|z), " (fn [[_ v]] (str "call sc(" (if (= v "z") "w" v) ", ")))]
      (str "module " nm "\n  implicit none\ncontains\n" procs
           "  subroutine run()\n"
           "    integer(1) :: b1\n    integer(2) :: h2\n    integer :: i, j, k, nw\n    integer(8) :: m8\n"
           "    real :: s\n    real(8) :: x, y\n    complex :: z\n    complex(8) :: w\n    logical :: p, q\n    character(len=8) :: t\n"
           "    integer :: ia(5)\n    real(8) :: ra(0:4)\n    real :: sa(3)\n"
           "    b1 = 5_1; h2 = -300_2; i = 1; j = 2; k = 3; nw = 0; m8 = 77_8\n"
           "    s = 0.25; x = 0.5d0; y = -1.5d0; z = (1.0, -2.0); w = (3.0d0, 0.5d0)\n"
           "    p = .true.; q = .false.; t = 'lemmis'\n"
           "    ia(1) = 1; ia(2) = -2; ia(3) = 3; ia(4) = 4; ia(5) = -5\n"
           "    ra(0) = 0.5d0; ra(1) = -1.0d0; ra(2) = 2.25d0; ra(3) = 3.0d0; ra(4) = -4.5d0\n"
           "    sa(1) = 1.5; sa(2) = -0.25; sa(3) = 2.0\n"
           body
           "    print *, b1, h2, i, j, k, m8, s, x, y, z, w, p, q, t\n    print *, ia, ra, sa\n"
           "  end subroutine run\nend module " nm "\n"))))
