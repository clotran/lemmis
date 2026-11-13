#!/usr/bin/env bb
;; fuzz.bb [seed] [count] (from model/, the books certified): random programs
;; of the subset run by fmean's fortran-run and compiled by gfortran and
;; flang; each line printed must agree, token by token, a real by its value
;; (fmatch.clj, as check-fsem.bb compares). A program is a module (a derived
;; type, an integer and a real function, a subroutine with INTENT IN, INOUT
;; and OUT) and a main program with an internal subroutine; its statements:
;; assignment to integer, real(8), real(4), logical, character and
;; structure-component variables, an integer array's elements and a
;; substring; DO (a step, EXIT, CYCLE), DO WHILE, IF constructs, SELECT CASE,
;; CALL, PRINT *; + - * /, MOD, MODULO, MIN, MAX, ABS, SIGN, SQRT, REAL, INT,
;; NINT, FLOOR, LEN_TRIM, TRIM, //, substrings, the relations and logical
;; operators. Values stay small (an integer assignment reduces MOD 97, a real
;; one MOD 100, a divisor is a nonzero literal, a function's arguments are
;; atoms), so nothing overflows and every real is finite. A program the model
;; or a compiler disagrees on is kept in ../build/fuzz/ as a regression case.
;; A program whose run turns on a processor-dependent value (the model stops
;; with :pd, e.g. at a test of a real MOD's zero) is counted, not compared.
;; Exit 1 on any disagreement.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(load-file (str here "/fmatch.clj"))
(def acl2 (or (System/getenv "ACL2") (str (fs/parent (fs/parent here)) "/acl2/saved_acl2")))
(def seed (parse-long (or (first *command-line-args*) "1")))
(def n (parse-long (or (second *command-line-args*) "20")))
(def rnd (java.util.Random. seed))
(defn r [k] (.nextInt rnd k))
(defn pick [xs] (nth xs (r (count xs))))
(defn shuf [xs] (let [l (java.util.ArrayList. xs)] (java.util.Collections/shuffle l rnd) (vec l)))

;; an environment: :i integer names read, :x real names, :v the array (or not)
(def main-env {:i ["a" "b" "c" "d" "q%x" "q%y"] :x ["x" "y" "s"] :v true :c true :f true :p true})
(declare iexp rexp)
(defn lit [] (let [k (- (r 41) 20)] (if (neg? k) (str "(" k ")") (str k))))
(defn rlit [] (pick ["0.5d0" "1.25d0" "0.1d0" "3.0d0" "(-2.5d0)" "0.3d0" "7.0d0"]))
(defn slit [] (pick ["1.5" "(-0.1)" "0.3" "2.0"]))   ; real(4)
(defn cvar [] (pick ["c1" "c2"]))
(defn idx [env lv] (if (zero? (r 2)) (str (inc (r 5))) (str "modulo(" (pick (concat (:i env) lv)) ", 5) + 1")))
(defn iatom [env lv]
  (let [k (r 10)]
    (cond (< k 3) (lit)
          (and (< k 4) (:v env)) (str "v(" (idx env lv) ")")
          (and (< k 5) (:c env)) (str "len_trim(" (cvar) ")")
          (and (< k 6) (seq (:x env))) (str (pick ["int" "nint" "floor"]) "(" (pick (:x env)) ")")
          :else (let [ns (concat (:i env) lv)] (if (seq ns) (pick ns) (lit))))))
(defn iexp [env lv d]
  (if (or (<= d 0) (< (r 10) 3)) (iatom env lv)
    (let [x #(iexp env lv (dec d))]
      (case (r 10)
        (0 1 2) (str "(" (x) " " (pick ["+" "-" "*"]) " " (x) ")")
        3 (str "(" (x) " / " (pick ["3" "(-2)" "7"]) ")")
        4 (str (pick ["mod" "modulo"]) "(" (x) ", " (pick ["5" "(-4)" "11"]) ")")
        5 (str (pick ["min" "max"]) "(" (x) ", " (x) ")")
        6 (str "abs(" (x) ")")
        7 (str "sign" "(" (x) ", " (x) ")")
        8 (if (:f env) (str "f1(" (iatom env lv) ", " (iatom env lv) ")") (x))
        9 (str "(-" (x) ")")))))
(defn ratom [env lv]
  (case (r 5) (0 1) (rlit) 2 (str "dble(" (iatom env lv) ")") (if (seq (:x env)) (str/replace (pick (:x env)) #"^s$" "dble(s)") (rlit))))
(defn rexp [env lv d]
  (if (or (<= d 0) (< (r 10) 3)) (ratom env lv)
    (let [x #(rexp env lv (dec d))]
      (case (r 9)
        (0 1 2) (str "(" (x) " " (pick ["+" "-" "*"]) " " (x) ")")
        3 (str "(" (x) " / " (pick ["3.0d0" "(-0.7d0)" "10.0d0" "4.0d0"]) ")")
        4 (str (pick ["min" "max"]) "(" (x) ", " (x) ")")
        5 (str "abs(" (x) ")")
        6 (str "sqrt(abs(" (x) "))")
        7 (if (:f env) (str "g1(dble(" (ratom env lv) "))") (x))
        8 (str "(-" (x) ")")))))
(defn clit [] (str "'" (apply str (repeatedly (r 5) #(pick "abcz XY"))) "'"))
(defn sub [] (let [i (inc (r 6)) j (+ i (r (- 7 i)))] (str (cvar) "(" i ":" j ")")))
(defn cexp [d]
  (if (or (<= d 0) (< (r 10) 4)) (case (r 3) 0 (clit) 1 (cvar) 2 (sub))
    (str (if (zero? (r 2)) (str "trim(" (cexp (dec d)) ")") (cexp (dec d))) " // " (cexp (dec d)))))
(def rel ["<" "<=" "==" "/=" ">" ">="])
(defn lexp [env lv d]
  (if (or (<= d 0) (< (r 10) 6))
    (case (r 7) 0 (if (:p env) "p" ".true.") 1 (pick [".true." ".false."])
      2 (str (rexp env lv 1) " " (pick rel) " " (rexp env lv 1))
      3 (if (:c env) (str (cexp 1) " " (pick rel) " " (cexp 1)) ".false.")
      (str (iexp env lv 1) " " (pick rel) " " (iexp env lv 1)))
    (case (r 3) 0 (str "(.not. " (lexp env lv (dec d)) ")")
      (str "(" (lexp env lv (dec d)) " " (pick [".and." ".or." ".eqv." ".neqv."]) " " (lexp env lv (dec d)) ")"))))

(def ivars ["a" "b" "c" "d"])   ; variables an actual argument may be that the procedure defines
(declare stmts)
(defn case-block [env lv in pad]
  (let [k1 (- (r 60) 30) k2 (+ k1 1 (r 20)) ind (str pad "  ")
        arms [(str "case (:" k1 ")") (str "case (" (inc k1) ":" k2 ")") (str "case (" (+ k2 1) ", " (+ k2 3) ")") "case default"]]
    (concat [(str pad "select case (" (iexp env lv 2) ")")]
            (mapcat (fn [a] (cons (str pad a) (stmts env lv in ind 1))) (filter (fn [_] (pos? (r 3))) (shuf arms)))
            [(str pad "end select")])))
(defn stmt [env lv in pad]
  (let [x (r 22) ind (str pad "  ")
        imod #(str "mod(" (iexp env lv 2) ", 97)")]
    (cond
      (< x 4) [(str pad (pick (:i env)) " = " (imod))]
      (< x 5) [(str pad "v(" (idx env lv) ") = " (imod))]
      (< x 7) [(str pad (pick (:x env)) " = mod(" (rexp env lv 2) ", 100.0d0)")]
      (< x 8) [(str pad "p = " (lexp env lv 2))]
      (< x 9) [(str pad (pick ["c1" "c2" (sub)]) " = " (cexp 2))]
      (< x 10) [(str pad "print *, " (iexp env lv 2) ", " (lexp env lv 1))]
      (< x 11) [(str pad "print *, " (rexp env lv 2) ", " (cexp 1) ", " (iexp env lv 1))]
      (< x 12) (let [[q2 r2] (take 2 (shuf ivars))
                     p1 (pick (concat (remove #{q2 r2} (:i env)) lv [(lit)]))]
                 [(str pad "call s1(" p1 ", " q2 ", " r2 ")")])
      (< x 13) [(str pad "call t1(" (pick ["a" "b"]) ")")]
      (and (< x 15) (< (count lv) 2))
      (let [v (if (empty? lv) "i" "j") lo (- (r 7) 3) hi (- (r 9) 2)]
        (concat [(str pad "do " v " = " lo ", " hi (when (zero? (r 3)) (str ", " (pick ["2" "-1" "3"]))))]
                (stmts env (conj lv v) true ind 3) [(str pad "end do")]))
      (and (< x 16) (not (some #{"w"} lv)))     ; w counts, first thing in the body, so CYCLE can't spin
      (concat [(str pad "w = 0") (str pad "do while (w < " (r 5) " .and. " (lexp env lv 1) ")") (str ind "w = w + 1")]
              (stmts env (conj lv "w") true ind 3) [(str pad "end do")])
      (< x 17) (case-block env lv in pad)
      (and in (< x 19)) [(str pad "if (" (lexp env lv 1) ") " (pick ["exit" "cycle"]))]
      :else (concat [(str pad "if (" (lexp env lv 2) ") then")] (stmts env lv in ind 2)
                    (when (zero? (r 2)) (cons (str pad "else") (stmts env lv in ind 2))) [(str pad "end if")]))))
(defn stmts [env lv in pad k] (vec (mapcat (fn [_] (stmt env lv in pad)) (range (inc (r k))))))

(defn program []
  (let [fe {:i ["m" "k"] :x []} ge {:i [] :x ["u"]} te {:i ["k" "c" "d"] :x []}]
    (str/join "\n"
      (concat ["module fzm" "  implicit none" "  type pt" "    integer :: x, y" "  end type pt" "contains"
               "  integer function f1(m, k)" "    integer, intent(in) :: m, k"
               (str "    f1 = mod(" (iexp fe [] 2) ", 97)")
               (str "    if (" (lexp fe [] 1) ") f1 = " (iexp fe [] 1)) "  end function f1"
               "  real(8) function g1(u)" "    real(8), intent(in) :: u"
               (str "    g1 = mod(" (rexp ge [] 2) ", 100.0d0)") "  end function g1"
               "  subroutine s1(m, k, n)" "    integer, intent(in) :: m" "    integer, intent(inout) :: k" "    integer, intent(out) :: n"
               (str "    k = mod(" (iexp fe [] 2) ", 97)") (str "    n = mod(" (iexp fe [] 2) ", 97)") "  end subroutine s1"
               "end module fzm"
               "program fz" "  use fzm" "  implicit none" "  integer :: a, b, c, d, i, j, w" "  integer :: v(5)" "  logical :: p"
               "  real(8) :: x, y" "  real :: s" "  character(len=6) :: c1, c2" "  type(pt) :: q"
               (str "  a = " (lit)) (str "  b = " (lit)) (str "  c = " (lit)) (str "  d = " (lit))
               "  i = 0" "  j = 0" "  w = 0" (str "  v = " (lit)) "  p = .false." (str "  x = " (rlit)) (str "  y = " (rlit)) (str "  s = " (slit))
               (str "  c1 = " (clit)) (str "  c2 = " (clit)) (str "  q = pt(" (lit) ", " (lit) ")")]
              (stmts main-env [] false "  " 8)
              ["  print *, a, b, c, d, i, j, w, p" "  print *, v" "  print *, x, y, s" "  print *, c1, c2, len_trim(c1), len_trim(c2)" "  print *, q"
               "contains" "  subroutine t1(k)" "    integer, intent(inout) :: k" (str "    k = mod(" (iexp te [] 2) ", 97)") "  end subroutine t1"
               "end program fz" ""]))))

(defn sh! [secs opts & cmd]
  (let [proc (apply p/process (merge {:out :string :err :string} opts) cmd) res (deref proc (* 1000 secs) ::timeout)]
    (if (= res ::timeout) (do (p/destroy-tree proc) {:exit 124 :out "" :err "deadline"}) res)))
(defn lisp-str [s] (str "\"" (-> s (str/replace "\\" "\\\\") (str/replace "\"" "\\\"")) "\""))

(defn short-program [] (first (filter #(every? (fn [l] (<= (count l) 132)) (str/split-lines %)) (repeatedly program)))) ; 6.3.2.1: 132 characters a line
(def progs (vec (repeatedly n short-program)))
(def work (str (fs/create-temp-dir {:prefix "fuzz"})))
(def keep-dir (str (fs/parent here) "/build/fuzz"))
(def model
  (let [in (str "(include-book \"frun\")\n(set-iprint nil)\n(set-fmt-hard-right-margin 100000 state)\n(set-fmt-soft-right-margin 100000 state)\n"
                "(defun show-toks (ts) (declare (xargs :mode :program)) (if (endp ts) \"\" (concatenate 'string \" \" (car ts) (show-toks (cdr ts)))))\n"
                "(defun show-lines (ls) (declare (xargs :mode :program)) (if (endp ls) nil (prog2$ (cw \"LINE~s0~%\" (show-toks (car ls))) (show-lines (cdr ls)))))\n"
                (str/join (for [t progs] (str "(let ((r (fortran-run " (lisp-str t) " 100000000)))\n"
                                              "  (prog2$ (cw \"~%PROG~%STATUS ~x0~%\" (car r)) (if (consp (car r)) (cw \"AT ~x0~%\" (cadr r)) (show-lines (cadr r)))))\n")))
                "(good-bye)\n")
        res (sh! 1200 {:dir here :in in} "nice" acl2)]
    (mapv (fn [b] {:status (second (re-find #"STATUS (.*)" b)) :at (second (re-find #"AT (.*)" b))
                   :lines (vec (for [l (str/split-lines b) :let [[_ x] (re-find #"^LINE(.*)$" l)] :when x] (toks-of-line x)))})
          (rest (str/split (:out res) #"\nPROG\n")))))
(when (not= (count model) n) (println "fuzz: ACL2 answered" (count model) "of" n "programs") (System/exit 1))

(def compilers (filter #(fs/which (first %)) [["gfortran" "-std=f2018"] ["flang"]]))
(def bad (atom 0))
(def pd (atom 0))   ; a program whose run turns on a processor-dependent value: the model answers none
(doseq [[k t m] (map vector (range) progs model)]
  (let [f (str work "/fz" k ".f90")
        _ (spit f t)
        why (cond (= (:status m) "(:ERROR :PD)") (do (swap! pd inc) nil)
                  (not (#{":NORMAL" ":STOP"} (:status m))) (str "the model stops with " (:status m) " " (:at m))
                  :else (first (for [[fc & fl] compilers
                                     :let [exe (str work "/fz" k "-" fc)
                                           cr (apply sh! 180 {:dir work} "nice" fc (concat fl ["-o" exe f]))
                                           rr (when (zero? (:exit cr)) (sh! 60 {:dir work} exe))
                                           got (when rr (vec (str/split-lines (str/trimr (:out rr)))))]
                                     :when (or (nil? rr) (not= 0 (:exit rr)) (not (lines-match? (map (fn [l] (map #(if (str/starts-with? % "~") % (str/upper-case %)) l)) (:lines m)) (map str/upper-case got))))]
                                 (str fc (if rr (str " printed " got "; the model " (:lines m)) (str " did not compile: " (:err cr)))))))]
    (when why
      (swap! bad inc) (fs/create-dirs keep-dir)
      (let [kf (str keep-dir "/fz-" seed "-" k ".f90")] (spit kf t) (println "fuzz: disagree" kf why)))))
(fs/delete-tree work)
(println (format "fuzz: seed %d, %d programs, %d agreeing with the model under %s, %d processor dependent" seed n (- n @bad @pd) (str/join " and " (map first compilers)) @pd))
(System/exit (if (zero? @bad) 0 1))
