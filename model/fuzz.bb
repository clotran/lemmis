#!/usr/bin/env bb
;; fuzz.bb [seed] [count] (from model/, the books certified): random programs
;; of the subset (integer and logical scalars, an integer array, assignment,
;; DO with EXIT and CYCLE, IF constructs, PRINT *, the intrinsics MOD, MODULO,
;; MIN, MAX, ABS, SIGN, integer /) run by fmean's fortran-run and compiled
;; by gfortran and flang; each line printed must agree, token by token. Values
;; stay small (every assignment reduces MOD 97, expressions are two operators
;; deep, a divisor is a nonzero literal), so no program overflows. A program
;; the model or a compiler disagrees on is kept in ../build/fuzz/ as a
;; regression case. Exit 1 on any disagreement.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(def acl2 (or (System/getenv "ACL2") (str (fs/parent (fs/parent here)) "/acl2/saved_acl2")))
(def seed (parse-long (or (first *command-line-args*) "1")))
(def n (parse-long (or (second *command-line-args*) "20")))
(def rnd (java.util.Random. seed))
(defn r [k] (.nextInt rnd k))
(defn pick [xs] (nth xs (r (count xs))))

(def scal ["a" "b" "c" "d"])
(declare iexp)
(defn lit [] (let [k (- (r 41) 20)] (if (neg? k) (str "(" k ")") (str k))))
(defn idx [lv d] (if (zero? (r 2)) (str (inc (r 5))) (str "modulo(" (pick (concat scal lv)) ", 5) + 1")))
(defn atom* [lv d]
  (case (r 4) 0 (lit) 1 (str "v(" (idx lv d) ")") (pick (concat scal lv))))
(defn iexp [lv d]
  (if (or (<= d 0) (< (r 10) 3)) (atom* lv d)
    (let [x #(iexp lv (dec d))]
      (case (r 9)
        (0 1 2) (str "(" (x) " " (pick ["+" "-" "*"]) " " (x) ")")
        3 (str "(" (x) " / " (pick ["3" "(-2)" "7"]) ")")
        4 (str (pick ["mod" "modulo"]) "(" (x) ", " (pick ["5" "(-4)" "11"]) ")")
        5 (str (pick ["min" "max"]) "(" (x) ", " (x) ")")
        6 (str "abs(" (x) ")")
        7 (str "sign" "(" (x) ", " (x) ")")
        8 (str "(-" (x) ")")))))
(defn lexp [lv d]
  (if (or (<= d 0) (< (r 10) 6))
    (case (r 5) 0 "p" 1 (pick [".true." ".false."]) (str (iexp lv 1) " " (pick ["<" "<=" "==" "/=" ">" ">="]) " " (iexp lv 1)))
    (case (r 3) 0 (str "(.not. " (lexp lv (dec d)) ")")
      (str "(" (lexp lv (dec d)) " " (pick [".and." ".or." ".eqv." ".neqv."]) " " (lexp lv (dec d)) ")"))))

(declare stmts)
(defn stmt [lv in pad]
  (let [x (r 12) ind (str pad "  ")]
    (cond
      (< x 4) [(str pad (pick scal) " = mod(" (iexp lv 2) ", 97)")]
      (< x 5) [(str pad "v(" (idx lv 1) ") = mod(" (iexp lv 2) ", 97)")]
      (< x 6) [(str pad "p = " (lexp lv 2))]
      (< x 7) [(str pad "print *, " (iexp lv 2) ", " (lexp lv 1))]
      (and (< x 9) (< (count lv) 2))
      (let [v (if (empty? lv) "i" "j") lo (- (r 7) 3) hi (- (r 9) 2)]
        (concat [(str pad "do " v " = " lo ", " hi (when (zero? (r 3)) (str ", " (pick ["2" "-1" "3"]))))]
                (stmts (conj lv v) true ind 3) [(str pad "end do")]))
      (and in (< x 10)) [(str pad "if (" (lexp lv 1) ") " (pick ["exit" "cycle"]))]
      :else (concat [(str pad "if (" (lexp lv 2) ") then")] (stmts lv in ind 2)
                    (when (zero? (r 2)) (cons (str pad "else") (stmts lv in ind 2))) [(str pad "end if")]))))
(defn stmts [lv in pad k] (vec (mapcat (fn [_] (stmt lv in pad)) (range (inc (r k))))))

(defn program []
  (str/join "\n"
    (concat ["program fz" "  implicit none" "  integer :: a, b, c, d, i, j" "  integer :: v(5)" "  logical :: p"
             (str "  a = " (lit)) (str "  b = " (lit)) (str "  c = " (lit)) (str "  d = " (lit))
             "  i = 0" "  j = 0" (str "  v = " (lit)) "  p = .false."]
            (stmts [] false "  " 8)
            ["  print *, a, b, c, d, i, j, p" "  print *, v" "end program fz" ""])))

(defn sh! [secs opts & cmd]
  (let [proc (apply p/process (merge {:out :string :err :string} opts) cmd) res (deref proc (* 1000 secs) ::timeout)]
    (if (= res ::timeout) (do (p/destroy-tree proc) {:exit 124 :out "" :err "deadline"}) res)))
(defn lisp-str [s] (str "\"" (-> s (str/replace "\\" "\\\\") (str/replace "\"" "\\\"")) "\""))
(defn toks [l] (vec (remove str/blank? (str/split (str/trim l) #"\s+"))))

(defn short-program [] (first (filter #(every? (fn [l] (<= (count l) 132)) (str/split-lines %)) (repeatedly program)))) ; 6.3.2.1: 132 characters a line
(def progs (vec (repeatedly n short-program)))
(def work (str (fs/create-temp-dir {:prefix "fuzz"})))
(def keep-dir (str (fs/parent here) "/build/fuzz"))
(def model
  (let [in (str "(include-book \"frun\")\n(set-iprint nil)\n(set-fmt-hard-right-margin 100000 state)\n(set-fmt-soft-right-margin 100000 state)\n"
                "(defun show-toks (ts) (declare (xargs :mode :program)) (if (endp ts) \"\" (concatenate 'string \" \" (car ts) (show-toks (cdr ts)))))\n"
                "(defun show-lines (ls) (declare (xargs :mode :program)) (if (endp ls) nil (prog2$ (cw \"LINE~s0~%\" (show-toks (car ls))) (show-lines (cdr ls)))))\n"
                (str/join (for [t progs] (str "(let ((r (fortran-run " (lisp-str t) " 100000000)))\n"
                                              "  (prog2$ (cw \"~%PROG~%STATUS ~x0~%\" (car r)) (if (consp (car r)) nil (show-lines (cadr r)))))\n")))
                "(good-bye)\n")
        res (sh! 1200 {:dir here :in in} "nice" acl2)]
    (mapv (fn [b] {:status (second (re-find #"STATUS (.*)" b))
                   :lines (vec (for [l (str/split-lines b) :let [[_ x] (re-find #"^LINE(.*)$" l)] :when x] (toks x)))})
          (rest (str/split (:out res) #"\nPROG\n")))))
(when (not= (count model) n) (println "fuzz: ACL2 answered" (count model) "of" n "programs") (System/exit 1))

(def compilers (filter #(fs/which (first %)) [["gfortran" "-std=f2018"] ["flang"]]))
(def bad (atom 0))
(doseq [[k t m] (map vector (range) progs model)]
  (let [f (str work "/fz" k ".f90")
        _ (spit f t)
        why (cond (not (#{":NORMAL" ":STOP"} (:status m))) (str "the model stops with " (:status m))
                  :else (first (for [[fc & fl] compilers
                                     :let [exe (str work "/fz" k "-" fc)
                                           cr (apply sh! 180 {:dir work} "nice" fc (concat fl ["-o" exe f]))
                                           rr (when (zero? (:exit cr)) (sh! 60 {:dir work} exe))
                                           got (when rr (mapv toks (str/split-lines (str/trimr (:out rr)))))]
                                     :when (or (nil? rr) (not= 0 (:exit rr)) (not= (map #(map str/upper-case %) got) (map #(map str/upper-case %) (:lines m))))]
                                 (str fc (if rr (str " printed " got "; the model " (:lines m)) (str " did not compile: " (:err cr)))))))]
    (when why
      (swap! bad inc) (fs/create-dirs keep-dir)
      (let [kf (str keep-dir "/fz-" seed "-" k ".f90")] (spit kf t) (println "fuzz: disagree" kf why)))))
(fs/delete-tree work)
(println (format "fuzz: seed %d, %d programs, %d agreeing with the model under %s" seed n (- n @bad) (str/join " and " (map first compilers))))
(System/exit (if (zero? @bad) 0 1))
