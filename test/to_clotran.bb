#!/usr/bin/env bb
;; test/to_clotran.bb [--fuzz SEED N] [CASEDIR ...] : THE OTHER DIRECTION OF THE TWO-PATH ORACLE (PLAN.md,
;; "The require hook on the compiled path"). A clotran namespace (CASEDIR/NS.cljf, with its Lemmis modules
;; under CASEDIR) that calls Lemmis functions goes two ways:
;;   (a) interpreted: clotran -m NS, the Lemmis modules read by lemmis.reader through require;
;;   (b) pure Fortran: clotran build --pure -m NS, the calls written as calls of the Lemmis modules' Fortran
;;       (clotran.lmsface, clotran.purefort), built by gfortran and by flang, no clotran in the program;
;; and the printed values are compared one by one: integers and words as text, doubles by their bits
;; (clotran prints a double its way, the pure program the Fortran way: DEVIATIONS 50).
;; Default corpus: test/to-clotran/*/. --fuzz SEED N adds N random cases: a Lemmis module of small real(8),
;; integer(8) and logical functions and a clotran namespace of functions that call them.
;; Prints a count by kind with the first few of each; exit 1 on any kind but agree.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(def root (str (fs/parent here)))
(def clotran (or (System/getenv "CLOTRAN") "/Users/james/clotran/clotran/clotran"))
(def src-path (or (System/getenv "LEMMIS_SRC") (str root "/src")))
(def tmp (str (fs/create-temp-dir {:prefix "lemmis-toclj"})))
(defn sh [opts & args] (apply p/shell (merge {:out :string :err :string :continue true :timeout 300000} opts) args))

;; ---- the random cases
(def ^:dynamic *s* nil)
(defn r [n] (swap! *s* #(mod (+ (* % 1103515245) 12345) 2147483648)) (mod (quot @*s* 65536) n))
(defn pick [xs] (nth xs (r (count xs))))

(defn gen-expr
  "A tree: [:v name] [:k text] [:op o a b] [:call f args] over names, with calls allowed when calls is a seq of [name arity]."
  [names consts d calls]
  (cond (zero? d) (if (zero? (r 3)) [:k (pick consts)] [:v (pick names)])
        (and (seq calls) (zero? (r 3))) (let [[f n] (pick calls)] [:call f (vec (repeatedly n #(gen-expr names consts (dec d) nil)))])
        :else [:op (pick ["+" "-" "*"]) (gen-expr names consts (dec d) calls) (gen-expr names consts (dec d) calls)]))

(defn lms-text [e] (case (first e) :v (second e) :k (second e)
                     :op (str "(" (lms-text (nth e 2)) " " (second e) " " (lms-text (nth e 3)) ")")
                     :call (str (second e) "(" (str/join ", " (map lms-text (nth e 2))) ")")))
(defn clj-text [e] (case (first e) :v (second e) :k (second e)
                     :op (str "(" (second e) " " (clj-text (nth e 2)) " " (clj-text (nth e 3)) ")")
                     :call (str "(s/" (second e) " " (str/join " " (map clj-text (nth e 2))) ")")))

(defn gen-case [nm seed]
  (binding [*s* (atom (long seed))]
    (let [rconsts ["0.5" "1.25" "2.0" "3.0" "0.125"] kconsts ["1" "2" "3" "5"]
          lm-r (for [k (range 3)] (let [e (gen-expr ["x" "y"] (map #(str % "d0") (map #(str/replace % "." ".") rconsts)) 3 nil)]
                                    [(str "rf" k) e]))
          lm-r (for [[n e] lm-r] [n e])
          lm-n (for [k (range 2)] [(str "nf" k) (gen-expr ["n" "m"] (map #(str % "_8") kconsts) 2 nil)])
          lm-p (for [k (range 2)] [(str "pf" k) (pick [">" "<"]) (pick rconsts)])
          ;; the module's Fortran text
          lms (str "module " nm ".lm\n  implicit none\ncontains\n"
                   (apply str (for [[n e] lm-r] (str "  pure real(8) function " n "(x, y)\n    real(8), intent(in) :: x, y\n    " n " = " (lms-text e) "\n  end function " n "\n")))
                   (apply str (for [[n e] lm-n] (str "  pure integer(8) function " n "(n, m)\n    integer(8), intent(in) :: n, m\n    " n " = " (lms-text e) "\n  end function " n "\n")))
                   (apply str (for [[n o c] lm-p] (str "  pure logical function " n "(x)\n    real(8), intent(in) :: x\n    " n " = x " o " " c "d0\n  end function " n "\n")))
                   "end module " nm ".lm\n")
          rcalls (map (fn [[n _]] [n 2]) lm-r) ncalls (map (fn [[n _]] [n 2]) lm-n)
          cdefs (for [k (range 3)] [(str "c" k) (gen-expr ["a" "b"] rconsts 3 rcalls)])
          ddefs (for [k (range 2)] [(str "d" k) (gen-expr ["n" "m"] kconsts 2 ncalls)])
          qdefs (for [[n _ _] lm-p] [(str "q" n) n])
          cljf (str "(ns " nm "\n  (:require [" nm ".lm :as s]))\n\n"
                    (apply str (for [[n e] cdefs] (str "(defn " n " ^double [^double a ^double b] " (clj-text e) ")\n\n")))
                    (apply str (for [[n e] ddefs] (str "(defn " n " ^long [^long n ^long m] " (clj-text e) ")\n\n")))
                    (apply str (for [[n f] qdefs] (str "(defn " n " ^long [^double a] (if (s/" f " a) 1 0))\n\n")))
                    "(defn -main []\n"
                    (apply str (for [[n _] cdefs] (str "  (println \"" n "\" (" n " 1.5 -0.75) (" n " 2.0 3.0))\n")))
                    (apply str (for [[n _] ddefs] (str "  (println \"" n "\" (" n " 3 4) (" n " 7 2))\n")))
                    (apply str (for [[n _] qdefs] (str "  (println \"" n "\" (" n " 1.5) (" n " -2.0) (" n " 0.25))\n")))
                    "  (println \"end\"))\n")]
      {:lms lms :cljf cljf})))

;; ---- running a case
(defn tok= [a b]
  (or (= a b)
      (and (re-matches #"[-+0-9.eE]+" a) (re-matches #"[-+0-9.eE]+" b) (or (re-find #"[.eE]" a) (re-find #"[.eE]" b))
           (try (= (Double/doubleToRawLongBits (Double/parseDouble a)) (Double/doubleToRawLongBits (Double/parseDouble b)))
                (catch Exception _ false)))))
(defn same? [x y]
  (let [xs (str/split-lines (str/trim x)) ys (str/split-lines (str/trim y))]
    (and (= (count xs) (count ys))
         (every? (fn [[a b]] (let [ta (str/split a #"\s+") tb (str/split b #"\s+")] (and (= (count ta) (count tb)) (every? (fn [[p q]] (tok= p q)) (map vector ta tb)))))
                 (map vector xs ys)))))

(defn run-case [dir ns]
  (let [env {"CLOTRAN_PATH" (str src-path ":" dir)}
        a (sh {:extra-env env :dir dir} clotran "-m" ns)]
    (if (pos? (:exit a)) [:clotran-error (str (take 200 (str (:err a) (:out a))))]
        (let [rs (for [fc ["gfortran" "flang"]]
                   (let [exe (str dir "/exe-" fc)
                         b (sh {:extra-env (assoc env "FC" fc) :dir dir} clotran "build" "--pure" "-m" ns "-o" exe)]
                     (if (pos? (:exit b)) [:pure-build-failed (str fc ": " (str/join " | " (take 3 (str/split-lines (str (:err b) (:out b))))))]
                         (let [x (sh {:dir dir} exe)]
                           (cond (pos? (:exit x)) [:pure-run-failed (str fc ": exit " (:exit x) " " (str/trim (str (:err x))))]
                                 (not (same? (:out a) (:out x))) [:differ (str fc ": interpreted\n" (:out a) "pure\n" (:out x))]
                                 :else [:agree])))))]
          (or (first (remove #(= :agree (first %)) rs)) [:agree])))))

(let [args *command-line-args*
      fuzz (when (= "--fuzz" (first args)) [(parse-long (second args)) (parse-long (nth args 2))])
      dirs (let [given (if fuzz (drop 3 args) args)]
             (if (and (empty? given) (not fuzz)) (sort (map str (fs/list-dir (str here "/to-clotran")))) given))
      cases (concat (map (fn [d] [(str (fs/file-name d)) (str (fs/absolutize d))]) dirs)
                    (when fuzz
                      (for [i (range (second fuzz))]
                        (let [nm (str "fz" (first fuzz) "_" i) d (str tmp "/" nm)
                              {:keys [lms cljf]} (gen-case nm (+ (* 1000 (first fuzz)) i))]
                          (fs/create-dirs (str d "/" nm))
                          (spit (str d "/" nm "/lm.lms") lms)
                          (spit (str d "/" nm ".cljf") cljf)
                          [nm d]))))
      results (pmap (fn [[nm d]] [nm (run-case d nm)]) cases)
      by (group-by (comp first second) results)]
  (doseq [[k rs] (sort-by key by)]
    (println (format "%-22s %d" (name k) (count rs)))
    (doseq [[nm [_ msg]] (take 3 rs) :when msg] (println "   " nm "--" msg)))
  (println (count results) "cases," (count (get by :agree)) "agree (gfortran and flang pure builds, each against the interpreted run)")
  (fs/delete-tree tmp)
  (System/exit (if (= (set (keys by)) #{:agree}) 0 1)))
