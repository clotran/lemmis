#!/usr/bin/env bb
;; test/cases.bb [DIR] [NAME ...] : every DIR/*.lms (default test/cases) run three ways --
;; gfortran -std=f2018, flang, and clotran through lemmis.reader -- and the printed lines
;; compared token by token; a real by its value in its kind (lemmis prints ~Rk:text in test
;; mode; the compilers' layout is processor dependent, 13.10.4). A module case is driven by
;; "program; use m; call run()"; a program case runs as it is. A case whose first line is
;; "! refused: <text>" must be refused by the reader with a message containing <text>
;; (and must still compile under both compilers, so the refusal is of valid Fortran).
;; Prints a count by kind and the first failures; exit 1 on any.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(def root (str (fs/parent here)))
(def clotran (or (System/getenv "CLOTRAN") "/Users/james/clotran/clotran/clotran"))
(def args *command-line-args*)
(def case-dir (if (and (first args) (fs/directory? (first args))) (first args) (str here "/cases")))
(def only (set (if (and (first args) (fs/directory? (first args))) (rest args) args)))
(def files (sort (map #(str (fs/absolutize %)) (filter #(or (empty? only) (only (fs/file-name %))) (map str (fs/glob case-dir "*.lms"))))))
(def tmp (str (fs/create-temp-dir {:prefix "lemmis-cases"})))

(defn sh [opts & args] (apply p/shell (merge {:out :string :err :string :continue true :timeout 60000} opts) args))

(defn module-name [src] (second (re-find #"(?im)^\s*module\s+([a-z0-9_.]+)\s*$" src)))
(defn program? [src] (re-find #"(?im)^\s*program\s+" src))

(defn compile-run [fc f]
  (let [src (slurp f) base (str tmp "/" fc "-" (fs/strip-ext (fs/file-name f)))
        f90 (str base ".f90")
        drv (when-not (program? src) (str "\nprogram lemmis_driver\n  use " (module-name src) "\n  call run()\nend program lemmis_driver\n"))]
    (spit f90 (str src drv))
    (let [c (sh {:dir tmp} fc (if (= fc "gfortran") "-std=f2018" "-pedantic") "-o" base f90)]
      (if (pos? (:exit c))
        {:error (str fc " compile: " (first (str/split-lines (str (:err c) (:out c)))))}
        (let [r (sh {:dir tmp} base)]
          (if (pos? (:exit r)) {:error (str fc " run exit " (:exit r) ": " (str/trim (str (:err r))))} {:lines (str/split-lines (:out r))}))))))

;; clotran: one process for every case
(defn clotran-all []
  (let [proc (apply p/process {:env {"CLOTRAN_PATH" (or (System/getenv "LEMMIS_SRC") (str root "/src"))} :dir tmp :out :string :err :string}
                    clotran (str here "/run-lms.clj") files)
        secs (parse-long (or (System/getenv "LEMMIS_TIMEOUT") "600"))
        r (deref proc (* 1000 secs) ::timeout)
        _ (when (= r ::timeout) (p/destroy-tree proc))
        r (if (= r ::timeout) {:out (str "!!! clotran did not finish in " secs " s")} r)
        out (str/split-lines (:out r))]
    (loop [ls out cur nil acc {}]
      (if-let [l (first ls)]
        (if-let [[_ f] (re-matches #"=== (.*)" l)]
          (recur (rest ls) f (assoc acc f []))
          (recur (rest ls) cur (if cur (update acc cur conj l) acc)))
        (if (and (empty? acc) (seq files)) {:fatal (str (:out r) (:err r))} acc)))))

(defn real-of [k s]
  (let [s (str/replace s #"[dD]" "E")]
    (cond (#{"Infinity" "+Infinity" "Inf" "+Inf"} s) (if (= k 4) Float/POSITIVE_INFINITY Double/POSITIVE_INFINITY)
          (#{"-Infinity" "-Inf"} s) (if (= k 4) Float/NEGATIVE_INFINITY Double/NEGATIVE_INFINITY)
          (#{"NaN" "+NaN" "-NaN"} s) Double/NaN
          :else (try (if (= k 4) (Float/parseFloat s) (Double/parseDouble s)) (catch Exception _ nil)))))

(defn same-real? [k a b]
  (and a b (or (and (Double/isNaN (double a)) (Double/isNaN (double b)))
               (and (= a b) (= (Math/copySign 1.0 (double a)) (Math/copySign 1.0 (double b)))))))

(defn tok-match? [mine theirs]
  (if-let [[_ k v] (re-matches #"~R(\d):(.*)" mine)]
    (let [k (parse-long k)] (same-real? k (real-of k v) (real-of k theirs)))
    (if-let [[_ a b] (re-matches #"\((~R.*),(~R.*)\)" mine)]
      (let [[_ x y] (re-matches #"\((.*),(.*)\)" theirs)] (boolean (and x (tok-match? a x) (tok-match? b y))))
      (= mine theirs))))

(defn toks [l] (vec (remove str/blank? (str/split (str/trim l) #"\s+"))))
;; the two compilers against each other: the same text, or the same value read as real(4)
(defn ctok-match? [a b]
  (or (= a b)
      (let [x (real-of 4 a) y (real-of 4 b)] (boolean (and x y (same-real? 4 x y))))
      (let [[_ p q] (re-matches #"\((.*),(.*)\)" a) [_ r s] (re-matches #"\((.*),(.*)\)" b)]
        (boolean (and p r (ctok-match? p r) (ctok-match? q s))))))
;; record length is the processor's (flang wraps long records): compare the token streams
(defn all-toks [ls] (vec (mapcat toks ls)))
(defn lines-match? [ms cs] (let [x (all-toks ms) y (all-toks cs)] (and (= (count x) (count y)) (every? true? (map tok-match? x y)))))
(defn clines-match? [as bs] (let [x (all-toks as) y (all-toks bs)] (and (= (count x) (count y)) (every? true? (map ctok-match? x y)))))


(defn -main []
  (let [cl (clotran-all)
        _ (when (:fatal cl) (println "clotran failed:" (:fatal cl)) (System/exit 1))
        results (pmap (fn [f]
                        (let [src (slurp f)
                              refused (second (re-find #"^! refused: (.*)" src))
                              g (compile-run "gfortran" f) fl (compile-run "flang" f)
                              mine (get cl f)
                              err (some #(when-let [[_ m] (re-matches #"!!! (.*)" %)] m) mine)]
                          [f (cond
                               (:error g) [:compiler-error (:error g)]
                               (:error fl) [:compiler-error (:error fl)]
                               (not (clines-match? (:lines g) (:lines fl))) [:compilers-differ (str (:lines g) " vs " (:lines fl))]
                               refused (cond (nil? err) [:not-refused (str "expected a refusal containing: " refused)]
                                             (str/includes? err refused) [:refused-ok]
                                             :else [:wrong-refusal err])
                               err [:clotran-error err]
                               (lines-match? mine (:lines g)) [:agree]
                               :else [:differ (str "lemmis " mine "\n      gfortran " (:lines g))])]))
                      files)
        by (group-by (comp first second) results)]
    (doseq [[k rs] (sort-by key by)]
      (println (format "%-18s %d" (name k) (count rs)))
      (when-not (#{:agree :refused-ok} k)
        (doseq [[f [_ msg]] (take 5 rs)] (println "   " (fs/file-name f) "--" msg))))
    (println (format "%d cases, %d agree, %d refused as expected" (count files) (count (:agree by)) (count (:refused-ok by))))
    (when-let [keep (System/getenv "LEMMIS_KEEP")]
      (doseq [[f [k]] results :when (not (#{:agree :refused-ok} k))] (fs/create-dirs keep) (fs/copy f keep {:replace-existing true})))
    (fs/delete-tree tmp)
    (System/exit (if (every? #{:agree :refused-ok} (keys by)) 0 1))))

(-main)
