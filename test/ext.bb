#!/usr/bin/env bb
;; test/ext.bb : (1) the extensions: each test/ext/X.lms prints exactly what clj prints running
;; test/ext/X.clj, the same program in plain Clojure (clj is the oracle for what an extension
;; means). (2) the errors: each test/errors/X.lms starts "! error: LINE:COL: text", and the
;; reader must refuse it with "PATH:LINE:COL: ...text...". Exit 1 on any failure.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])
(def here (str (fs/parent (fs/absolutize *file*))))
(def root (str (fs/parent here)))
(def clotran (or (System/getenv "CLOTRAN") "/Users/james/clotran/clotran/clotran"))

(defn clotran-out [files]
  (let [r (apply p/shell {:out :string :err :string :continue true
                          :extra-env {"CLOTRAN_PATH" (or (System/getenv "LEMMIS_SRC") (str root "/src"))}}
                 clotran (str here "/run-plain.clj") files)]
    (loop [ls (str/split-lines (:out r)) cur nil acc {}]
      (if-let [l (first ls)]
        (if-let [[_ f] (re-matches #"=== (.*)" l)] (recur (rest ls) f (assoc acc f [])) (recur (rest ls) cur (if cur (update acc cur conj l) acc)))
        acc))))

(def exts (sort (map str (fs/glob (str here "/ext") "*.lms"))))
(def errs (sort (map str (fs/glob (str here "/errors") "*.lms"))))
(def got (clotran-out (concat exts errs)))

(def results
  (concat
   (for [f exts]
     (let [c (p/shell {:out :string :err :string :continue true :dir (str here "/ext")} "clj" "-M" (str (fs/strip-ext f) ".clj"))
           want (str/split-lines (:out c))]
       [f (if (= want (get got f)) :ext-agree [:ext-differ (str "lemmis " (get got f) "\n      clj " want (:err c))])]))
   (for [f errs]
     (let [[_ lc text] (re-find #"^! error: (\d+:\d+): (.*)" (slurp f))
           msg (some #(second (re-matches #"!!! (.*)" %)) (get got f))]
       [f (if (and msg (str/starts-with? msg (str f ":" lc ": ")) (str/includes? msg text)) :error-ok
              [:error-wrong (str "want " lc ": " text "\n      got " msg)])]))))

(doseq [[k rs] (group-by #(if (keyword? (second %)) (second %) (first (second %))) results)]
  (println (format "%-14s %d" (name k) (count rs)))
  (doseq [[f v] (take 5 rs) :when (vector? v)] (println "   " (fs/file-name f) "--" (second v))))
(System/exit (if (every? #(keyword? (second %)) results) 0 1))
