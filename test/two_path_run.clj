;; clotran test/two_path_run.clj FILE.lms ... : lane 2's path (lemmis.reader to forms, run by
;; clotran), printing as test/lms_tagio.f90 prints: one tagged value per line, a record ended
;; by "/". Reals are printed as clotran prints them (shortest text, exact in their kind);
;; test/two_path.bb turns that text into the real's bits. Each file's output starts "=== FILE";
;; an error prints "!!! message".
(require 'lemmis.reader 'lemmis.rt '[fortran.ops :as f] '[clojure.string :as str])

(defn- kn [x] (subs (name (f/kind-of x)) (if (str/starts-with? (name (f/kind-of x)) "complex") 7 (if (str/starts-with? (name (f/kind-of x)) "real") 4 3))))

(defn- tag [x]
  (cond (string? x) (str "S:" x)
        (boolean? x) (if x "L:T" "L:F")
        (instance? fortran.ops.Complex x) (str "C" (kn x) ":" (:re x) "," (:im x))
        (and (number? x) (integer? x)) (str "I" (kn x) ":" x)
        (number? x) (str "R" (kn x) ":" x)
        :else (str "X:" (pr-str x))))

(defn- scalar? [x] (or (nil? x) (string? x) (boolean? x) (number? x) (keyword? x) (coll? x) (fn? x) (instance? fortran.ops.Complex x)))

(defn print-tagged [& items]
  (doseq [x (mapcat #(if (scalar? %) [%] (seq %)) items)] (println (tag x)))
  (println "/"))

(alter-var-root #'lemmis.rt/print-star (constantly print-tagged))
(doseq [p *command-line-args*]
  (println "===" p)
  (try
    (let [forms (lemmis.reader/read-forms (slurp p) p)
          lib (second (first forms))]
      (binding [*ns* *ns*] (doseq [form forms] (eval form)))
      (if-let [r (ns-resolve (find-ns lib) 'run)] (r) ((ns-resolve (find-ns lib) '-main))))
    (catch clotran.host.exception e (println "!!!" (ex-message e))))
  (flush))
