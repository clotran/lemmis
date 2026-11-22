#!/usr/bin/env bb
;; test/two_path.bb [--fuzz SEED N]... [DIR|FILE.lms ...] : THE TWO-PATH ORACLE (PLAN.md,
;; "Two paths, one oracle"). Every program goes two ways:
;;   (a) lemmis.fortran's Fortran, built by gfortran and by flang, run;
;;   (b) lane 2's lemmis.reader to Clojure forms, run by clotran;
;; and the printed values are compared one by one: integers with their kind, reals bit for bit
;; in their kind (test/lms_tagio.f90 and test/two_path_run.clj print the same tagged lines).
;; A program that is plain Fortran also checks the pass-through: the source as it is and the
;; translation, built by the same compiler, must print the same bytes. The translation must
;; build with no diagnostic under gfortran -std=f2018 -pedantic and flang -pedantic.
;; Default corpus: test/cases and test/model-cases. --fuzz SEED N adds N random programs from
;; seed SEED (test/two_path_gen.clj, the generator). Prints a count by kind with the first few
;; of each; exit 1 on any kind but agree.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(def root (str (fs/parent here)))
(def clotran (or (System/getenv "CLOTRAN") "/Users/james/clotran/clotran/clotran"))
(def src-path (or (System/getenv "LEMMIS_SRC") (str root "/src")))
(def tmp (str (fs/create-temp-dir {:prefix "lemmis-2path"})))
(load-file (str here "/two_path_gen.clj"))

(defn parse-args [args]
  (loop [as args fuzz [] paths []]
    (cond (empty? as) [fuzz paths]
          (= "--fuzz" (first as)) (recur (drop 3 as) (conj fuzz [(parse-long (nth as 1)) (parse-long (nth as 2))]) paths)
          :else (recur (rest as) fuzz (conj paths (first as))))))

(def files
  (let [[fuzz paths] (parse-args *command-line-args*)
        paths (if (and (empty? paths) (empty? fuzz)) [(str here "/cases") (str here "/model-cases")] paths)
        given (mapcat #(if (fs/directory? %) (sort (map str (fs/glob % "*.lms"))) [(str (fs/absolutize %))]) paths)
        fdir (str tmp "/fuzz")]
    (fs/create-dirs fdir)
    (concat (map str given)
            (for [[seed n] fuzz i (range n)]
              (let [nm (str "tp" seed "_" i) f (str fdir "/" nm ".lms")]
                (spit f (gen-program nm (+ (* 1000 seed) i)))
                f)))))

(defn sh [opts & args] (apply p/shell (merge {:out :string :err :string :continue true :timeout 120000} opts) args))

(defn sections
  "clotran's output split at === FILE lines."
  [out]
  (loop [ls (str/split-lines out) cur nil acc {}]
    (if-let [l (first ls)]
      (if-let [[_ f] (re-matches #"=== (.*)" l)]
        (recur (rest ls) f (assoc acc f []))
        (recur (rest ls) cur (if cur (update acc cur conj l) acc)))
      acc)))

(defn clotran-run [script & args]
  (let [r (apply sh {:extra-env {"CLOTRAN_PATH" src-path} :timeout 1800000} clotran (str here "/" script) args)]
    (when (and (str/blank? (:out r)) (seq args)) (println "clotran failed:" (:exit r) (:err r) (pr-str (take 3 args))) (System/exit 1))
    (sections (:out r))))

(defn module-name [src] (second (re-find #"(?im)^\s*module\s+([a-z0-9_.?]+)\s*$" src)))
(defn program? [src] (re-find #"(?im)^\s*program\s+" src))
(defn driver [src]
  (when-not (program? src)
    (str "\nprogram lms_driver\n  use " (str/replace (str/replace (module-name src) "." "_") "?" "_q") "\n  call run()\nend program lms_driver\n")))

(def flags {"gfortran" ["-std=f2018" "-pedantic" "-O2" "-ffp-contract=off"]
            "flang" ["-pedantic" "-O2" "-ffp-contract=off"]})

(defn build-run
  "Compile text (one file) with fc and run it: {:out text :warn diagnostics} or {:error msg}."
  [fc base text]
  (let [dir (str tmp "/" base "-" fc) _ (fs/create-dirs dir)
        f90 (str dir "/p.f90") exe (str dir "/p")]
    (spit f90 text)
    (let [c (apply sh {:dir dir} fc (concat (flags fc) ["-o" exe f90]))]
      (if (pos? (:exit c))
        {:error (str fc " compile: " (str/join " | " (take 3 (str/split-lines (str (:err c) (:out c))))))}
        (let [r (sh {:dir dir} exe)]
          (if (pos? (:exit r)) {:error (str fc " run exit " (:exit r) ": " (str/trim (str (:err r))))}
              {:out (:out r) :warn (str/trim (str (:err c) (:out c)))}))))))

(defn bits [k s]
  (case k
    "4" (Float/floatToRawIntBits (Float/parseFloat s))
    "8" (Double/doubleToRawLongBits (Double/parseDouble s))))
(defn nan-bits? [k b] (case k "4" (Float/isNaN (Float/intBitsToFloat (int b))) "8" (Double/isNaN (Double/longBitsToDouble (long b)))))
(defn same-bits? [k text fb]
  (let [mine (bits k text) theirs (parse-long fb)]
    (or (= mine theirs) (and (nan-bits? k mine) (nan-bits? k theirs)))))

(defn value-match?
  "clotran's tagged line against the compiled program's."
  [c f]
  (or (= c f)
      (when-let [[_ k t] (re-matches #"R(\d):(.*)" c)]
        (when-let [[_ k2 b] (re-matches #"B(\d):(-?\d+)" f)] (and (= k k2) (same-bits? k t b))))
      (when-let [[_ k a b] (re-matches #"C(\d):([^,]*),(.*)" c)]
        (when-let [[_ k2 x y] (re-matches #"C(\d):(-?\d+),(-?\d+)" f)] (and (= k k2) (same-bits? k a x) (same-bits? k b y))))))

(defn first-diff [cl fl]
  (let [n (max (count cl) (count fl))]
    (first (keep (fn [i] (let [a (get cl i) b (get fl i)] (when-not (and a b (value-match? a b)) (str "value " (inc i) ": clotran " a ", fortran " b))))
                 (range n)))))

(defn -main []
  (let [cl (apply clotran-run "two_path_run.clj" files)
        em (apply clotran-run "two_path_emit.clj" tmp files)
        tagio (slurp (str here "/lms_tagio.f90"))
        results
        (pmap (fn [[i f]]
                (let [src (slurp f) drv (driver src)
                      e (first (get em f))
                      mine (get cl f)
                      expect-diff (second (re-find #"^! differs: (.*)" src))
                      cerr (some #(when-let [[_ m] (re-matches #"!!! (.*)" %)] m) mine)]
                  [f (cond
                       (nil? e) [:no-output "the translator printed nothing"]
                       (str/starts-with? e "tier-b:") [:tier-b e]
                       (str/starts-with? e "!!!") [:translate-error e]
                       cerr [:clotran-error cerr]
                       :else
                       (let [plain (slurp (str tmp "/" i ".plain.f90"))
                             tagged (str tagio (slurp (str tmp "/" i ".tagged.f90")) drv)
                             rs (for [fc ["gfortran" "flang"]]
                                  (let [t (build-run fc (str i "t") tagged)
                                        pl (build-run fc (str i "p") (str plain drv))
                                        orig (build-run fc (str i "o") (str src drv))]
                                    (cond (:error t) [:fortran-error (:error t)]
                                          (:error pl) [:fortran-error (:error pl)]
                                          (seq (:warn pl)) [:not-clean (str fc ": " (first (str/split-lines (:warn pl))))]
                                          :else
                                          (let [d (first-diff (vec mine) (str/split-lines (:out t)))]
                                            (cond d [:differ (str fc " " d)]
                                                  ;; valid Fortran as written: the translation prints the same bytes
                                                  (and (not (:error orig)) (not= (:out orig) (:out pl))) [:pass-through-differs (str fc ": source and translation print differently")]
                                                  :else [:agree (if (:error orig) :extended :plain)])))))]
                         (let [v (or (first (remove #(= :agree (first %)) rs)) (first rs))]
                           (cond (not expect-diff) v
                                 (= :differ (first v)) [:differs-as-expected expect-diff]
                                 :else [:expected-a-difference (str "it was marked 'differs: " expect-diff "' -- " (pr-str v))]))))]))
              (map-indexed vector files))
        by (group-by (comp first second) results)]
    (doseq [[k rs] (sort-by key by)]
      (println (format "%-22s %d" (name k) (count rs)))
      (if (= k :agree)
        (println (format "    %d plain Fortran (pass-through checked), %d with extensions"
                         (count (filter #(= :plain (second (second %))) rs)) (count (filter #(= :extended (second (second %))) rs))))
        (doseq [[f [_ msg]] (take 4 rs)] (println "   " (fs/file-name f) "--" msg))))
    (println (format "%d programs, %d agree (gfortran and flang, each against clotran)" (count files) (count (:agree by))))
    (when-let [keep (System/getenv "LEMMIS_KEEP")]
      (doseq [[f [k]] results :when (not= :agree k)] (fs/create-dirs keep) (fs/copy f keep {:replace-existing true})))
    (fs/delete-tree tmp)
    (System/exit (if (every? #{:agree :differs-as-expected} (keys by)) 0 1))))

(-main)
