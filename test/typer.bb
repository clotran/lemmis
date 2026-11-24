#!/usr/bin/env bb
;; test/typer.bb : the checks of lemmis.typer.
;; (1) Every case of clotran's Fortran-types oracle (clotran/test/ftypes/cases.edn, the oracle
;;     checked against gfortran and flang): the oracle runs on real clj (its names mapped by
;;     clotran's upstream/names.clj, as scripts/ftypes-check does), the typer types the same
;;     expression written in Lemmis (test/typer_cases.clj). A defined case must get the oracle's
;;     kind; an ill-typed one must be a type error; an undefined one (the value is the
;;     processor's) must still get a type.
;; (2) Each test/typer-errors/X.lms starts "! error: LINE:COL: text": lemmis.fortran must refuse
;;     it with "PATH:LINE:COL: ...text...".
;; (3) The report of test/report/report.lms is test/report/report.expected.
;; Prints counts by kind; exit 1 on any failure. CLOTRAN_REPO names the clotran checkout.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str] '[clojure.edn :as edn])

(def here (str (fs/parent (fs/absolutize *file*))))
(def root (str (fs/parent here)))
(def repo (or (System/getenv "CLOTRAN_REPO") "/Users/james/clotran/clotran"))
(def clotran (or (System/getenv "CLOTRAN") (str repo "/clotran")))
(def src-path (or (System/getenv "LEMMIS_SRC") (str root "/src")))
(def cases-file (str repo "/test/ftypes/cases.edn"))
(def tmp (str (fs/create-temp-dir {:prefix "lemmis-typer"})))

(defn sh [opts & args] (apply p/shell (merge {:out :string :err :string :continue true :timeout 900000} opts) args))
(defn clotran-run [& args] (:out (apply sh {:extra-env {"CLOTRAN_PATH" src-path}} clotran args)))

;; (1) the oracle on clj
(load-file (str repo "/upstream/names.clj"))
(spit (str tmp "/refmath.clj") (names/to-upstream (slurp (str repo "/test/ftypes/refmath.clj"))))
(spit (str tmp "/oracle.clj") (names/to-upstream (slurp (str repo "/test/ftypes/oracle.clj"))))
(def answers
  (let [r (sh {:dir repo} "clj" "-Sdeps" "{:deps {org.clojure/clojure {:mvn/version \"1.12.6\"}}}"
              "-M" "-i" (str tmp "/refmath.clj") "-i" (str tmp "/oracle.clj")
              "-e" (str "(require 'clojure.edn) (ftypes.oracle/run-file " (pr-str cases-file) ")"))]
    (->> (str/split-lines (:out r)) (remove str/blank?) (mapv read-string))))
(def typed (vec (remove str/blank? (str/split-lines (clotran-run (str here "/typer_cases.clj") cases-file)))))
(def ncases (count (edn/read-string (slurp cases-file))))
(when-not (= ncases (count answers) (count typed))
  (println "cases" ncases "oracle answers" (count answers) "typer answers" (count typed)) (System/exit 1))

(def oracle-results
  (for [[[st k] line] (map vector answers typed)]
    (let [[mine text] (str/split line #" " 2)
          err? (str/starts-with? mine "ERROR:")]
      (case st
        :ok (if (= (name k) mine) [:kind-agrees] [:kind-differs (str text ": oracle " (name k) ", typer " mine)])
        :ill-typed (if err? [:refused-as-ill-typed] [:ill-typed-accepted (str text ": typer says " mine)])
        (if err? [:undefined-refused (str text ": " mine)] [:undefined-typed])))))

;; (2) type errors at their positions
(def err-files (sort (map str (fs/glob (str here "/typer-errors") "*.lms"))))
(def err-out
  (loop [ls (str/split-lines (apply clotran-run (str here "/typer_errors.clj") err-files)) cur nil acc {}]
    (if-let [l (first ls)]
      (if-let [[_ f] (re-matches #"=== (.*)" l)] (recur (rest ls) f acc) (recur (rest ls) cur (assoc acc cur l)))
      acc)))
(def error-results
  (for [f err-files]
    (let [[_ at lc text] (re-find #"^! error: (?:(\S+\.lms):)?(\d+:\d+): (.*)" (slurp f))   ; an error in a used module names its file
          at (if at (str (fs/parent f) "/" at) f)
          got (get err-out f)]
      (if (and got (str/starts-with? got (str "!!! " at ":" lc ": ")) (str/includes? got text))
        [:error-at-position]
        [:error-wrong (str (fs/file-name f) ": want " lc ": " text "\n        got " got)]))))

;; (3) the report
(def report-results
  (for [[f e] [["report/report.lms" "report/report.expected"] ["report-use/report_use.lms" "report-use/report_use.expected"] ["report-use/report_cproc.lms" "report-use/report_cproc.expected"]]]
    (let [got (clotran-run "-m" "lemmis.fortran" "--report" (str here "/" f))
          want (slurp (str here "/" e))
          got (str/replace got (str here "/") "test/")]
      (if (= (str/trim want) (str/trim got)) [:report-as-expected] [:report-differs (str f " got:\n" got)]))))

(def all (concat oracle-results error-results report-results))
(def by (group-by first all))
(doseq [[k rs] (sort-by key by)]
  (println (format "%-22s %d" (name k) (count rs)))
  (doseq [[_ msg] (take 5 rs) :when msg] (println "   " msg)))
(println (format "%d oracle cases (%d defined, %d ill-typed, %d undefined), %d error cases, 3 reports"
                 ncases (count (filter #(= :ok (first %)) answers)) (count (filter #(= :ill-typed (first %)) answers))
                 (count (filter #(= :undefined (first %)) answers)) (count err-files)))
(fs/delete-tree tmp)
(System/exit (if (every? #{:kind-agrees :refused-as-ill-typed :undefined-typed :error-at-position :report-as-expected} (keys by)) 0 1))
