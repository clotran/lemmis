#!/usr/bin/env bb
;; test/all.bb [--mutate] : every check of lemmis.reader, in order; exit 1 on the first failure.
;; The oracle cases, the model's cases and the refusals (gfortran, flang, clotran), the
;; extensions against clj and the error positions, a seeded fuzz run; --mutate adds the
;; mutation test (slow, ~10 min).
(require '[babashka.process :as p] '[babashka.fs :as fs])
(def here (str (fs/parent (fs/absolutize *file*))))
(def steps (cond-> [["cases.bb"] ["cases.bb" (str here "/model-cases")] ["cases.bb" (str here "/refused")]
                    ["ext.bb"] ["macro.bb"] ["fuzz.bb" "7" "40"]]
             (some #{"--mutate"} *command-line-args*) (conj ["mutate.bb"])))
(let [root (str (fs/parent here))
      r (p/shell {:continue true :out :string :err :string :dir root
                  :extra-env {"CLOTRAN_PATH" (str root "/src:" root "/examples")}}
                 (or (System/getenv "CLOTRAN") "/Users/james/clotran/clotran/clotran") "examples/run.clj")]
  (println "== examples/run.clj")
  (when-not (= (:out r) (slurp (str root "/examples/run.out")))
    (println "FAILED: examples/run.clj printed\n" (:out r) (:err r)) (System/exit 1)))
(doseq [[s & args] steps]
  (println "==" s (apply str (interpose " " args)))
  (let [r (apply p/shell {:continue true} "bb" (str here "/" s) args)]
    (when (pos? (:exit r)) (println "FAILED:" s) (System/exit 1))))
(println "all green")
