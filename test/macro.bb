#!/usr/bin/env bb
;; test/macro.bb : the pattern macros (src/lemmis/macro.cljf, prelude when, ->, ->>).
;; (1) each test/macro/X.lms must print what test/macro/ref/X.lms prints: the same program with the
;;     built-in forms (if, the prefix pipelines) written out, run by clotran (the interpreted oracle);
;; (2) the report of X.lms must put its findings on the lines the user wrote (the same lines as the built-in form), never in the prelude;
;; (3) test/macro/two_path/*.lms go through the two-path oracle (compiled Fortran against clotran);
;; (4) a macro call no rule matches is refused at the call. Exit 1 on any failure.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])
(def here (str (fs/parent (fs/absolutize *file*))))
(def root (str (fs/parent here)))
(def clotran (or (System/getenv "CLOTRAN") "/Users/james/clotran/clotran/clotran"))
(defn ct [& args] (:out (apply p/shell {:out :string :err :string :continue true :dir here
                                       :extra-env {"CLOTRAN_PATH" (or (System/getenv "LEMMIS_SRC") (str root "/src"))}} clotran args)))
(defn body [out] (rest (str/split-lines out)))
(def fails (atom []))
(doseq [f (sort (map str (fs/glob (str here "/macro") "*.lms")))
        :let [rel (str "macro/" (fs/file-name f))]]
  (let [a (body (ct "run-lms.clj" rel)) b (body (ct "run-lms.clj" (str "macro/ref/" (fs/file-name f))))]
    (when-not (and (seq a) (= a b)) (swap! fails conj (str rel ": macro " a " ref " b))))
  (let [at (fn [r] (set (map #(parse-long (second %)) (re-seq #"--> \S+?:(\d+):" r))))
        a (at (ct "-m" "lemmis.fortran" "--report" rel))
        b (at (ct "-m" "lemmis.fortran" "--report" (str "macro/ref/" (fs/file-name f))))]
    (when-not (= a b) (swap! fails conj (str rel ": findings at lines " (sort a) ", the built-in form's at " (sort b))))))
(let [tp (p/shell {:out :string :err :string :continue true} "bb" (str here "/two_path.bb") (str here "/macro/two_path"))]
  (when-not (zero? (:exit tp)) (swap! fails conj (str "two_path on macro/two_path: " (:out tp)))))
(let [bad (str root "/test/macro/bad/nomatch.lms")
      out (ct "run-lms.clj" "macro/bad/nomatch.lms")]
  (when-not (str/includes? out "nomatch.lms:6:") (swap! fails conj (str "nomatch: " out))))
(let [out (ct "run-lms.clj" "macro/bad/deep.lms")]
  (when-not (and (str/includes? out "deep.lms:9:") (str/includes? out "deeper than")) (swap! fails conj (str "deep: " out))))
(doseq [m @fails] (println "FAIL" m))
(println (if (empty? @fails) "macro: ok" (str "macro: " (count @fails) " failed")))
(System/exit (if (empty? @fails) 0 1))
