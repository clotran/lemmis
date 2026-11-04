#!/usr/bin/env bb
;; fetch-fcvs.bb: NIST's FCVS (FORTRAN 77 validation suite) into model/fcvs/, from
;; LLVM's test-suite copy (Fortran/UnitTests/fcvs21_f95: 180 programs, each with
;; its reference output). The suite is a work of the US government, in the
;; public domain (17 USC 105); NIST asks that it be acknowledged and that
;; changes be stated: LLVM's README states theirs (FM110's FORMAT fixed,
;; Hollerith strings in FORMATs quoted). Lemmis changes nothing.
(require '[babashka.fs :as fs] '[babashka.process :as p] '[clojure.string :as str])
(def here (str (fs/parent (fs/absolutize *file*))))
(def dest (str here "/fcvs"))
(def base "https://raw.githubusercontent.com/llvm/llvm-test-suite/main/Fortran/UnitTests/fcvs21_f95/")
(defn sh! [secs & cmd]
  (let [proc (apply p/process {:out :string :err :string} cmd) r (deref proc (* 1000 secs) ::timeout)]
    (if (= r ::timeout) (do (p/destroy-tree proc) {:exit 124 :out ""}) r)))
(fs/create-dirs dest)
(let [ls (sh! 60 "gh" "api" "repos/llvm/llvm-test-suite/contents/Fortran/UnitTests/fcvs21_f95" "--jq" ".[].name")
      names (filter #(str/starts-with? % "FM") (str/split-lines (:out ls)))]
  (when (empty? names) (println "fetch-fcvs: no listing (gh api)") (System/exit 1))
  (doseq [n (cons "README" names) :let [f (str dest "/" n)] :when (not (fs/exists? f))]
    (let [r (sh! 60 "curl" "-s" "-f" "-o" f (str base n))]
      (when (not= 0 (:exit r)) (println "fetch-fcvs: could not fetch" n))))
  (println "fetch-fcvs:" (count (fs/glob dest "FM*.f")) "programs in" dest))
