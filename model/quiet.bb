#!/usr/bin/env bb
;; quiet.bb NAME CMD...: run CMD, all output to build/NAME.txt (from the repo root).
;; Success: print only its "check-fsem:/check-gen:/fuzz:" summary lines. Failure:
;; print up to 20 lines that look like failures (else the last 20), exit 1.
(require '[babashka.process :as p] '[clojure.string :as str])
(let [[name & cmd] *command-line-args*
      r (apply p/shell {:out :string :err :string :continue true} cmd)
      all (str (:out r) (:err r))
      ls (str/split-lines all)
      f (str "build/" name ".txt")]
  (spit f all)
  (if (zero? (:exit r))
    (doseq [l (take-last 6 (filter #(re-find #"^(check-fsem|check-gen|fuzz): " %) ls))] (println l))
    (let [bad (filter #(re-find #"FAIL|disagree|differ|DIFFER|refuses|not what|did not|rror|answered" %) ls)]
      (doseq [l (take 20 (if (seq bad) bad (take-last 20 ls)))] (println l))
      (println "(full output in" f ")")))
  (System/exit (:exit r)))
