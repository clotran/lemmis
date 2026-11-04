;; regen-steps.bb FILE FN STEPS EXTRA... (from model/): replace the generated
;; (defun STEPS ...) with a fresh one from mksteps.bb, after FILE's FN changed; STEPS
;; may live in another book (fps-steps is in fstmt-cost.lisp)
(require '[babashka.fs :as fs] '[babashka.process :as p] '[clojure.string :as str])
(defn form-end [s i]                   ; index just past the form opening at i (strings, chars, comments skipped)
  (loop [j i depth 0]
    (let [c (.charAt s j)]
      (cond (= c \") (recur (loop [k (inc j)] (case (.charAt s k) \\ (recur (+ k 2)) \" (inc k) (recur (inc k)))) depth)
            (= c \;) (recur (inc (str/index-of s "\n" j)) depth)
            (and (= c \#) (= (.charAt s (inc j)) \\)) (recur (+ j 3) depth)
            (= c \() (recur (inc j) (inc depth))
            (= c \)) (if (= depth 1) (inc j) (recur (inc j) (dec depth)))
            :else (recur (inc j) depth)))))
(let [[f fname steps & extra] *command-line-args*
      mark (str "(defun\n " steps "\n")
      dst (first (filter #(str/includes? (slurp %) mark) (cons f (map str (fs/glob "." "*.lisp")))))
      s (slurp dst)
      gen (:out (apply p/shell {:out :string} "bb" "mksteps.bb" f fname steps extra))
      i (str/index-of s mark)
      j (form-end s i)]
  (spit dst (str (subs s 0 i) (str/trimr gen) (subs s j)))
  (println "regenerated" steps))
