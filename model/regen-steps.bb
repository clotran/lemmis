;; regen-steps.bb FILE FN STEPS EXTRA... (from model/): replace the generated
;; (defun STEPS ...) with a fresh one from mksteps.bb, after FILE's FN changed; STEPS
;; may live in another book. Split mode, when a book holds (defconst *STEPS-1* ...):
;; the defun's case clauses go half to *STEPS-1*, half to *STEPS-2*, and the rest of
;; the defun to the (make-event `(defun STEPS ...)) after *STEPS-2*, which splices the
;; two together; so each book stays under 800 lines (fstmt-steps, fstmt-steps2).
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
(defn holder [f mark] (first (filter #(str/includes? (slurp %) mark) (cons f (map str (fs/glob "." "*.lisp"))))))
(defn replace-form [dst mark new]
  (let [s (slurp dst) i (str/index-of s mark)]
    (spit dst (str (subs s 0 i) new (subs s (form-end s i))))))
(let [[f fname steps & extra] *command-line-args*
      gen (str/trimr (:out (apply p/shell {:out :string} "bb" "mksteps.bb" f fname steps extra)))
      m1 (str "(defconst *" steps "-1*") m2 (str "(defconst *" steps "-2*") m3 (str "(make-event\n `(defun\n " steps "\n")]
  (if-let [d1 (holder f m1)]
    (let [ci (str/index-of gen "(case\n") cj (form-end gen ci)
          starts (take-while #(and % (< % cj)) (iterate #(str/index-of gen "\n    (" (inc %)) (str/index-of gen "\n    (" ci)))
          lines #(count (re-seq #"\n" (subs gen 0 %)))
          half (/ (+ (lines (first starts)) (lines cj)) 2)
          cs (apply min-key #(Math/abs (double (- (lines %) half))) starts)
          d2 (holder f m2)]
      (replace-form d1 m1 (str m1 "\n '(" (str/triml (subs gen (first starts) cs)) "))"))
      (replace-form d2 m2 (str m2 "\n '(" (str/triml (subs gen cs (dec cj))) "))"))
      (replace-form d2 m3 (str "(make-event\n `" (subs gen 0 ci) "(case nt ,@*" steps "-1* ,@*" steps "-2*)" (subs gen cj) ")")))
    (let [mark (str "(defun\n " steps "\n")]
      (replace-form (holder f mark) mark gen)))
  (println "regenerated" steps))
