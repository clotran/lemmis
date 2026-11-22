#!/usr/bin/env bb
;; test/mutate.bb : break the translator on purpose, one mutation at a time (in a copy of
;; src/), and check that the oracle cases (test/cases and test/model-cases, run by
;; test/cases.bb against gfortran and flang) catch each. A mutation the cases do not catch
;; is a hole in the tests. Prints killed/total; exit 1 if any survives.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(def root (str (fs/parent here)))

(def mutations
  [["rt.cljf" "(max 0 (quot (+ (- b a) s) s))" "(max 0 (quot (- b a) s))" "DO trip count off by one"]
   ["emit.cljf" "(list 'fortran.ops/+ (symbol dv) st)" "(list 'fortran.ops/- (symbol dv) st)" "DO variable stepped backwards"]
   ["rt.cljf" "(f/int (if (instance? fortran.ops.Complex v) (f/real v) v) k)" "(f/nint (if (instance? fortran.ops.Complex v) (f/real v) v) k)" "assignment rounds a real into an integer"]
   ["rt.cljf" "(defn concat-str [a b] (str a b))" "(defn concat-str [a b] (str b a))" "// reversed"]
   ["rt.cljf" "c (compare (conv-char n a) (conv-char n b))" "c (compare a b)" "character relations not blank-padded"]
   ["emit.cljf" "(reduce (fn [acc [c b]] (list 'if (ex env c) (f b) acc)) (f els) (reverse arms))" "(reduce (fn [acc [c b]] (list 'if (ex env c) (f b) acc)) (f els) arms)" "else-if arms in the wrong order"]
   ["rt.cljf" "(if (sub? r) (leftmost old (nth r k)) old)" "old" "CALL does not rebind its actuals"]
   ["rt.cljf" "(str v (subs old (count v)))" "v" "a shorter character dummy replaces the whole actual"]
   ["expr.cljf" "(at t {:op :un :o (:v t) :a (mult c)})" "(at t {:op :un :o (:v t) :a (power c)})" "unary minus binds tighter than *"]
   ["expr.cljf" ":a a :b (power c) :line (:line a)" ":a a :b (primary c) :line (:line a)" "** not right to left"]
   ["emitx.cljf" "(or k (if d? 8 4))" "(or k 4)" "a d exponent is real(4)"]
   ["rt.cljf" "(let [j (- (long i) lo)]" "(let [j (- (long i) 1)]" "array lower bound ignored"]
   ["emit.cljf" "bcx {:fall (constantly again) :cycle (constantly again) :exit #(yield false) :ret #(yield true)}" "bcx {:fall (constantly again) :cycle (constantly again) :exit (constantly again) :ret #(yield true)}" "EXIT continues the loop"]
   ["rt.cljf" "(not (and s? prev-str?))" "true" "adjacent character values separated"]
   ["emit.cljf" "after (if ret? (list 'if ret ((:ret cx)) after) after)" "after after" "RETURN inside a loop ignored"]])

(defn run-cases [src]
  (let [dir (str (fs/create-temp-dir {:prefix "lemmis-mut-cases"}))]
    (doseq [d ["cases" "model-cases"] f (fs/glob (str here "/" d) "*.lms")] (fs/copy f dir))
    (let [r (p/shell {:continue true :out :string :err :string :extra-env {"LEMMIS_SRC" src "LEMMIS_TIMEOUT" "90"}} "bb" (str here "/cases.bb") dir)]
      (fs/delete-tree dir)
      r)))

(let [base (run-cases (str root "/src"))]
  (when (pos? (:exit base)) (println "the cases fail with no mutation:\n" (:out base)) (System/exit 1)))

(def survivors
  (doall
   (for [[f old new why] mutations]
     (let [tmp (str (fs/create-temp-dir {:prefix "lemmis-mut"}))
           _ (fs/copy-tree (str root "/src") tmp)
           path (str tmp "/lemmis/" f)
           text (slurp path)
           n (count (re-seq (re-pattern (java.util.regex.Pattern/quote old)) text))]
       (when-not (= 1 n) (println "mutation text not found once in" f ":" old) (System/exit 2))
       (spit path (str/replace text old new))
       (let [r (run-cases tmp) killed (pos? (:exit r))]
         (println (if killed "killed  " "SURVIVED") why)
         (fs/delete-tree tmp)
         (when-not killed why))))))

(let [s (remove nil? survivors)]
  (println (format "%d/%d mutations killed" (- (count mutations) (count s)) (count mutations)))
  (System/exit (if (seq s) 1 0)))
