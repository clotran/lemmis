#!/usr/bin/env bb
;; test/mutate_fortran.bb [N [WHY]] : break lemmis.typer and lemmis.fortran on purpose, one rule at a
;; time (in a copy of src/), and check that the checks catch each: a rule of the types or of the
;; translation must make THE TWO-PATH ORACLE fail (test/two_path.bb over the cases, the model
;; cases, test/fortran-cases and 25 fuzzed programs); a refusal rule (an error Lemmis must give)
;; must make test/typer.bb fail. A mutation nothing catches is a hole in the checks. Runs N at a
;; time (default 3), only those whose description contains WHY if given; prints killed/total;
;; exit 1 if any survives.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(def root (str (fs/parent here)))
(def par (parse-long (or (first *command-line-args*) "3")))
(def only (second *command-line-args*))

(def mutations
  [;; the typer: Fortran's kinds (the oracle sees them through vals, pipeline helpers and kind tags)
   ["typer.cljf" "(and (ik? a) (ik? b)) (if (>= (bits a) (bits b)) a b)" "(and (ik? a) (ik? b)) (if (>= (bits a) (bits b)) b a)" "integer with integer gives the smaller kind" :two-path]
   ["typer.cljf" "(ik? a) b\n        :else a))" "(ik? a) a\n        :else a))" "integer with real gives the integer's kind" :two-path]
   ["typer.cljf" "(and (rk? a) (rk? b)) (if (>= (bits a) (bits b)) a b)" "(and (rk? a) (rk? b)) (if (>= (bits a) (bits b)) b a)" "real with real gives the smaller kind" :two-path]
   ["typer.cljf" "(cplx-of (reduce (fn [x y] (if (>= (bits x) (bits y)) x y)) ps))" "(cplx-of (reduce (fn [x y] (if (>= (bits x) (bits y)) y x)) ps))" "a complex result takes the narrower part" :two-path]
   ["typer.cljf" "{:k (or (kind-arg env e \"int\") :int4)})\n        (\"nint\"" "{:k (or (kind-arg env e \"int\") :int8)})\n        (\"nint\"" "int's default kind is integer(8)" :two-path]
   ["typer.cljf" "{:k (or (kind-arg env e \"real\") (when (ck? (:k t0)) (part (:k t0))) :real4)}" "{:k (or (when (ck? (:k t0)) (part (:k t0))) :real4)}" "real(x, kind) ignores its kind" :two-path]
   ["typer.cljf" "(when (ck? (:k t0)) (part (:k t0))) :real4)}" "nil :real4)}" "real of a complex(8) is real(4)" :two-path]
   ["typer.cljf" "(if (clj? t0) t0 {:k (or (part (:k t0)) (:k t0))})" "(if (clj? t0) t0 {:k (:k t0)})" "abs of a complex is complex" :two-path]
   ["typer.cljf" "(+ (:len ta) (:len tb))" "(max (:len ta) (:len tb))" "// has the longer operand's length" :two-path]
   ["typer.cljf" "\"dble\" (do (when-not (clj? t0) (num1 \"a number\" num-k?)) {:k :real8})" "\"dble\" (do (when-not (clj? t0) (num1 \"a number\" num-k?)) {:k :real4})" "dble is real(4)" :two-path]
   ["typer.cljf" ":real (let [k (keyword (str \"real\" n))]" ":real (let [k :real4]" "every real literal is real(4)" :two-path]
   ["typer.cljf" "kn (max (or (part-k (:re e)) 4) (or (part-k (:im e)) 4))]\n               (tx env (:re e))" "kn 4]\n               (tx env (:re e))" "every complex literal is complex(4)" :two-path]
   ["typer.cljf" "\"aimag\" (do (num1 \"a complex\" ck?) {:k (part (:k t0))})" "\"aimag\" (do (num1 \"a complex\" ck?) {:k (:k t0)})" "aimag is complex" :two-path]
   ["typer.cljf" "(and (= n (:src v)) (= (select-keys t [:k :len :rank]) (select-keys (:t v) [:k :len :rank])))" "(= n (:src v))" "a val reuses an earlier val's local of another type" :two-path]
   ;; the typer: what Fortran refuses (no valid program shows a missing refusal: test/typer.bb's cases do)
   ["typer.cljf" "(scalar! env a t (str \"the actual for \" dn))\n            (when-not (= (:k t) (:k d))" "(scalar! env a t (str \"the actual for \" dn))\n            (when (= :never (:k d))" "an actual of another kind is accepted" :typer]
   ["typer.cljf" "(do (need-logical env (:a e) ta (str \"the left operand of .\" o \".\"))" "(do ta" "an integer left operand of .and. is accepted" :typer]
   ["typer.cljf" "(when (some (:printers env) (calls-in i))" "(when false" "a printing function inside PRINT is accepted" :typer]
   ;; the translator
   ["fortran.cljf" "{\"and\" \".and.\" \"or\" \".or.\"" "{\"and\" \".or.\" \"or\" \".and.\"" ".and. and .or. swapped" :two-path]
   ["fortran.cljf" ":paren (str \"(\" (ex ctx (:a e)) \")\")" ":paren (ex ctx (:a e))" "parentheses dropped" :two-path]
   ["fortran.cljf" "(when (:step s) (str \", \" (ex ctx (:step s)))))]" "nil)]" "a DO step dropped" :two-path]
   ["fortran.cljf" "(range) (:arms s))" "(range) (reverse (:arms s)))" "else-if arms reversed" :two-path]
   ["fortran.cljf" "\"      if (.not. \" (:fn st) \"(\" cur \")) cycle\"" "\"      if (\" (:fn st) \"(\" cur \")) cycle\"" "filter keeps what it should drop" :two-path]
   ["fortran.cljf" "\"sum\" [\"    r = 0\"]" "\"sum\" [\"    r = 1\"]" "a pipeline sum starts at 1" :two-path]
   ["fortran.cljf" "(if (= red \"maxval\") \"max\" \"min\")" "(if (= red \"maxval\") \"min\" \"max\")" "maxval and minval swapped in a pipeline" :two-path]
   ["fortran.cljf" "(conj out (str \"      \" (tmp-of i) \" = \" (:fn st) \"(\" cur \")\"))" "(conj out (str \"      \" (tmp-of i) \" = \" cur))" "map does not apply its function" :two-path]
   ["fortran.cljf" "(fname (:name l)) (when (:idx l) (str \"(\" (ex ctx (:idx l)) \")\")) \" = \"" "(fname (:name l)) \" = \"" "an element assignment assigns the whole array" :two-path]
   ["fortran.cljf" "(str/join \", \" (map #(ex ctx %) (:items s)))" "(str/join \", \" (map #(ex ctx %) (butlast (:items s))))" "plain PRINT drops its last item (only the pass-through sees it)" :two-path]
   ["fortran.cljf" "(str (:o e) (ex ctx (:a e)))" "(ex ctx (:a e))" "unary minus dropped" :two-path]
   ["fortran.cljf" ":real (str (:v e) (kind-sfx e))" ":real (:v e)" "a real literal's kind suffix dropped" :two-path]
   ["typer.cljf" "(if thread-last? (conj args hole) (into [hole] args))" "(into [hole] args)" "->> passes its value first" :two-path]
   ["fortran.cljf" ":val [(str I (:fname s) \" = \" (ex ctx (:e s)))]" ":val []" "a val is declared but never assigned" :two-path]
   ["fortran.cljf" "(str \"'\" (str/replace s \"'\" \"''\") \"'\")" "(str \"'\" s \"'\")" "a quote in a character literal not doubled" :two-path]
   ["fortran.cljf" "(cons (str (subs line 0 i) \" &\")" "(cons (subs line 0 i)" "a long line is split with no &" :two-path]
   ;; use of another Lemmis module (the compiled path of require)
   ["typer.cljf" "(= :public (get-in acc [:names n] (:default acc)))" "true" "a private name of a used module is imported" :typer]
   ["typer.cljf" "((:printers (:env dep)) r) (update :printers conj l)" "false (update :printers conj l)" "an imported function that prints is not known to print" :typer]
   ["typer.cljf" "(concat deps (:deps dep) [[m dp dtext]])" "(concat deps [[m dp dtext]] (:deps dep))" "a module is built before the modules it uses" :two-path]
   ["typer.cljf" "(if (seen (first d)) {:seen seen :val val}" "(if false {:seen seen :val val}" "a module used twice is built twice" :two-path]
   ["typer.cljf" "(conj uses (assoc u :lms dp))" "(conj uses u)" "a use of a Lemmis module has no use statement" :two-path]
   ["typer.cljf" "(assoc-in env [:b-from l] [(:name u) bs])" "env" "the B004 help does not name the module's tier-B procedures" :typer]
   ["typer.cljf" "(every? #(= :A (:tier %)) (vals (:procs dep)))" "true" "a module with a tier-B procedure is imported as if tier A" :typer]
   ["typer.cljf" "(when (and dp ((:stack opts) m))" "(when false" "a circular use is not refused" :typer]
   ["fortran.cljf" "(if (= l r) l (str l \" => \" r))) (:only u))" "(if (= l r) l (str r \" => \" l))) (:only u))" "a renamed import is written the wrong way round" :two-path]
   ;; a clotran function calling a Lemmis module (the other direction)
   ["fortran.cljf" "(when (and (= :function (:kind p)) res (zero? (or (:rank res) 0)))\n                                          (get ty/type-ts [(:k res) 0]))" "(when (and (= :function (:kind p)) res (zero? (or (:rank res) 0)))\n                                          (get ty/type-ts [(:k res) 1]))" "a Lemmis function's result type is looked up as an array" :to-clotran]])

(def mutations (if only (filterv #(str/includes? (nth % 3) only) mutations) mutations))

(def corpus [(str here "/cases") (str here "/model-cases") (str here "/fortran-cases") (str here "/multi/mu_basic/mu_basic.lms") (str here "/multi/mu_whole/mu_whole.lms") "--fuzz" "1" "25"])

(defn run-check [check src]
  (case check
    :two-path (apply p/shell {:continue true :out :string :err :string :extra-env {"LEMMIS_SRC" src}} "bb" (str here "/two_path.bb") corpus)
    :typer (p/shell {:continue true :out :string :err :string :extra-env {"LEMMIS_SRC" src}} "bb" (str here "/typer.bb"))
    :to-clotran (p/shell {:continue true :out :string :err :string :extra-env {"LEMMIS_SRC" src}} "bb" (str here "/to_clotran.bb") "--fuzz" "1" "6" (str here "/to-clotran/cl_calls"))))

(println "baseline (no mutation) ...")
(doseq [c [:two-path :typer]]
  (let [r (run-check c (str root "/src"))]
    (when (pos? (:exit r)) (println "the" (name c) "check fails with no mutation:\n" (:out r)) (System/exit 1))))

(defn mutate [[f old new why check]]
  (let [tmp (str (fs/create-temp-dir {:prefix "lemmis-fmut"}))
        _ (fs/copy-tree (str root "/src") tmp)
        path (str tmp "/lemmis/" f)
        text (slurp path)
        n (loop [i 0 n 0] (if-let [j (str/index-of text old i)] (recur (inc j) (inc n)) n))]
    (if-not (= 1 n)
      (do (fs/delete-tree tmp) [why :bad (str "the text occurs " n " times in " f)])
      (do (spit path (str/replace text old new))
          (let [r (run-check check tmp)
                summary (str/join " / " (filter #(re-find #"^[a-z-]+ +\d+$" %) (str/split-lines (:out r))))]
            (fs/delete-tree tmp)
            [why (if (pos? (:exit r)) :killed :survived) (str (name check) ": " summary)])))))

(def results (vec (mapcat #(pmap mutate %) (partition-all par mutations))))
(doseq [[why st msg] results]
  (println (case st :killed "killed  " :survived "SURVIVED" :bad "BROKEN  ") why "--" msg))
(let [k (count (filter #(= :killed (second %)) results))]
  (println (format "%d/%d mutations killed" k (count mutations)))
  (System/exit (if (= k (count mutations)) 0 1)))
