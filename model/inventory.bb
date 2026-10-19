#!/usr/bin/env bb
;; inventory.bb: count each Fortran construct in clotran's generated files
;; (SUBSET.md's table).  bb model/inventory.bb [CLOTRAN-DIR]
(require '[clojure.string :as str])
(def clotran-dir (or (first *command-line-args*) "../clotran"))
(def files ["src/f/gen/vm_gen.f90" "src/f/gen/vmc_gen.f90" "src/f/gen/heap_gen.inc"])
(def lines (for [f files l (str/split-lines (slurp (str clotran-dir "/" f)))
                 :let [t (str/trim l)] :when (and (seq t) (not (str/starts-with? t "!")))] t))
;; [name, :line regex (whole statement) or :occ regex (occurrences in any line)]
(def rows
  [["module-stmt" :line #"^module \w+$"] ["end-module-stmt" :line #"^end module \w+$"]
   ["use-stmt, ONLY" :line #"^use iso_fortran_env, only: int64$"] ["use-stmt" :line #"^use \w+$"]
   ["implicit none" :line #"^implicit none$"] ["contains-stmt" :line #"^contains$"]
   ["function-stmt, pure" :line #"^pure function \w+\(.*\) result\(r\)$"]
   ["function-stmt, recursive pure" :line #"^recursive pure function "]
   ["function-stmt, impure" :line #"^function \w+\(.*\) result\(r\)$"]
   ["function-stmt, recursive impure" :line #"^recursive function "]
   ["subroutine-stmt" :line #"^subroutine \w+\("] ["subroutine-stmt, recursive" :line #"^recursive subroutine "]
   ["end-function-stmt" :line #"^end function \w+$"] ["end-subroutine-stmt" :line #"^end subroutine \w+$"]
   ["decl integer(int64), value dummy" :line #"^integer\(int64\), value :: \w+$"]
   ["decl type(value), value dummy" :line #"^type\(value\), value :: \w+$"]
   ["decl type(T), intent(in) dummy" :line #"^type\(\w+\), intent\(in\) :: \w+$"]
   ["decl type(T), intent(inout) dummy" :line #"^type\(\w+\), intent\(inout\) :: \w+$"]
   ["decl integer(int64), intent(out) dummy" :line #"^integer\(int64\), intent\(out\) :: \w+$"]
   ["decl type(value), intent(out) dummy" :line #"^type\(value\), intent\(out\) :: \w+$"]
   ["decl integer(int64) local/result" :line #"^integer\(int64\) :: \w+$"]
   ["decl logical local/result" :line #"^logical :: \w+$"]
   ["decl type(value) local/result" :line #"^type\(value\) :: \w+$"]
   ["assignment to variable" :line #"^\w+ = "]
   ["assignment to component" :line #"^\w+%\w+ = "]
   ["assignment to array element of component" :line #"^\w+%\w+\(.*\) = "]
   ["call-stmt, generated procedure" :line #"^call (?!rt_|hp_)\w+\("]
   ["call-stmt, runtime (rt_*, hp_*)" :line #"^call (rt_|hp_)\w+\("]
   ["if-then-stmt" :line #"^if \(.*\) then$"] ["else-stmt" :line #"^else$"] ["end-if-stmt" :line #"^end if$"]
   ["select-case-stmt" :line #"^select case \(.*\)$"] ["case-stmt (value)" :line #"^case \(-?\d+_int64\)$"]
   ["case-stmt default" :line #"^case default$"] ["end-select-stmt" :line #"^end select$"]
   ["do-stmt (no loop-control)" :line #"^do$"] ["end-do-stmt" :line #"^end do$"]
   ["cycle-stmt" :line #"^cycle$"] ["exit-stmt" :line #"^exit$"] ["return-stmt" :line #"^return$"]
   ["int-literal _int64 (nonnegative)" :occ #"(?<![\w-])\d+_int64"]
   ["int-literal _int64 after unary minus" :occ #"(?<![\w)])-\d+_int64"]
   [".true." :occ #"\.true\."] [".false." :occ #"\.false\."]
   ["(-huge(0_int64) - 1_int64)" :occ #"\(-huge\(0_int64\) - 1_int64\)"]
   ["binary +" :occ #" \+ "] ["binary *" :occ #" \* "] ["binary - (only in the line above)" :occ #"\) - 1_int64"]
   ["unary - on a parenthesised operand (-e)" :occ #"\(-(?!\d|huge)"]
   ["==" :occ #" == "] ["<" :occ #" < "] ["<=" :occ #" <= "] [">=" :occ #" >= "]
   [".not." :occ #"\.not\. "] [".and./.or./.eqv." :occ #"\.(and|or|eqv|neqv)\."]
   ["intrinsic max(0_int64, e)" :occ #"max\(0_int64, "] ["intrinsic size(x%a, kind=int64)" :occ #"size\(\w+%\w+, kind=int64\)"]
   ["intrinsic huge" :occ #"huge\("]
   ["component ref x%c (any)" :occ #"\b\w+%\w+\b"]
   ["char-literal (rt_keyword(\"...\") only)" :occ #"\"[^\"]*\""]
   ["function ref to runtime (rt_*, hp_*)" :occ #"\b(rt|hp)_\w+\("]])
(doseq [[n k re] rows]
  (let [hits (if (= k :line) (filter #(re-find re %) lines) (mapcat #(map (constantly %) (re-seq re %)) lines))
        c (count hits)]
    (println (format "%-45s %6d   %s" n c (if (seq hits) (let [e (first (sort-by count hits))] (subs e 0 (min 90 (count e)))) "")))))
(println "non-comment lines:" (count lines))
;; references to the generated functions themselves (not the runtime's)
(let [fns (set (keep #(second (re-find #"function (\w+)\(" %)) lines))
      refs (for [l lines :when (not (re-find #"function |subroutine |^call " l))
                 [_ f] (re-seq #"(?<![%\w])(\w+)\(" l) :when (fns f)] l)]
  (println (format "%-45s %6d   %s" "function ref to a generated function" (count refs) (first (sort-by count refs)))))
