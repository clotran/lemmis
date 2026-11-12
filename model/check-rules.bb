;; check-rules.bb DRAFT.txt (from model/): each SCOPE.md row's R-number against
;; J3/24-007's text (https://j3-fortran.org/doc/year/24/24-007.pdf, as text:
;; gs -sDEVICE=txtwrite -o 24-007.txt 24-007.pdf); prints each row whose number
;; does not name its rule there, and the number that does.
(require '[clojure.string :as str])
(let [rules (into {} (for [[_ r n] (re-seq #"(R\d+)\s+([a-z][a-z0-9-]*)\s+is\b" (slurp (first *command-line-args*)))] [r n]))
      byname (group-by val rules)]
  (doseq [[_ r n] (re-seq #"(?m)^\| (R\d+) \| ([a-z0-9-]+) \|" (slurp "SCOPE.md"))]
    (when (and (not= (rules r) n) (not= r "R1535"))         ; suffix: the draft's text has a ligature
      (println r n "-- draft:" (rules r) "; the name's number:" (str/join "," (map key (byname n)))))))
