;; CLOTRAN_PATH=<lemmis>/src:<lemmis>/examples clotran examples/run.clj
;; clotran calling Lemmis: require finds geo/shapes.lms and geo/report.lms (after .cljf,
;; .cljc and .clj) and reads them with lemmis.reader. geo.shapes in turn uses a clotran
;; namespace (geo.stats, a .cljf) and clojure.string; geo.report uses geo.shapes.
(require '[geo.shapes :as shapes] '[geo.report :as report])

(println (shapes/area 2.0))                       ; Fortran's real(8) arithmetic
(let [a (fortran/make-array "real8" 3)]
  (shapes/areas a 3)                               ; a subroutine writes the array in place
  (println (vec a)))
(println (clojure.string/trim (shapes/report [1 2 3])))
(println (report/total_area 3))
(println (report/count_kept (range 1 10) #(> % 50.0)))   ; a Clojure fn passed into Lemmis
