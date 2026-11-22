;; clotran test/two_path_emit.clj OUTDIR FILE.lms ... : lemmis.fortran on each file, in one
;; process: OUTDIR/<i>.plain.f90 (the Fortran as a user gets it) and OUTDIR/<i>.tagged.f90
;; (PRINT through test/lms_tagio.f90), i the file's position. Prints "=== FILE" then "ok",
;; "tier-b: msg" (not translated) or "!!! msg" (an error).
(require 'lemmis.fortran)
(let [[out & files] *command-line-args*]
  (doseq [[i p] (map-indexed vector files)]
    (println "===" p)
    (try
      (let [src (slurp p)]
        (spit (str out "/" i ".plain.f90") (lemmis.fortran/to-fortran src p))
        (spit (str out "/" i ".tagged.f90") (lemmis.fortran/to-fortran src p {:tagged true}))
        (println "ok"))
      (catch clotran.host.exception e
        (println (if (:tier-b (ex-data e)) "tier-b:" "!!!") (ex-message e))))
    (flush)))
