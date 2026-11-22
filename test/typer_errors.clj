;; clotran test/typer_errors.clj FILE.lms ... : lemmis.fortran/to-fortran on each, printing
;; "=== FILE" then "!!! message" for an error or "ok" (test/typer.bb checks the position and text).
(require 'lemmis.fortran)
(doseq [p *command-line-args*]
  (println "===" p)
  (try (lemmis.fortran/to-fortran (slurp p) p) (println "ok")
       (catch clotran.host.exception e (println "!!!" (ex-message e))))
  (flush))
