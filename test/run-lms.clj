;; clotran test/run-lms.clj FILE.lms ... : read each with lemmis.reader, evaluate its forms, call
;; its run (a module) or -main (a program), with reals printed tagged (lemmis.rt/*tagged*).
;; Each file's output starts with a line "=== FILE"; an error prints "!!! message".
(require 'lemmis.reader 'lemmis.rt)
(doseq [p *command-line-args*]
  (println "===" p)
  (try
    (let [forms (lemmis.reader/read-forms (slurp p) p)
          lib (second (first forms))]
      (binding [*ns* *ns*] (doseq [f forms] (eval f)))
      (binding [lemmis.rt/*tagged* true]
        (if-let [r (ns-resolve (find-ns lib) 'run)] (r) ((ns-resolve (find-ns lib) '-main)))))
    (catch clotran.host.exception e (println "!!!" (ex-message e))))
  (flush))
