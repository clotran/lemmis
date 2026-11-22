;; clotran test/run-plain.clj FILE.lms ... : like run-lms.clj, reals printed as clotran prints them
;; (no tags), and a read error printed as "!!! message" (test/ext.bb compares both).
(require 'lemmis.reader 'lemmis.rt)
(doseq [p *command-line-args*]
  (println "===" p)
  (try
    (let [forms (lemmis.reader/read-forms (slurp p) p) lib (second (first forms))]
      (binding [*ns* *ns*] (doseq [f forms] (eval f)))
      (if-let [r (ns-resolve (find-ns lib) 'run)] (r) ((ns-resolve (find-ns lib) '-main))))
    (catch clotran.host.exception e (println "!!!" (ex-message e))))
  (flush))
