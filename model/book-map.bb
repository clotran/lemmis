#!/usr/bin/env bb
;; book-map.bb (from the repo root; `make book-map`): build/book-map.txt, one line
;; per defun/defthm/defun-sk/defmacro/defconst (and the like) in each model/*.lisp:
;; `book:line event-name`. grep it instead of reading books.
(require '[clojure.string :as str] '[babashka.fs :as fs])
(def kinds "defun|defund|defun-sk|defun-nx|defund-nx|defthm|defthmd|defmacro|defconst|defabbrev|defrec|defstobj|defun-inline|defmacro-last|define")
(let [re (re-pattern (str "(?i)^\\((?:" kinds ")\\s+([^\\s()]+)"))
      out (for [f (sort (map str (fs/glob "model" "*.lisp")))
                :let [b (fs/strip-ext (fs/file-name f))]
                [i l] (map-indexed vector (str/split-lines (slurp f)))
                :let [m (re-find re l)] :when m]
            (str b ":" (inc i) " " (second m)))]
  (fs/create-dirs "build")
  (spit "build/book-map.txt" (str (str/join "\n" out) "\n"))
  (println "book-map:" (count out) "events in build/book-map.txt"))
