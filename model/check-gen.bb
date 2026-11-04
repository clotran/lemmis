#!/usr/bin/env bb
;; check-gen.bb: gen.lisp's translation against clotran's scripts/acl2-fortran,
;; on clotran's own functions. For each book: ACL2, in clotran's model/ and
;; reading only its certified books, hands over the functions' translated
;; bodies as acl2-fortran takes them; gen.lisp's g-module translates them to
;; fsyn; fprint.clj prints that; the text must equal the generated function
;; in clotran's src/f/gen/*, line for line. One difference is the printer's,
;; and meaning-preserving: the locals are declared sorted by name, as the
;; generator declares them (fsem's meaning does not depend on their order).
;;
;;   CLOTRAN=/path/to/clotran ACL2=/path/to/saved_acl2 bb check-gen.bb   (from model/, gen certified)
;;
;; Exit 1 on any difference, or a function either side refuses.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str] '[clojure.edn :as edn])
(load-file "fprint.clj")

(def acl2 (or (System/getenv "ACL2") "/Users/james/clotran/acl2/saved_acl2"))
(def clotran (or (System/getenv "CLOTRAN") "/Users/james/clotran/clotran"))

;; the slice: every function of these books with no stobj, no value and no
;; runtime call -- integers and booleans only (GEN.md)
(def books
  [{:book "heapgn" :file "src/f/gen/heap_gen.inc"
    :fns '[hpg-add hpg-text-tag hpg-s64 hpg-n40 hpg-size-class hpg-class-len] :bools '[hpg-text-tag] :raw "*heapgn-raw*"}
   {:book "vmfg" :file "src/f/gen/vm_gen.f90"
    :fns '[bnd40p sk-step sk-more ex-aplook ex-apstep] :bools '[bnd40p sk-more] :raw "*vmfg-raw*"}
   {:book "vmicg" :file "src/f/gen/vmc_gen.f90" :fns '[vmicg-sat] :bools '[] :raw "*vmicg-raw*"}])

(defn acl2! [dir input]
  (let [r (p/shell {:dir dir :in input :out :string :err :string :continue true} acl2)] (:out r)))

;; the s-expression starting at the first "(" of s, by balanced parentheses
(defn form-text [s]
  (let [i (str/index-of s "(")]
    (loop [j i d 0]
      (let [c (.charAt s j) d (case c \( (inc d) \) (dec d) d)]
        (if (zero? d) (subs s i (inc j)) (recur (inc j) d))))))

(defn dump [{:keys [book fns]}]
  (let [out (acl2! (str clotran "/model")
                   (str "(include-book \"" book "\")\n(set-print-case :downcase state)\n"
                        "(defun dump-fns (fns state)\n  (declare (xargs :mode :program :stobjs state))\n"
                        "  (if (endp fns) state\n    (let ((fn (car fns)) (w (w state)))\n"
                        "      (prog2$ (cw \"~%FN ~x0~%\" (list fn (formals fn w) (stobjs-out fn w)\n"
                        "                 (eq (symbol-class fn w) :common-lisp-compliant) (body fn nil w)))\n"
                        "              (dump-fns (cdr fns) state)))))\n"
                        "(set-iprint nil)\n(dump-fns '(" (str/join " " fns) ") state)\n(good-bye)\n"))
        blocks (map form-text (rest (str/split out #"\nFN\s+")))]
    (when (not= (count blocks) (count fns))
      (println "check-gen: ACL2 did not hand over" book "'s functions") (System/exit 1))
    blocks))

(defn translate [raws bools const]
  (let [out (acl2! "."
                   (str "(include-book \"gen-inst\")\n(set-print-case :downcase state)\n"
                        "(defun g-show (ps) (declare (xargs :mode :program))\n"
                        "  (if (endp ps) nil (prog2$ (cw \"~%PROC ~x0~%\" (car ps)) (g-show (cdr ps)))))\n"
                        "(set-iprint nil)\n"
                        "(cw \"~%RAWS ~x0~%\" (equal '(" (str/join "\n" raws) ") " const "))\n"
                        "(mv-let (e ps) (g-module '(" (str/join "\n" raws) ") '(" (str/join " " bools) "))\n"
                        "  (if e (cw \"~%GENERR ~x0~%\" e) (g-show ps)))\n(good-bye)\n"))]
    (when-not (re-find #"RAWS t" out)
      (println "check-gen: gen-inst.lisp's" const "is not what ACL2 hands over") (System/exit 1))
    (when-let [m (re-find #"GENERR (.*)" out)] (println "check-gen: gen.lisp refuses" (second m)) (System/exit 1))
    (map #(edn/read-string (form-text %)) (rest (str/split out #"\nPROC\s+")))))

(defn generated [lines fname]
  (let [start (first (keep-indexed #(when (re-find (re-pattern (str "^  (recursive )?(pure )?function " fname "\\(")) %2) %1) lines))
        end (first (keep-indexed #(when (and start (> %1 start) (= %2 (str "  end function " fname))) %1) lines))]
    (when (and start end) (subvec lines start (inc end)))))

(def failures (atom 0))
(doseq [{:keys [book file fns bools raw] :as b} books]
  (let [procs (translate (dump b) bools raw)
        lines (vec (str/split-lines (slurp (str clotran "/" file))))]
    (doseq [[fn pr] (map vector fns procs)]
      (let [pr (vec pr)
            pr (assoc pr 6 (sort-by first (nth pr 6)))
            ours (map #(str "  " %) (fproc pr))
            theirs (generated lines (nth pr 1))]
        (if (= ours theirs)
          (println (format "check-gen: %-16s %3d lines agree (%s)" fn (count ours) file))
          (do (swap! failures inc)
              (println "check-gen:" fn "DIFFERS from" file)
              (doseq [[a t] (map vector (concat ours (repeat "<none>")) (or theirs ["<not found>"]))
                      :when (not= a t)] ; first differences only
                (println "  gen.lisp:     " a) (println "  acl2-fortran: " t))))))))
(if (zero? @failures)
  (println "check-gen: all agree")
  (do (println "check-gen:" @failures "differ") (System/exit 1)))
