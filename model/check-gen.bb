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
;; Then mod-ok (VALIDATION-DESIGN.md step 1): the ground side conditions,
;; evaluated on the regenerated module (below).
;;
;; Exit 1 on any difference, a function either side refuses, or a mod-ok condition not t.
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
   {:book "vmicg" :file "src/f/gen/vmc_gen.f90" :fns '[vmicg-sat] :bools '[] :raw "*vmicg-raw*"}
   ;; stobj subroutines (gen-st.lisp's g-st-module, its configuration :st)
   {:book "heapgn" :file "src/f/gen/heap_gen.inc" :fns '[hpg-spush] :bools '[] :raw "*spush-raw*" :st "*heapg-st*"}
   ;; :ctx -- callees handed over too (their formals and results), not compared
   ;; with the procedures on the hp_* externs (gen-st's extern roles, *heapg-xst*)
  {:book "heapgn" :file "src/f/gen/heap_gen.inc"
    :fns '[hpg-drain hpg-run-from-batch hpg-run-take hpg-next-tail hpg-seq-op hpg-scan-obj hpg-scan-vec hpg-run-pop
           hpg-run-new hpg-run-take-c hpg-ot hpg-or hpg-obj-at hpg-okd hpg-oi hpg-push hpg-scan-run hpg-runs-fill hpg-run-push]
    :ctx '[hpg-size-class hpg-class-len hpg-s64 hpg-add hpg-text-tag hpg-spush]
    :bools '[hpg-obj-at hpg-text-tag] :raw "*heapg-st-raw*" :st "*heapg-xst*"}])

(defn acl2! [dir input]
  (let [r (p/shell {:dir dir :in input :out :string :err :string :continue true} acl2)] (:out r)))

;; the s-expression starting at the first "(" of s, by balanced parentheses
(defn form-text [s]
  (let [i (str/index-of s "(")]
    (loop [j i d 0]
      (let [c (.charAt s j) d (case c \( (inc d) \) (dec d) d)]
        (if (zero? d) (subs s i (inc j)) (recur (inc j) d))))))

(defn dump [{:keys [book fns ctx]}]
  (let [fns (concat fns ctx)
        out (acl2! (str clotran "/model")
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

(defn translate [raws bools const fns st]
  (let [out (acl2! "."
                   (str "(include-book \"gen-inst\")\n(include-book \"gen-st-heap\")\n(set-print-case :downcase state)\n"
                        "(defun g-show (ps) (declare (xargs :mode :program))\n"
                        "  (if (endp ps) nil (prog2$ (cw \"~%PROC ~x0~%\" (car ps)) (g-show (cdr ps)))))\n"
                        "(set-iprint nil)\n"
                        "(cw \"~%RAWS ~x0~%\" (equal '(" (str/join "\n" raws) ") " const "))\n"
                        "(mv-let (e ps) " (if st (str "(g-st-module '(" (str/join "\n" raws) ") '(" (str/join " " bools) ") '(" (str/join " " fns) ") " st ")")
                                             (str "(g-module '(" (str/join "\n" raws) ") '(" (str/join " " bools) "))")) "\n"
                        "  (if e (cw \"~%GENERR ~x0~%\" e) (g-show ps)))\n(good-bye)\n"))]
    (when-not (re-find #"RAWS t" out)
      (println "check-gen: gen-inst.lisp's" const "is not what ACL2 hands over") (System/exit 1))
    (when-let [m (re-find #"GENERR (.*)" out)] (println "check-gen: gen.lisp refuses" (second m)) (System/exit 1))
    (map #(edn/read-string (form-text %)) (rest (str/split out #"\nPROC\s+")))))

(defn generated [lines fname]
  (let [start (first (keep-indexed #(when (re-find (re-pattern (str "^  (recursive )?(pure )?(function|subroutine) " fname "\\(")) %2) %1) lines))
        end (first (keep-indexed #(when (and start (> %1 start) (re-matches (re-pattern (str "  end (function|subroutine) " fname)) %2)) %1) lines))]
    (when (and start end) (subvec lines start (inc end)))))

(def failures (atom 0))
(defn compare! [file fns procs]
  (let [lines (vec (str/split-lines (slurp (str clotran "/" file))))]
    (doseq [[fn pr] (map vector fns procs)]
      (let [pr (vec pr)
            li (if (= :function (first pr)) 6 4)
            pr (assoc pr li (sort-by first (nth pr li)))
            ours (map #(str "  " %) (fproc pr))
            theirs (generated lines (nth pr 1))]
        (if (= ours theirs)
          (println (format "check-gen: %-16s %3d lines agree (%s)" fn (count ours) file))
          (do (swap! failures inc)
              (println "check-gen:" fn "DIFFERS from" file)
              (doseq [[a t] (map vector (concat ours (repeat "<none>")) (or theirs ["<not found>"]))
                      :when (not= a t)] ; first differences only
                (println "  gen.lisp:     " a) (println "  acl2-fortran: " t))))))))
(def heapg-raws (atom nil))
(doseq [{:keys [book file fns bools raw st] :as b} books]
  (let [raws (dump b)]
    (when (= raw "*heapg-st-raw*") (reset! heapg-raws raws))
    (compare! file fns (translate raws bools raw fns st))))

;; mod-ok (VALIDATION-DESIGN.md step 1, a check, not a theorem): on the module
;; regenerated from clotran's hand-over (g-st-module of heapgn's stobj
;; procedures, the hpg_spush module, g-module of heapgn's value functions, and
;; the hp_* extern table) every ground side condition the proved theorems
;; take as a hypothesis must evaluate to t: names distinct, nt-finds, xr-finds,
;; xt-finds, rt-finds, the module = the instance books' *heapg-xmod*; tab-ok on
;; hpg_spush and sfd-ok on hpg_ot/or/okd/oi. (gen-stdisch and gen-sfdisch clash
;; on g-scs-one, so tab-ok and sfd-ok are evaluated in sessions of their own.)
(defn mod-ok! [raws]
  (let [vout (acl2! "." (str "(include-book \"gen-inst\")\n(set-iprint nil)\n"
                             "(cw \"~%VMOD ~x0~%\" (mv-let (e ps) (g-module *heapgn-raw* *heapgn-bools*) (if e nil ps)))\n(good-bye)\n"))
        vmod (form-text (second (str/split vout #"\nVMOD\s+")))
        pre (str "(include-book \"gen-st-heap\")\n(set-iprint nil)\n"
                 "(defconst *raw* '(" (str/join "\n" raws) "))\n"
                 "(defconst *bools* '(hpg-obj-at hpg-text-tag))\n"
                 "(defconst *st* (append *heapg-xst* (g-st-subs *raw*)))\n"
                 "(defconst *xmod* (mv-let (e ps) (g-st-module *raw* *bools* *heapg-xfns* *heapg-xst*) (if e nil ps)))\n"
                 "(defconst *spmod* (mv-let (e ps) (g-st-module *raw* *bools* '(hpg-spush) *heapg-xst*) (if e nil ps)))\n"
                 "(defconst *procs* (append *xmod* *spmod*))\n")
        checks [["gen-st-xtake"
                 (str "(defconst *heapg-externs* (append *nt-externs* *xr-externs* (list (list :extern \"hp_set_rb\" :set-elem *h-rbi*))))\n"
                      "(defconst *mprocs* (append *procs* '" vmod " *heapg-externs*))\n"
                      "(cw \"~%MODOK names-distinct ~x0~%\" (no-duplicatesp-equal (strip-cadrs *mprocs*)))\n"
                      "(cw \"~%MODOK xmod ~x0~%\" (and *xmod* (equal *xmod* *heapg-xmod*)))\n"
                      "(cw \"~%MODOK nt-finds ~x0~%\" (let ((procs *mprocs*)) (nt-finds)))\n"
                      "(cw \"~%MODOK xr-finds ~x0~%\" (let ((procs *mprocs*)) (xr-finds)))\n"
                      "(cw \"~%MODOK xt-finds ~x0~%\" (let ((procs *mprocs*)) (xt-finds)))\n"
                      "(cw \"~%MODOK rt-finds ~x0~%\" (let ((procs *mprocs*)) (rt-finds)))\n")]
                ["gen-stdisch"
                 "(cw \"~%MODOK tab-ok ~x0~%\" (tab-ok (list (assoc-eq 'hpg-spush *raw*)) (g-defs *raw*) (g-sigs *raw* *bools*) *st* (g-defs *raw*) *procs* \"hs\" 10000))\n"]
                ["gen-sfdisch"
                 (str "(defconst *sfd* (g-defs (list (assoc-eq 'hpg-ot *raw*) (assoc-eq 'hpg-or *raw*) (assoc-eq 'hpg-okd *raw*) (assoc-eq 'hpg-oi *raw*))))\n"
                      "(cw \"~%MODOK sfd-ok ~x0~%\" (sfd-ok *sfd* (g-defs *raw*) (g-sigs *raw* *bools*) *st* *procs* \"hs\" 10000))\n")]]]
    (doseq [[book body] checks]
      (let [in (str "(include-book \"" book "\")\n" pre body "(good-bye)\n")
            _ (when-let [d (System/getenv "MODOK_DUMP")] (spit (str d "/" book ".lsp") in))
            out (acl2! "." in)
            res (re-seq #"MODOK (\S+) (\S+)" out)]
        (when (empty? res) (swap! failures inc) (println "check-gen: mod-ok: no answer from the" book "session"))
        (doseq [[_ k v] res]
          (if (= (str/lower-case v) "t")
            (println (format "check-gen: mod-ok %-14s t" k))
            (do (swap! failures inc) (println "check-gen: mod-ok" k "FAILS (" v ")"))))))))
(mod-ok! @heapg-raws)

;; gen-disch.lisp's and gen-disch-loop.lisp's copies of clotran's definitions: the
;; formals, guard and
;; body ACL2 makes of each must equal what clotran's certified books make
;; (heapgn and vmfg are read in separate sessions: they clash on sb64p)
(def disch-groups [["heapgn" '[hpg-add hpg-text-tag hpg-s64 hpg-n40 hpg-size-class hpg-class-len] "gen-disch-loop"]
                   ["vmfg" '[bnd40p sk-step sk-more ex-apstep ex-aplook vmicg-sat] "gen-disch-loop"]
                   ;; gen-st-spush.lisp's copy of the hpg stobj (its recognizer, so every
                   ;; field's place and type) and of hpg-spush with its guard's functions
                   ["heapgn" '[hpgp hpg-lens hpg-ok hpg-spush h-err h-msp h-mtagi h-mrefi h-mtag-length h-mref-length
                               update-h-err update-h-msp update-h-mtagi update-h-mrefi] "gen-st-spush"]
                   ;; gen-st-ntail.lisp's copies of hpg-next-tail, hpg-seq-op and their callees
                   ["heapgn" '[hpg-next-tail hpg-seq-op hpg-ot hpg-or hpg-okd hpg-oi hpg-obj-at h-otagi h-orefi h-okindi h-oi1i
                               h-otag-length h-oref-length h-okind-length h-oi1-length] "gen-st-ntail"]
                   ;; gen-st-drain.lisp's copies of hpg-drain and its callees
                   ["heapgn" '[hpg-drain hpg-scan-obj hpg-scan-vec hpg-scan-run hpg-push hpg-add hpg-text-tag] "gen-st-drain"]
                   ;; gen-st-rfb.lisp's copies of hpg-run-from-batch, its callees and their guards
                   ["heapgn" '[hpg-run-from-batch hpg-run-pop hpg-run-new hpg-rn-ok hpg-al-ok hpg-sw-ok hpg-s64] "gen-st-rfb"]
                   ;; gen-st-take.lisp's copies of hpg-run-take and its callees (hpg-size-class, hpg-class-len above)
                   ["heapgn" '[hpg-run-take hpg-run-take-c hpg-runs-fill hpg-run-push] "gen-st-take"]])
(defn defs-text [dir book fns]
  (let [fs (str/join " " fns)
        out (acl2! dir (str "(include-book \"" book "\")\n"
                            "(set-print-case :downcase state)\n(set-iprint nil)\n"
                            "(defun dl (fns w) (declare (xargs :mode :program))\n"
                            "  (if (endp fns) nil (cons (list (car fns) (formals (car fns) w) (guard (car fns) nil w) (body (car fns) nil w)) (dl (cdr fns) w))))\n"
                            "(cw \"~%DEFS ~x0~%\" (dl '(" fs ") (w state)))\n"
                            "(good-bye)\n"))]
    (if (str/includes? out "\nDEFS ") (form-text (second (str/split out #"\nDEFS\s+"))) "<none>")))
(doseq [[book fns ourbook] disch-groups]
  (let [theirs (defs-text (str clotran "/model") book fns)
        ours (defs-text "." ourbook fns)]
    (if (= ours theirs)
      (println (str "check-gen: " ourbook ".lisp's") (count fns) "definitions agree with clotran's" book)
      (do (swap! failures inc) (println (str "check-gen: " ourbook ".lisp's definitions DIFFER from clotran's") book)
          (println "  gen-disch: " ours) (println "  clotran:   " theirs)))))
(if (zero? @failures)
  (println "check-gen: all agree")
  (do (println "check-gen:" @failures "differ") (System/exit 1)))
