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
(require '[clojure.pprint] '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str] '[clojure.edn :as edn])
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
  (let [r (p/shell {:dir dir :in input :out :string :err :string :continue true} "sh" "-c" (str "ulimit -t 200; exec " acl2))] (:out r)))

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
;; xt-finds, rt-finds, xp-finds (p-sorc-d's, gen-st-xpush), the module = the instance books' *heapg-xmod*; tab-ok on
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
        checks [["gen-st-xpush"
                 (str "(defconst *heapg-externs* (append *nt-externs* *xr-externs* (list (list :extern \"hp_set_rb\" :set-elem *h-rbi*)) *xd-externs*))\n"
                      "(defconst *mprocs* (append *procs* '" vmod " *heapg-externs*))\n"
                      "(cw \"~%MODOK names-distinct ~x0~%\" (no-duplicatesp-equal (strip-cadrs *mprocs*)))\n"
                      "(cw \"~%MODOK xmod ~x0~%\" (and *xmod* (equal *xmod* *heapg-xmod*)))\n"
                      "(cw \"~%MODOK nt-finds ~x0~%\" (let ((procs *mprocs*)) (nt-finds)))\n"
                      "(cw \"~%MODOK xr-finds ~x0~%\" (let ((procs *mprocs*)) (xr-finds)))\n"
                      "(cw \"~%MODOK xt-finds ~x0~%\" (let ((procs *mprocs*)) (xt-finds)))\n"
                      "(cw \"~%MODOK rt-finds ~x0~%\" (let ((procs *mprocs*)) (rt-finds)))\n"
                      "(cw \"~%MODOK xp-finds ~x0~%\" (let ((procs *mprocs*)) (xp-finds)))\n")]
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

;; Coverage (model/COVERAGE-GEN.md): every function acl2-fortran generates, from
;; its own book table (clotran's scripts/acl2-fortran), is handed over by ACL2,
;; classified, and, when g-module (integers and booleans, no stobj, no value) or
;; g-st-module on the heapgn stobj (*heapg-xst*) accepts it, regenerated and
;; compared with the generated file by the same line-for-line compare as above.
;; The set compared per file is pinned in check-gen-cover.edn (a function
;; dropping out, or coming in, is a failure: CHECKGEN_UPDATE=1 rewrites it).
(def table
  (let [src (slurp (str clotran "/scripts/acl2-fortran"))
        forms (with-open [r (java.io.PushbackReader. (java.io.StringReader. (subs src (str/index-of src "(def books"))))] (read r))]
    (second (nth forms 2))))
(def st-config {"heapg" "*heapg-xst*" "arraymapg" "(rs *heapg-xst*)"})
;; a book with one stobj and no externs: its configuration read off acl2-fortran's table
;; (:stobjs, :stobj-types, :fields, :array-names with :prefix, the value arrays left out)
(defn derived-config [v]
  (when (and (= 1 (count (:stobjs v))) (empty? (:externs v)) (empty? (:local-arrays v)))
    (let [[[sym var]] (seq (:stobjs v)) ty (get (:stobj-types v) var)
          pre (get (:prefix v) var "")]
      (str "(g-st-cfg '((" sym " \"" var "\" \"" ty "\")) '("
           (str/join " " (for [[acc [o f]] (:fields v)] (str "(" acc " \"" o "\" \"" f "\")")))
           ") '(" (str/join " " (for [a (get (:array-names v) var) :when (not (contains? (:value-arrays v) a))]
                                  (str "(" pre a " \"" var "\" \"" a "\")"))) "))"))))
;; arraymapg's stobj type is amg_heap, where heapgn's is heap_state
(def st-prelude "(defun rs (x) (declare (xargs :mode :program)) (cond ((consp x) (cons (rs (car x)) (rs (cdr x)))) ((equal x \"heap_state\") \"amg_heap\") (t x)))\n")

(defn dump-all [bk fns]
  (let [fl (str/join " " fns)
        out (acl2! (str clotran "/model")
                   (str "(include-book \"" bk "\")\n(set-print-case :downcase state)\n"
                        "(defun dump-fns (fns state)\n  (declare (xargs :mode :program :stobjs state))\n"
                        "  (if (endp fns) state\n    (let ((fn (car fns)) (w (w state)))\n"
                        "      (prog2$ (cw \"~%FN ~x0~%\" (list fn (formals fn w) (stobjs-out fn w) (eq (symbol-class fn w) :common-lisp-compliant) (body fn nil w)))\n"
                        "              (dump-fns (cdr fns) state)))))\n"
                        "(defun dump-sin (fns state)\n  (declare (xargs :mode :program :stobjs state))\n"
                        "  (if (endp fns) state\n    (prog2$ (cw \"~%SIN ~x0~%\" (list (car fns) (stobjs-in (car fns) (w state))))\n"
                        "            (dump-sin (cdr fns) state))))\n"
                        "(set-iprint nil)\n(dump-fns '(" fl ") state)\n(dump-sin '(" fl ") state)\n(good-bye)\n"))
        blocks (map form-text (rest (str/split out #"\nFN\s+")))
        sins (into {} (map (fn [[_ f s]] [f (not (re-find #"^\(nil( nil)*\)$" (str/trim s)))]) (re-seq #"\nSIN \((\S+) (\([^)]*\))\)" out)))]
    (when (not= (count blocks) (count fns))
      (println "check-gen: ACL2 did not hand over" bk "'s functions") (System/exit 1))
    (mapv (fn [fn raw] {:fn fn :raw raw :stobj? (get sins (name fn))
                        :stobj-out? (not (re-find #"^\(\S+ \([^)]*\) \(nil( nil)*\)" (str/replace raw #"\s+" " ")))})
          fns blocks)))

(defn try-session [kind raws bools fns st]
  ;; kind :pure -- g-module, cumulative; :st -- g-st-module, one function at a time over all raws
  (let [out (acl2! "."
                   (str "(include-book \"" (if (= kind :pure) "gen-inst" "gen-st-heap") "\")\n(set-print-case :downcase state)\n(set-iprint nil)\n" st-prelude
                        "(defconst *raws* '(" (str/join "\n" raws) "))\n"
                        (if (= kind :pure)
                          (str "(defun try-all (rs acc state) (declare (xargs :mode :program :stobjs state))\n"
                               "  (if (endp rs) state\n    (mv-let (e ps) (g-module (append acc (list (car rs))) '(" (str/join " " bools) "))\n"
                               "      (declare (ignorable ps))\n"
                               "      (if (or e (not ps)) (prog2$ (cw \"~%REFUSE ~x0 ~x1~%\" (caar rs) e) (try-all (cdr rs) acc state))\n"
                               "        (prog2$ (cw \"~%ACCEPT ~x0~%\" (caar rs)) (try-all (cdr rs) (append acc (list (car rs))) state))))))\n"
                               "(try-all *raws* nil state)\n")
                          (str "(defun try-all (cs state) (declare (xargs :mode :program :stobjs state))\n"
                               "  (if (endp cs) state\n    (mv-let (e ps) (g-st-module *raws* '(" (str/join " " bools) ") (list (car cs)) " st ")\n"
                               "      (declare (ignorable ps))\n"
                               "      (prog2$ (if (or e (not ps)) (cw \"~%REFUSE ~x0 ~x1~%\" (car cs) e) (cw \"~%ACCEPT ~x0~%\" (car cs)))\n"
                               "         (try-all (cdr cs) state)))))\n"
                               "(try-all '(" (str/join " " fns) ") state)\n"))
                        "(good-bye)\n"))]
    (when (and (seq fns) (empty? (re-seq #"\n(ACCEPT|REFUSE) " out)))
      (println "check-gen: the" (name kind) "session (200s of CPU) gave no answer") (System/exit 1))
    (into {} (map (fn [[_ k f r]] [f (if (= k "ACCEPT") :ok (str/trim (or r "")))])
                  (re-seq #"\n(ACCEPT|REFUSE) (\S+)(.*)" out)))))

(defn translate* [raws bools fns st]
  (let [out (acl2! "."
                   (str "(include-book \"" (if st "gen-st-heap" "gen-inst") "\")\n(set-print-case :downcase state)\n" st-prelude
                        "(defun g-show (ps) (declare (xargs :mode :program))\n"
                        "  (if (endp ps) nil (prog2$ (cw \"~%PROC ~x0~%\" (car ps)) (g-show (cdr ps)))))\n(set-iprint nil)\n"
                        "(mv-let (e ps) " (if st (str "(g-st-module '(" (str/join "\n" raws) ") '(" (str/join " " bools) ") '(" (str/join " " fns) ") " st ")")
                                               (str "(g-module '(" (str/join "\n" raws) ") '(" (str/join " " bools) "))")) "\n"
                        "  (if e (cw \"~%GENERR ~x0~%\" e) (g-show ps)))\n(good-bye)\n"))]
    (when-let [m (re-find #"GENERR (.*)" out)] (println "check-gen: gen.lisp refuses" (second m)) (System/exit 1))
    (map #(edn/read-string (form-text %)) (rest (str/split out #"\nPROC\s+")))))

(defn compare-quiet [file procs]
  (let [lines (vec (str/split-lines (slurp (str clotran "/" file))))]
    (vec (for [pr procs
               :let [pr (vec pr)
                     li (if (= :function (first pr)) 6 4)
                     pr (assoc pr li (sort-by first (nth pr li)))
                     ours (map #(str "  " %) (fproc pr))
                     theirs (generated lines (nth pr 1))]]
           [(nth pr 1) (= ours theirs)
            (when-not (= ours theirs)
              (first (for [[a t] (map vector (concat ours (repeat "<none>")) (or theirs ["<not found>"])) :when (not= a t)] [a t])))]))))

(def cover-file (str (fs/parent (fs/absolutize *file*)) "/check-gen-cover.edn"))
(def cover-old (if (fs/exists? cover-file) (edn/read-string (slurp cover-file)) {}))
(def cover-new (atom (sorted-map)))
(def report (atom []))
(doseq [bk-key (sort (keys table))
        :when (or (not (System/getenv "COVER_ONLY")) (= bk-key (System/getenv "COVER_ONLY")))
        :let [v (get table bk-key) bk (or (:book v) bk-key) file (:out v)
              fns (vec (distinct (:fns v)))
              valued (fn [f] (or (contains? (:value-fns v) f) (seq (get (:value-formals v) f))))
              rows (dump-all bk fns)
              bools (filter (set fns) (:bool-fns v))
              pure (filter #(and (not (:stobj? %)) (not (:stobj-out? %)) (not (valued (:fn %)))) rows)
              pure-res (if (seq pure) (try-session :pure (map :raw pure) (filter (set (map :fn pure)) (:bool-fns v)) nil nil) {})
              st (or (get st-config bk-key) (derived-config v))
              stobj-rows (filter #(or (:stobj? %) (:stobj-out? %)) rows)
              st-res (if (and st (seq stobj-rows)) (try-session :st (map :raw rows) bools (map :fn stobj-rows) st) {})
              ok0 (set (concat (map #(name (:fn %)) (filter #(= :ok (get pure-res (name (:fn %)))) pure)) (map #(name (:fn %)) (filter #(= :ok (get st-res (name (:fn %)))) stobj-rows))))
              fnnames (set (map (comp name :fn) rows))
              callees (fn [r] (disj (set (filter fnnames (re-seq #"[^\s()']+" (str/replace-first (:raw r) #"^\(\S+" "")))) (name (:fn r))))
              okset (loop [s ok0] (let [s2 (set (filter (fn [r] (every? s (callees r))) (filter #(s (name (:fn %))) rows)))
                                         s2 (set (map (comp name :fn) s2))] (if (= s s2) s (recur s2))))
              acc-pure (filter #(okset (name (:fn %))) (filter #(= :ok (get pure-res (name (:fn %)))) pure))
              acc-st (filter #(okset (name (:fn %))) (filter #(= :ok (get st-res (name (:fn %)))) stobj-rows))
              res-pure (when (seq acc-pure) (compare-quiet file (translate* (map :raw acc-pure) (filter (set (map :fn acc-pure)) bools) nil nil)))
              res-st (when (seq acc-st) (compare-quiet file (translate* (map :raw rows) bools (map :fn acc-st) st)))
              bad (remove second (concat res-pure res-st))
              okn (count (filter second (concat res-pure res-st)))
              names (vec (sort (map #(str (first %)) (filter second (concat res-pure res-st)))))
              why (fn [r] (cond (valued (:fn r)) "value-typed formals/results (type(value))"
                                (and (or (:stobj? r) (:stobj-out? r)) (not st)) "stobj without a gen-st configuration"
                                :else (let [x (get (merge pure-res st-res) (name (:fn r)))] (if (= x :ok) (str "calls " (str/join " " (remove okset (callees r))) ", not regenerated") (str "g-module/g-st-module refuses " x)))))]]
  (swap! cover-new assoc file (vec (sort (concat (get @cover-new file) names))))
  (swap! report conj {:file file :book bk :total (count fns) :compared okn
                      :pure (count pure) :stobj (count stobj-rows) :value (count (filter #(valued (:fn %)) rows))
                      :refused (mapv (fn [r] [(name (:fn r)) (why r)]) (remove #(or (some (fn [x] (= (name (:fn x)) (name (:fn %)))) acc-pure) (some (fn [x] (= (name (:fn x)) (name (:fn %)))) acc-st)) rows))})
  (println (format "check-gen: coverage %-28s %3d of %3d procedures regenerated and compared, %d differ" file okn (count fns) (count bad)))
  (doseq [[n _ d] bad] (swap! failures inc) (println "check-gen:" n "DIFFERS from" file) (println "  gen.lisp:     " (first d)) (println "  acl2-fortran: " (second d))))
(spit "../build/check-gen-coverage.edn" (pr-str @report))
(if (System/getenv "CHECKGEN_UPDATE")
  (spit cover-file (with-out-str (clojure.pprint/pprint (into {} @cover-new))))
  (when (not= (into {} @cover-new) cover-old)
    (swap! failures inc)
    (println "check-gen: the set of functions compared differs from check-gen-cover.edn (CHECKGEN_UPDATE=1 to rewrite it)")))

;; Parsing (VALIDATION-DESIGN.md step 2, first half): every generated file, read
;; by Lemmis's proved parser (frun's fortran-parse: flex, fps, fpu), must be a
;; program of the grammar. A .inc is a module's contains part, so it is wrapped
;; in "module m / use iso_fortran_env, only: int64 / implicit none / contains".
;; heaprt_gen.inc is the one known refusal (see COVERAGE-GEN.md); a change in
;; either direction fails. What is NOT done: comparing the parse trees with the
;; regenerated fsyn (fparse's trees are the full grammar's, nested expression
;; levels deep; the tree-to-fsyn pass is not written), so the printer is still trusted.
(def parse-refused #{"src/f/gen/heaprt_gen.inc"})
(doseq [f (sort (map :out (vals table)))]
  (let [t (slurp (str clotran "/" f))
        mod? (boolean (re-find #"(?m)^\s*module\s" t))
        tmp (str (fs/absolutize "../build") "/check-gen-parse.f90")
        _ (spit tmp (if mod? t (str "module m\n  use iso_fortran_env, only: int64\n  implicit none\ncontains\n" t "\nend module m\n")))
        out (acl2! "." (str "(include-book \"frun\")\n(set-iprint nil)\n(set-print-case :downcase state)\n"
                            "(make-event (let ((s (read-file-into-string \"" tmp "\"))) (mv-let (ok r) (fortran-parse s nil) (prog2$ (cw \"~%PARSE ~x0 ~x1~%\" ok (if ok 0 r)) (value '(value-triple nil))))))\n(good-bye)\n"))
        ok (= "t" (str/lower-case (or (second (re-find #"PARSE (\S+)" out)) "?")))
        expect (not (parse-refused f))]
    (if (= ok expect)
      (println (format "check-gen: parse    %-28s %s" f (if ok "accepted by fparse" "refused by fparse (known)")))
      (do (swap! failures inc) (println "check-gen: parse" f (if ok "accepted, but listed as refused" "REFUSED by fparse"))))))

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
