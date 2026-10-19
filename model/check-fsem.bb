#!/usr/bin/env bb
;; check-fsem.bb: fsem.lisp against the compilers. Each case is a module in
;; fsyn's syntax (the subset clotran's generator emits) and a harness: the
;; derived-type objects, the main program's variables, and probes -- print
;; a value, or call a subroutine. The case is printed as Fortran and run
;; through gfortran (-std=f2018) and flang if present, and run through
;; fsem-run in ACL2; the printed values must agree, line for line. A case
;; whose model run stops with (:error :bounds) must stop under gfortran
;; -fcheck=bounds with a nonzero exit, after the same lines.
;;
;;   bb check-fsem.bb        (from model/, the books certified)
;;
;; The harness (types module, main program, print, allocate) is outside
;; the subset; only the module m is the subset. Exit 1 on any difference.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(def acl2 (or (System/getenv "ACL2") (str (fs/parent (fs/parent here)) "/acl2/saved_acl2")))
(def work (str (fs/create-temp-dir {:prefix "check-fsem"})))

(defn sh!
  "run cmd with a deadline of secs; {:exit :out :err}, exit 124 on the deadline (the tree killed)"
  [secs opts & cmd]
  (let [proc (apply p/process (merge {:out :string :err :string} opts) cmd)
        r (deref proc (* 1000 secs) ::timeout)]
    (if (= r ::timeout)
      (do (p/destroy-tree proc) {:exit 124 :out "" :err (str "deadline of " secs " s hit")})
      r)))

;; ---- the cases ------------------------------------------------------------

(defn v [x] (list :var x))
(defn n [k] (list :int k))
(def ret '(:return))

(def cases
  [{:name "arith"
    :procs [(list :function "ops" 't 'nil [["a_" :value :int64] ["b_" :value :int64]] :int64 [["t_1" :int64]]
                  [(list :assign (v "t_1") (list :add (list :mul (v "a_") (n 3)) (list :neg (v "b_"))))
                   (list :assign (v "r") (list :add (n -1) (list :max (n 0) (v "t_1")))) ret])
            ;; a negative literal after an operator: printed (-3_int64), as the generator now writes it
            (list :function "neg" 't 'nil [["a_" :value :int64]] :int64 []
                  [(list :assign (v "r") (list :mul (list :add (v "a_") (n -3)) (n -2)))])
            (list :function "lo" 't 'nil [] :int64 []
                  [(list :assign (v "r") '(:sub (:neg (:huge)) (:int 1)))])
            (list :function "cmp" 't 'nil [["a_" :value :int64] ["b_" :value :int64]] :logical [["t_1" :logical]]
                  [(list :assign (v "t_1") (list :lt (v "a_") (v "b_")))
                   (list :if (list :not (v "t_1"))
                         [(list :assign (v "r") (list :ge (v "a_") (list :add (v "b_") (n 10))))]
                         [(list :assign (v "r") (list :eq (list :mul (n 2) (v "a_")) (v "b_")))])])]
    :probes [(list :print (list :fcall "ops" [(n 5) (n 4)]))
             (list :print (list :fcall "ops" [(n -5) (n 4)]))
             (list :print (list :fcall "ops" [(n 3037000499) (n -9)]))
             (list :print (list :fcall "neg" [(n 10)]))
             (list :print (list :fcall "neg" [(n -4)]))
             '(:print (:fcall "lo" ()))
             '(:print (:huge))
             (list :print (list :fcall "cmp" [(n 3) (n 6)]))
             (list :print (list :fcall "cmp" [(n 3) (n 7)]))
             (list :print (list :fcall "cmp" [(n 20) (n 7)]))
             (list :print (list :fcall "cmp" [(n 9) (n 7)]))]}
   {:name "bnd40p"
    :procs [(list :function "bnd40p" 't 'nil [["x_" :value :int64]] :logical []
                  [(list :if '(:true)
                         [(list :if (list :not (list :lt (v "x_") (n 0)))
                                [(list :assign (v "r") (list :not (list :lt (n 1099511627776) (v "x_")))) ret]
                                [(list :assign (v "r") '(:false)) ret])]
                         [(list :assign (v "r") '(:false)) ret])])]
    :probes (for [x [0 -1 1099511627776 1099511627777 42]] (list :print (list :fcall "bnd40p" [(n x)])))}
   {:name "select"
    :procs [(list :function "pick" 't 'nil [["k_" :value :int64]] :int64 []
                  [(list :select (v "k_")
                         [[1 [(list :assign (v "r") (n 10)) ret]]
                          [-1 [(list :assign (v "r") (n 20)) ret]]
                          [7 [(list :assign (v "r") (list :mul (v "k_") (v "k_"))) ret]]]
                         [(list :assign (v "r") (n 30)) ret])])]
    :probes (for [k [1 -1 7 0 8]] (list :print (list :fcall "pick" [(n k)])))}
   {:name "recursion"
    :procs [(list :function "fact" 't 't [["n_" :value :int64]] :int64 []
                  [(list :if (list :le (v "n_") (n 1))
                         [(list :assign (v "r") (n 1))]
                         [(list :assign (v "r") (list :mul (v "n_") (list :fcall "fact" [(list :add (n -1) (v "n_"))])))])])
            (list :function "fib" 't 't [["n_" :value :int64]] :int64 []
                  [(list :if (list :lt (v "n_") (n 2))
                         [(list :assign (v "r") (v "n_"))]
                         [(list :assign (v "r") (list :add (list :fcall "fib" [(list :add (n -1) (v "n_"))])
                                                      (list :fcall "fib" [(list :add (n -2) (v "n_"))])))])])]
    :probes (concat (for [k [0 1 5 20]] (list :print (list :fcall "fact" [(n k)])))
                    (for [k [0 1 10 20]] (list :print (list :fcall "fib" [(n k)]))))}
   {:name "loop"
    ;; the generator's tail call: new values into temporaries, then the dummies, then cycle
    :procs [(list :function "gcd" 't 'nil [["a_" :value :int64] ["b_" :value :int64]] :int64 [["t_1" :logical] ["a_1" :int64]]
                  [(list :do
                         [(list :assign (v "t_1") (list :le (v "b_") (n 0)))
                          (list :if (v "t_1")
                                [(list :assign (v "r") (v "a_")) ret]
                                [(list :assign (v "a_1") (v "b_"))
                                 ;; b mod a by subtraction: a_ - b_*(a_/b_) is not in the subset
                                 (list :do [(list :if (list :lt (v "a_") (v "b_")) ['(:exit)]
                                                  [(list :assign (v "a_") (list :add (v "a_") (list :neg (v "b_"))))])])
                                 (list :assign (v "b_") (v "a_"))
                                 (list :assign (v "a_") (v "a_1"))
                                 '(:cycle)])])])
            (list :function "sum_to" 't 'nil [["n_" :value :int64] ["acc_" :value :int64]] :int64 [["n_1" :int64] ["acc_2" :int64]]
                  [(list :do
                         [(list :if (list :le (v "n_") (n 0))
                                [(list :assign (v "r") (v "acc_")) ret]
                                [(list :assign (v "n_1") (list :add (n -1) (v "n_")))
                                 (list :assign (v "acc_2") (list :add (v "acc_") (v "n_")))
                                 (list :assign (v "n_") (v "n_1"))
                                 (list :assign (v "acc_") (v "acc_2"))
                                 '(:cycle)])])])]
    :probes [(list :print (list :fcall "gcd" [(n 1071) (n 462)]))
             (list :print (list :fcall "gcd" [(n 17) (n 5)]))
             (list :print (list :fcall "sum_to" [(n 1000) (n 0)]))
             (list :print (list :fcall "sum_to" [(n 0) (n -3)]))]}
   {:name "machine"
    ;; a stack machine in the generator's shape: a derived type updated in
    ;; place, its 0-based arrays, a run loop, select case on the opcode,
    ;; intent(out) results, and functions reading it through intent(in)
    :objects [{:name "st" :type "vm_state"
               :comps [["pc" :scalar 0] ["sp" :scalar 0] ["status" :scalar 0]
                       ;; push 6, push 7, mul, push -2, add, dup, add, halt
                       ["code" :array [1 6 1 7 3 1 -2 2 4 2 0]]
                       ["stk" :array [0 0 0 0]]]}]
    :vars [["o1" :int64] ["o2" :int64]]
    :procs [(list :function "top" 't 'nil [["st" :in "vm_state"]] :int64 []
                  [(list :assign (v "r") (list :elem "st" "stk" (list :add (n -1) (list :comp "st" "sp"))))])
            (list :function "room" 't 'nil [["st" :in "vm_state"]] :logical []
                  [(list :assign (v "r") (list :lt (list :comp "st" "sp") (list :size "st" "stk")))])
            (list :subroutine "push" 'nil [["st" :inout "vm_state"] ["x_" :value :int64]] [["i_1" :int64]]
                  [(list :assign (v "i_1") (list :comp "st" "sp"))
                   (list :assign (list :elem "st" "stk" (v "i_1")) (v "x_"))
                   (list :assign (list :comp "st" "sp") (list :add (v "i_1") (n 1)))])
            (list :subroutine "pop2" 'nil [["st" :inout "vm_state"] ["r1" :out :int64] ["r2" :out :int64]] []
                  [(list :assign (v "r1") (list :elem "st" "stk" (list :add (n -1) (list :comp "st" "sp"))))
                   (list :assign (v "r2") (list :elem "st" "stk" (list :add (n -2) (list :comp "st" "sp"))))
                   (list :assign (list :comp "st" "sp") (list :add (n -2) (list :comp "st" "sp")))])
            (list :subroutine "step" 'nil [["st" :inout "vm_state"]] [["op_1" :int64] ["mv_2" :int64] ["mv_3" :int64]]
                  [(list :assign (v "op_1") (list :elem "st" "code" (list :comp "st" "pc")))
                   (list :select (v "op_1")
                         [[1 [(list :call "push" [(v "st") (list :elem "st" "code" (list :add (list :comp "st" "pc") (n 1)))])
                              (list :assign (list :comp "st" "pc") (list :add (list :comp "st" "pc") (n 2)))]]
                          [2 [(list :call "pop2" [(v "st") (v "mv_2") (v "mv_3")])
                              (list :call "push" [(v "st") (list :add (v "mv_2") (v "mv_3"))])
                              (list :assign (list :comp "st" "pc") (list :add (list :comp "st" "pc") (n 1)))]]
                          [3 [(list :call "pop2" [(v "st") (v "mv_2") (v "mv_3")])
                              (list :call "push" [(v "st") (list :mul (v "mv_2") (v "mv_3"))])
                              (list :assign (list :comp "st" "pc") (list :add (list :comp "st" "pc") (n 1)))]]
                          [4 [(list :call "push" [(v "st") (list :fcall "top" [(v "st")])])
                              (list :assign (list :comp "st" "pc") (list :add (list :comp "st" "pc") (n 1)))]]]
                         [(list :assign (list :comp "st" "status") (n 1))])])
            (list :subroutine "run" 'nil [["st" :inout "vm_state"] ["fuel_" :value :int64] ["r" :out :int64]] [["t_1" :logical]]
                  [(list :do
                         [(list :assign (v "t_1") (list :not (list :eq (list :comp "st" "status") (n 0))))
                          (list :if (list :ge (n 0) (v "fuel_"))
                                [(list :assign (v "r") (n -1)) ret]
                                [(list :if (v "t_1")
                                       [(list :assign (v "r") (list :fcall "top" [(v "st")])) '(:exit)]
                                       [(list :call "step" [(v "st")])
                                        (list :assign (v "fuel_") (list :add (n -1) (v "fuel_")))
                                        '(:cycle)])])])])]
    :probes [(list :print (list :fcall "room" [(v "st")]))
             (list :call "run" [(v "st") (n 100) (v "o1")])
             (list :print (v "o1"))
             (list :print (list :fcall "room" [(v "st")]))
             '(:dump "st")
             (list :call "push" [(v "st") (n 5)])
             (list :call "pop2" [(v "st") (v "o1") (v "o2")])
             (list :print (v "o1")) (list :print (v "o2"))
             '(:dump "st")]}
   {:name "bounds"
    ;; the model stops at the subscript past the array (9.5.3.1p2); gfortran -fcheck=bounds must too
    :objects [{:name "st" :type "s_state" :comps [["n" :scalar 3] ["a" :array [5 6 7]]]}]
    :procs [(list :function "peek" 't 'nil [["st" :in "s_state"] ["i_" :value :int64]] :int64 []
                  [(list :assign (v "r") (list :elem "st" "a" (v "i_")))])]
    :probes [(list :print (list :fcall "peek" [(v "st") (n 0)]))
             (list :print (list :fcall "peek" [(v "st") (n 2)]))
             (list :print (list :fcall "peek" [(v "st") (n 3)]))
             (list :print (list :fcall "peek" [(v "st") (n 1)]))]}])

;; (:dump o): every component of the object, in order
(defn expand-probes [c]
  (mapcat (fn [pr]
            (if (= :dump (first pr))
              (let [o (first (filter #(= (second pr) (:name %)) (:objects c)))]
                (mapcat (fn [[cn k vs]]
                          (if (= k :scalar) [(list :print (list :comp (:name o) cn))]
                            (for [i (range (count vs))] (list :print (list :elem (:name o) cn (n i))))))
                        (:comps o)))
              [pr]))
          (:probes c)))

;; ---- ACL2 text ------------------------------------------------------------

(defn sexp [x]
  (cond (nil? x) "nil" (string? x) (pr-str x) (keyword? x) (str x) (symbol? x) (str x) (number? x) (str x)
        (sequential? x) (str "(" (str/join " " (map sexp x)) ")")
        :else (throw (ex-info (str "no sexp for " (pr-str x)) {}))))

(defn model-input [c]
  (str "(fsem-show '" (sexp (list :module "m" (:procs c)))
       " '" (sexp (for [o (:objects c)] (list (:name o) (:comps o))))
       " '" (sexp (:vars c ())) " '" (sexp (expand-probes c)) ")\n"))

(def driver-head
  (str "(include-book \"fsem\")\n"
       "(defun fsem-shows (outs)\n"
       "  (declare (xargs :mode :program))\n"
       "  (if (endp outs) nil\n"
       "    (prog2$ (cw \"OUT ~x0~%\" (let ((v (car outs))) (cond ((eq v t) 'T) ((eq v nil) 'F) (t v))))\n"
       "            (fsem-shows (cdr outs)))))\n"
       "(defun fsem-show (m objs vars probes)\n"
       "  (declare (xargs :mode :program))\n"
       "  (prog2$ (cw \"~%CASE~%\") (prog2$ (if (fmodule-p m) nil (cw \"OUT NOT-IN-SUBSET~%\"))\n"
       "     (fsem-shows (fsem-run m objs vars probes 10000000)))))\n"
       "(set-iprint nil)\n"))

;; ---- Fortran text ----------------------------------------------------------

(declare fx fstmt fproc ftype)            ; defined by fprint.clj
(load-file (str here "/fprint.clj"))

(defn etype [c e]
  (let [[op a] e]
    (case op
      (:true :false :not :eq :lt :le :ge) :logical
      :fcall (let [pr (first (filter #(= a (second %)) (:procs c)))] (nth pr 5))
      :var (second (first (filter #(= a (first %)) (:vars c))))
      :int64)))

(defn fortran [c]
  (let [lines
        (concat
         ["module types" "  use iso_fortran_env, only: int64" "  implicit none"]
         (mapcat (fn [[t comps]] (concat [(str "  type " t)]
                                        (for [[cn k] comps] (if (= k :scalar) (str "    integer(int64) :: " cn)
                                                              (str "    integer(int64), allocatable :: " cn "(:)")))
                                        [(str "  end type " t)]))
                 (distinct (for [o (:objects c)] [(:type o) (:comps o)])))
         ["end module types"
          "module m" "  use iso_fortran_env, only: int64" "  use types" "  implicit none" "contains"]
         (mapcat #(map (fn [l] (str "  " l)) (fproc %)) (:procs c))
         ["end module m"
          "program main" "  use iso_fortran_env, only: int64" "  use types" "  use m" "  implicit none"]
         (for [o (:objects c)] (str "  type(" (:type o) ") :: " (:name o)))
         (for [[x t] (:vars c)] (str "  " (ftype t) " :: " x))
         (mapcat (fn [o] (mapcat (fn [[cn k vs]]
                                   (if (= k :scalar) [(str "  " (:name o) "%" cn " = " vs "_int64")]
                                     [(str "  allocate(" (:name o) "%" cn "(0:" (dec (count vs)) "))")
                                      (str "  " (:name o) "%" cn " = [" (str/join ", " (map #(str % "_int64") vs)) "]")]))
                                 (:comps o)))
                 (:objects c))
         (mapcat (fn [pr] (if (= :print (first pr))
                            [(str "  print '(" (if (= :logical (etype c (second pr))) "l1" "i0") ")', " (fx (second pr)))]
                            (map #(str "  " %) (fstmt pr))))
                 (expand-probes c))
         ["end program main"])]
    (str (str/join "\n" lines) "\n")))

;; ---- run -------------------------------------------------------------------

(def model-outs
  (let [r (sh! 600 {:dir here :in (str driver-head (str/join (map model-input cases)) "(good-bye)\n")} "nice" acl2)
        blocks (rest (str/split (:out r) #"\nCASE\n"))]
    (when (not= (count blocks) (count cases))
      (println "check-fsem: ACL2 answered" (count blocks) "cases of" (count cases) "; its output ends:")
      (println (subs (:out r) (max 0 (- (count (:out r)) 3000))) (:err r))
      (System/exit 1))
    (mapv (fn [b] (vec (for [l (str/split-lines b) :let [[_ x] (re-find #"^OUT (.*)$" l)] :when x] (str/trim x)))) blocks)))

(def compilers (filter #(fs/which (first %)) [["gfortran" "-std=f2018"] ["flang"]]))

(def results (atom {:cases 0 :runs 0 :agree 0 :values 0 :fail 0 :skipped 0}))
(defn fail! [& msg] (swap! results update :fail inc) (apply println "FAIL" msg))

(doseq [[c want] (map vector cases model-outs)]
  (swap! results update :cases inc)
  (let [src (str work "/" (:name c) ".f90")
        err? (some #(str/starts-with? % "(:ERROR") want)
        lines (if err? (vec (butlast want)) want)]
    (spit src (fortran c))
    (when (some #{"NOT-IN-SUBSET"} want) (fail! (:name c) "is not in fsyn's subset"))
    (when (and err? (not= (last want) "(:ERROR :BOUNDS)"))
      (fail! (:name c) "the model stops with" (last want) "-- not checkable against a compiler"))
    (doseq [[fc & flags] compilers]
      (if (and err? (not= fc "gfortran"))
        (do (swap! results update :skipped inc) (println "skip" (:name c) fc "(a bounds error is checked under gfortran -fcheck=bounds)"))
        (let [exe (str work "/" (:name c) "-" fc)
              cr (apply sh! 120 {:dir work} "nice" fc (concat flags (when err? ["-fcheck=bounds"]) ["-o" exe src]))]
          (if (not= 0 (:exit cr))
            (fail! (:name c) fc "did not compile:" (:err cr))
            (let [rr (sh! 60 {:dir work} exe)
                  got (vec (map str/trim (str/split-lines (str/trim (:out rr)))))
                  got (if (= got [""]) [] got)]
              (swap! results update :runs inc)
              (swap! results update :values + (count lines))
              (cond (and err? (zero? (:exit rr))) (fail! (:name c) fc "ran to the end; the model stops at a bounds error")
                    (and (not err?) (not= 0 (:exit rr))) (fail! (:name c) fc "exited" (:exit rr) (:err rr))
                    (not= (map str/upper-case got) (map str/upper-case lines))
                    (fail! (:name c) fc "printed" got "; the model" lines)
                    :else (do (swap! results update :agree inc) (println "ok" (:name c) fc (count lines) "values" (if err? "then the bounds error" "")))))))))))

(let [{:keys [cases runs agree values fail skipped]} @results]
  (println (format "check-fsem: %d cases; compiler runs agreeing with the model %d/%d (%.0f%%); %d values compared; %d failures; %d skipped; compilers: %s"
                   cases agree runs (if (pos? runs) (* 100.0 (/ agree runs)) 0.0) values fail skipped
                   (str/join " " (map first compilers))))
  (fs/delete-tree work)
  (System/exit (if (zero? fail) 0 1)))
