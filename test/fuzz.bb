#!/usr/bin/env bb
;; test/fuzz.bb [seed] [count] : random Lemmis modules drawn from version 0's subset, each run
;; three ways by test/cases.bb (gfortran -std=f2018, flang, clotran through lemmis.reader) and
;; compared. A module: an integer function, a real(8) function, a subroutine with intent(in),
;; (inout) and (out) dummies, and run(), whose statements are assignments to integer(4),
;; integer(8), real(8), real(4) and logical variables and to array elements (one array with a
;; lower bound of 0), IF constructs and IF statements, DO with a step of either sign, DO WHILE,
;; DO with EXIT, CYCLE, RETURN, CALL, PRINT *. Values stay small (an integer assignment
;; reduces MOD 97, a real one MOD 100, a divisor is a nonzero literal) so nothing overflows
;; and every real is finite: nothing the standard leaves to the processor. Failing programs
;; are kept in test/fuzz-found/ as regression cases. Exit 1 on any disagreement.
(require '[babashka.process :as p] '[babashka.fs :as fs] '[clojure.string :as str])

(def here (str (fs/parent (fs/absolutize *file*))))
(def seed (parse-long (or (first *command-line-args*) "1")))
(def n (parse-long (or (second *command-line-args*) "20")))
(def rnd (java.util.Random. seed))
(defn r [k] (.nextInt rnd k))
(defn pick [xs] (nth xs (r (count xs))))

(def ivars ["i" "j" "k"])
(def i8vars ["m8"])
(def rvars ["x" "y"])
(def svars ["s"])
(def lvars ["p" "q"])

(defn ilit [] (let [k (- (r 41) 20)] (if (neg? k) (str "(" k ")") (str k))))
(defn nzlit [] (pick ["2" "3" "5" "7" "(-3)" "11"]))
(defn rlit [] (pick ["0.5d0" "1.25d0" "0.1d0" "3.0d0" "(-2.5d0)" "0.3d0" "7.0d0"]))
(defn slit [] (pick ["1.5" "(-0.1)" "0.3" "2.0" "0.25"]))

(declare iexp rexp)
(defn aidx [] (pick [(str (inc (r 5))) (str "modulo(" (pick ivars) ", 5) + 1")]))
(defn bidx [] (pick [(str (r 5)) (str "modulo(" (pick ivars) ", 5)")]))
(defn iatom [d]
  (case (r (if (pos? d) 9 4))
    0 (ilit) 1 (pick ivars) 2 (pick ivars) 3 (str "a(" (aidx) ")")
    4 (str "mod(" (iexp (dec d)) ", " (nzlit) ")")
    5 (str "modulo(" (iexp (dec d)) ", " (nzlit) ")")
    6 (str "abs(" (iexp (dec d)) ")")
    7 (str (pick ["min" "max"]) "(" (iexp (dec d)) ", " (iexp (dec d)) ")")
    8 (str "fi(" (iexp (dec d)) ")")))
(defn iexp [d]
  (case (r (if (pos? d) 6 2))
    (0 1) (iatom d)
    2 (str (iexp (dec d)) " + " (iatom (dec d)))
    3 (str (iexp (dec d)) " - " (iatom (dec d)))
    4 (str (iatom (dec d)) " * " (iatom (dec d)))
    5 (str "(" (iexp (dec d)) ") / " (nzlit))))
(defn ratom [d]
  (case (r (if (pos? d) 8 4))
    0 (rlit) 1 (pick rvars) 2 (str "b(" (bidx) ")") 3 (str "real(" (pick ivars) ", 8)")
    4 (str "abs(" (rexp (dec d)) ")")
    5 (str "fr(" (rexp (dec d)) ")")
    6 (str "(" (rexp (dec d)) ") ** 2")
    7 (str "sqrt(abs(" (rexp (dec d)) "))")))
(defn rexp [d]
  (case (r (if (pos? d) 6 2))
    (0 1) (ratom d)
    2 (str (rexp (dec d)) " + " (ratom (dec d)))
    3 (str (rexp (dec d)) " - " (ratom (dec d)))
    4 (str (ratom (dec d)) " * " (ratom (dec d)))
    5 (str "(" (rexp (dec d)) ") / " (rlit))))
(defn sexp [d] (case (r 4) 0 (slit) 1 (pick svars) 2 (str (pick svars) " * " (slit)) 3 (str "real(" (pick ivars) ") + " (slit))))
(defn cnd [d]
  (case (r (if (pos? d) 6 3))
    0 (str (iexp 1) " " (pick ["<" "<=" ">" ">=" "==" "/="]) " " (iexp 1))
    1 (str (rexp 1) " " (pick ["<" ">" ">="]) " " (rexp 1))
    2 (pick lvars)
    3 (str (cnd (dec d)) " .and. " (cnd (dec d)))
    4 (str (cnd (dec d)) " .or. " (cnd (dec d)))
    5 (str ".not. (" (cnd (dec d)) ")")))

(defn sb-call [I] (let [u (pick ivars) v (pick (remove #{u} ivars))] (str I "call sb(" u ", " v ", " (pick rvars) ")")))
(defn ind [k] (apply str (repeat (* 2 k) " ")))
(declare stmts)
(defn stmt [d k loop?]
  (let [I (ind k)]
    (case (r (if (pos? d) 16 9))
      0 (str I (pick ivars) " = mod(" (iexp 2) ", 97)")
      1 (str I (pick rvars) " = mod(" (rexp 2) ", 100.0d0) + 0.0d0")
      2 (str I "a(" (aidx) ") = mod(" (iexp 2) ", 97)")
      3 (str I "b(" (bidx) ") = mod(" (rexp 1) ", 100.0d0) + 0.0d0")
      4 (str I (pick svars) " = mod(" (sexp 1) ", 100.0) + 0.0")
      5 (str I (pick lvars) " = " (cnd 1))
      6 (str I "m8 = mod(m8 * 31 + " (pick ivars) ", 1000003_8)")
      7 (str I "print *, " (str/join ", " (repeatedly (inc (r 3)) #(pick (concat ivars rvars svars lvars i8vars ["a(1)" "b(0)"])))))
      8 (if loop? (str I "if (" (cnd 1) ") " (pick ["exit" "cycle"])) (sb-call I))
      9 (str I "if (" (cnd 2) ") then\n" (stmts (dec d) (inc k) loop?)
           (when (zero? (r 2)) (str I "else if (" (cnd 1) ") then\n" (stmts (dec d) (inc k) loop?)))
           (when (zero? (r 2)) (str I "else\n" (stmts (dec d) (inc k) loop?)))
           I "end if")
      (10 11) (let [v (pick ivars) a (- (r 9) 3) b (- (r 13) 3) s (pick ["" ", 2" ", -1" ", 3" ", -2"])]
                (str I "do " v " = " a ", " b s "\n"
                     (stmts (dec d) (inc k) true v) I "end do\n" I "print *, " v))
      12 (str I "w = 0\n" I "do while (w < " (inc (r 6)) ")\n" I "  w = w + 1\n" (stmts (dec d) (inc k) false "w") I "end do")
      13 (str I "do\n" (stmts (dec d) (inc k) false) I "  if (" (cnd 1) ") exit\n" I "  exit\n" I "end do")
      14 (sb-call I)
      15 (str I "if (" (cnd 1) ") return"))))

(defn stmts
  ([d k loop?] (stmts d k loop? nil))
  ([d k loop? busy]
   (str/join (for [_ (range (inc (r 4)))]
               (let [s (stmt d k loop?)]
                 ;; never assign a DO variable inside its loop
                 (if (and busy (or (re-find (re-pattern (str "(?m)^\\s*(do )?" busy " = ")) s)
                                    (re-find (re-pattern (str "sb\\([a-z]+, " busy ",")) s))) "" (str s "\n")))))))

(defn program [name]
  (str "module " name "\n  implicit none\ncontains\n"
       "  integer function fi(u)\n    integer, intent(in) :: u\n    fi = mod(u * 3 + 1, 97)\n  end function fi\n"
       "  real(8) function fr(t)\n    real(8), intent(in) :: t\n    fr = mod(t * 0.5d0 + 1.0d0, 100.0d0) + 0.0d0\n  end function fr\n"
       "  subroutine sb(u, v, t)\n    integer, intent(in) :: u\n    integer, intent(inout) :: v\n    real(8), intent(out) :: t\n"
       "    v = mod(v + u, 97)\n    t = 0.5d0 * u\n  end subroutine sb\n"
       "  subroutine run()\n    integer :: i, j, k, w\n    integer(8) :: m8\n    real(8) :: x, y\n    real :: s\n    logical :: p, q\n"
       "    integer :: a(5)\n    real(8) :: b(0:4)\n"
       "    i = 1; j = 2; k = 3; w = 0; m8 = 7; x = 0.5d0; y = 1.5d0; s = 0.25; p = .true.; q = .false.\n"
       "    a(1) = 1; a(2) = 2; a(3) = 3; a(4) = 4; a(5) = 5\n    b(0) = 0.0d0; b(1) = 1.0d0; b(2) = 2.0d0; b(3) = 3.0d0; b(4) = 4.0d0\n"
       (stmts 3 2 false)
       "    print *, i, j, k, m8, x, y, s, p, q\n    print *, a, b\n"
       "  end subroutine run\nend module " name "\n"))

;; free form's lines are at most 132 characters (6.3.2.1): continue a long one with &
(defn wrap [line]
  (if (<= (count line) 100) line
      (let [i (str/last-index-of line " " 90)]
        (if (and i (> i 20)) (str (subs line 0 i) " &\n      &" (wrap (subs line i))) line))))

(defn -main []
  (let [dir (str (fs/create-temp-dir {:prefix "lemmis-fuzz"}))]
    (dotimes [i n] (spit (str dir "/fz" seed "_" i ".lms") (str/join "\n" (map wrap (str/split-lines (program (str "fz" seed "_" i)))))))
    (println (str "fuzz seed " seed ", " n " programs"))
    (let [res (p/shell {:continue true :extra-env {"LEMMIS_KEEP" (str here "/fuzz-found")}}
                       "bb" (str here "/cases.bb") dir)]
      (fs/delete-tree dir)
      (System/exit (:exit res)))))

(-main)
