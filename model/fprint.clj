;; fprint.clj: fsyn s-expressions printed as Fortran, as clotran's generator
;; (scripts/acl2-fortran) writes them -- the text check-fsem.bb compiles
;; and check-gen.bb compares the generated files against, line for line.
;; Loaded by both: (load-file "fprint.clj").
(require (quote [clojure.string :as str]))

(defn fx [e]
  (let [[op a b c] e]
    (case (if (= e (quote (:sub (:neg (:huge)) (:int 1)))) :min op)
      ;; -2^63, which has no literal, as the generator writes it
      :min "(-huge(0_int64) - 1_int64)"
      ;; a negative literal in parentheses: no sign may follow an operator (R1007)
      :int (if (neg? a) (str "(" a "_int64)") (str a "_int64")) :true ".true." :false ".false." :huge "huge(0_int64)"
      :var a :comp (str a "%" b) :elem (str a "%" b "(" (fx c) ")")
      :add (str "(" (fx a) " + " (fx b) ")") :sub (str "(" (fx a) " - " (fx b) ")")
      :mul (str "(" (fx a) " * " (fx b) ")") :neg (str "(-" (fx a) ")")
      :eq (str "(" (fx a) " == " (fx b) ")") :lt (str "(" (fx a) " < " (fx b) ")")
      :le (str "(" (fx a) " <= " (fx b) ")") :ge (str "(" (fx a) " >= " (fx b) ")")
      :not (str "(.not. " (fx a) ")") :max (str "max(" (fx a) ", " (fx b) ")")
      :size (str "size(" a "%" b ", kind=int64)")
      :fcall (str a "(" (str/join ", " (map fx b)) ")"))))

(declare fstmts)
(defn fstmt [s]
  (let [[op a b c] s ind #(map (fn [l] (str "  " l)) %)]
    (case op
      :assign [(str (fx a) " = " (fx b))]
      :if (concat [(str "if (" (fx a) ") then")] (ind (fstmts b)) ["else"] (ind (fstmts c)) ["end if"])
      :select (concat [(str "select case (" (fx a) ")")]
                      (mapcat (fn [[k ss]] (cons (str "case (" k "_int64)") (ind (fstmts ss)))) b)
                      ["case default"] (ind (fstmts c)) ["end select"])
      :do (concat ["do"] (ind (fstmts a)) ["end do"])
      (:cycle :exit :return) [(name op)]
      :call [(str "call " a "(" (str/join ", " (map fx b)) ")")])))
(defn fstmts [ss] (mapcat fstmt ss))

(defn ftype [t] (case t :int64 "integer(int64)" :logical "logical"))

(defn fproc [pr]
  (let [fun (= :function (first pr))
        [_ nm pure rec dummies rtype locals body] (if fun pr (let [[k nm rec ds ls b] pr] [k nm nil rec ds nil ls b]))
        head (str (when (= 't rec) "recursive ") (when (= 't pure) "pure ")
                  (if fun "function " "subroutine ") nm "(" (str/join ", " (map first dummies)) ")" (when fun " result(r)"))
        decl (fn [[x k t]] (case k :value (str "integer(int64), value :: " x)
                             (:in :inout) (str "type(" t "), intent(" (name k) ") :: " x)
                             :out (str "integer(int64), intent(out) :: " x)))]
    (concat [head] (map #(str "  " %) (concat (map decl dummies) (when fun [(str (ftype rtype) " :: r")])
                                               (for [[x t] locals] (str (ftype t) " :: " x)) (fstmts body)))
            [(str "end " (if fun "function " "subroutine ") nm)])))

