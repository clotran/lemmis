;; clotran test/typer_cases.clj CASES.edn : each case of clotran's Fortran-types oracle
;; (clotran/test/ftypes/cases.edn), written as a Lemmis expression and typed by lemmis.typer.
;; One line per case, in order: <kind-or-ERROR:msg> <lemmis expression>. test/typer.bb runs
;; the oracle itself on clj and compares.
(require 'lemmis.typer '[clojure.string :as str])

(defn- case-expr [c] (if (map? c) (or (:undefined c) (:processor c) (:interpreted c) (:expr c)) c))

(def kn {:int1 "1" :int2 "2" :int4 "4" :int8 "8" :real4 "4" :real8 "8" :complex4 "4" :complex8 "8"})

(defn- real-text [k t & [bare]]
  (let [neg (str/starts-with? t "-") t (if neg (subs t 1) t)
        t (if (re-find #"[.eE]" t) t (str t ".0"))
        t (if (str/starts-with? t ".") (str "0" t) t)
        s (str t "_" (kn k))]
    (if neg (if bare (str "-" s) (str "(-" s ")")) s)))

(defn lms [e]
  (cond
    (vector? e)
    (let [[k x] e]
      (cond (#{:int1 :int2 :int4 :int8} k)
            (if (neg? x)
              (if (= x ({:int1 -128 :int2 -32768 :int4 -2147483648 :int8 (- -9223372036854775807 1)} k))
                (str "(-" (- (inc x)) "_" (kn k) " - 1_" (kn k) ")")
                (str "(-" (- x) "_" (kn k) ")"))
              (str x "_" (kn k)))
            (#{:real4 :real8} k) (real-text k x)
            :else (let [pk ({:complex4 :real4 :complex8 :real8} k)] (str "(" (real-text pk (first x) true) ", " (real-text pk (second x) true) ")"))))
    (seq? e)
    (let [[op & args] e
          kw (filter keyword? args) as (remove keyword? args)]
      (cond (and (= 'store op) (= 1 (count kw)) (= 1 (count as)))
            ;; a store into an array of kind k is a conversion by assignment: the same as int/real/cmplx(v, kind=k)
            (str ({:int1 "int" :int2 "int" :int4 "int" :int8 "int" :real4 "real" :real8 "real" :complex4 "cmplx" :complex8 "cmplx"} (first kw))
                 "(" (lms (first as)) ", kind=" (kn (first kw)) ")")
            (and ('#{+ - * / **} op) (= 2 (count as))) (str "(" (lms (first as)) " " op " " (lms (second as)) ")")
            (and (= '- op) (= 1 (count as))) (str "(-" (lms (first as)) ")")
            :else (str op "(" (str/join ", " (concat (map lms as) (map #(str "kind=" (kn %)) kw))) ")")))))

(doseq [c (read-string (slurp (first *command-line-args*)))]
  (let [e (case-expr c)
        text (lms e)
        mine (try (let [t (lemmis.typer/type-expr text)] (name (:k t)))
                  (catch clotran.host.exception ex (str "ERROR:" (str/replace (ex-message ex) " " "_"))))]
    (println mine text)))
