;; fmatch.clj: a model line against a compiler's, loaded by check-fsem.bb and fuzz.bb
;; a real the model prints exactly, ~Rk:n/d (or -0 +Inf -Inf NaN), against
;; a compiler's list-directed text read as a value of kind k: the layout
;; is processor dependent (13.10.4), the value is not. ~PD, a value the
;; standard leaves to the processor, matches anything and is recorded.
(defn real-of [k c]                  ; a compiler's token as a double, or nil
  (let [c (str/replace c #"[dD]" "E")]
    (cond (#{"Infinity" "+Infinity" "Inf" "+Inf"} c) Double/POSITIVE_INFINITY
          (#{"-Infinity" "-Inf"} c) Double/NEGATIVE_INFINITY
          (#{"NaN" "+NaN" "-NaN"} c) Double/NaN
          :else (try (if (= k 4) (double (Float/parseFloat c)) (Double/parseDouble c)) (catch Exception _ nil)))))
(defn neg-zero? [x] (and (zero? x) (neg? (Math/copySign 1.0 x))))
(defn real-match? [m c]
  (let [[_ k v] (re-matches #"~R(\d+):(.*)" m) k (parse-long k) x (real-of k c)]
    (boolean
     (and x (case v "NaN" (Double/isNaN x) "+Inf" (= x Double/POSITIVE_INFINITY) "-Inf" (= x Double/NEGATIVE_INFINITY)
                "-0" (neg-zero? x)
                (let [[n d] (str/split v #"/") q (.divide (BigDecimal. (str n)) (BigDecimal. (str (or d "1"))))]
                  (and (not (Double/isNaN x)) (not (Double/isInfinite x)) (not (neg-zero? x))
                       (zero? (.compareTo (BigDecimal. (double x)) q)))))))))
;; a complex, (re,im) (13.10.4p8): its parts as reals
(defn parts-of [t] (rest (re-matches #"\((.*),(.*)\)" t)))
(defn tok-match? [m c]
  (cond (str/starts-with? m "~R") (real-match? m c) (= m "~PD") true
        (str/starts-with? m "(~R") (let [[a b] (parts-of m) [x y] (parts-of c)] (boolean (and x (real-match? a x) (real-match? b y))))
        :else (= m c)))
(defn toks-of-line [l] (vec (remove str/blank? (str/split (str/trim l) #"\s+"))))
(defn line-match? [m c]              ; m a model line: a formatted record (a string) or tokens
  (if (string? m) (= m (str/trimr c)) (let [ts (toks-of-line c)] (and (= (count m) (count ts)) (every? true? (map tok-match? m ts))))))
(defn lines-match? [ms cs] (and (= (count ms) (count cs)) (every? true? (map line-match? ms cs))))
