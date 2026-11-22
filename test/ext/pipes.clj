(require '[clojure.string :refer [join upper-case]])
(defn twice [x] (* 2 x))
(defn max-of [a b c] (max a b c))
(let [xs [1 2 3 4 5]
      evens (->> xs (filter even?) (map twice) vec)]
  (println "" evens)
  (println "" (->> xs (map inc) (reduce +)))
  (println "" (-> "lemmis" upper-case (str "!")))
  (println "" (join ", " ["a" "b" "c"]))
  (let [m {:name "Ada" :year 1815}] (println "" (str (get m :name)) (get m :year)))
  (let [n (count xs)] (println "" n (inc n) "T" "F"))
  (println "" (twice 21) (apply max-of [3 9 4])))
