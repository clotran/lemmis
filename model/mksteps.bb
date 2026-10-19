;; mksteps.bb FILE FN STEPS EXTRA... (from model/: bb mksteps.bb fparse.lisp fp fp-steps): from FILE's (defun FN (nt toks) ...), the call-counting
;; STEPS: the same recursion, each answer 1 + the counts of the calls made, every call let-bound
;; under the tests that govern it (so the termination proof sees them). EXTRA names other
;; counted parsers: a call of one is counted with its own -steps function.
(require '[clojure.string :as str] '[edamame.core :as e] '[clojure.pprint :as pp])
(let [[file fname steps & extra] *command-line-args*
      fsym (symbol fname) ssym (symbol steps)
      counted (into {fsym ssym} (for [x extra] [(symbol x) (symbol (str x "-steps"))]))
      src (slurp file)
      i (str/index-of src (str "(defun " fname " (nt toks)"))
      form (e/parse-string (subs src i))
      n (atom 0)
      call? (fn [x] (and (seq? x) (counted (first x))))
      cnt-of (fn [x] (cons (counted (first x)) (rest x)))
      leaf? (fn [x] (and (seq? x) (or (= x '(fail)) (= 'mv (first x)))))]
  (letfn [(tr [x acc]
            (cond (leaf? x) (cons '+ (cons 1 acc))
                  (call? x) (let [c (symbol (str "c" (swap! n inc)))]
                              (list 'let (list (list c (cnt-of x))) (cons '+ (cons 1 (cons c acc)))))
                  (and (seq? x) (= 'mv-let (first x)))
                  (let [[_ vars bound & body] x
                        c (symbol (str "c" (swap! n inc)))
                        ;; a branch counts its call, or the call an mv-let in it binds
                        br (fn br [y] (cond (call? y) (cnt-of y)
                                            (and (seq? y) (= 'mv-let (first y))) (br (nth y 2))
                                            :else 0))
                        cexp (cond (call? bound) (cnt-of bound)
                                   (and (seq? bound) (= 'if (first bound)))
                                   (let [[_ tst a b] bound] (list 'if tst (br a) (br b)))
                                   :else (throw (ex-info "mv-let bound" {:b bound})))]
                    (list 'mv-let vars bound (list 'declare (cons 'ignorable vars))
                          (list 'let (list (list c cexp)) (tr (last body) (cons c acc)))))
                  (and (seq? x) (= 'cond (first x))) (cons 'cond (map (fn [cl] (list (first cl) (tr (second cl) acc))) (rest x)))
                  (and (seq? x) (= 'if (first x))) (list 'if (second x) (tr (nth x 2) acc) (tr (nth x 3) acc))
                  (and (seq? x) (= 'case (first x))) (concat ['case (second x)] (map (fn [cl] (list (first cl) (tr (second cl) acc))) (drop 2 x)))
                  (and (seq? x) (#{'let 'let*} (first x))) (list (first x) (second x) (tr (nth x 2) acc))
                  :else (throw (ex-info "unknown" {:x x}))))]
    (let [[_ _ args decl body] form
          xargs (second decl)
          measure (second (drop-while #(not= :measure %) xargs))]
      (binding [pp/*print-right-margin* 110]
        (pp/pprint (list 'defun ssym args
                           (list 'declare (list 'xargs :guard 't :measure measure :verify-guards nil))
                           (tr body ())))))))
