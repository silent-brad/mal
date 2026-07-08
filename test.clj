(ns test)


(defn print-all
  [xs]
  (if (null? xs)
    nil
    (do
      (print (car xs))
      (print-all (cdr xs)))))


(print-all (cons 1 (cons 2 (cons 3 nil))))

(map inc [1 2 3])
(filter (fn [x] (< x 3)) [1 2 3 4])
(reduce + 0 [1 2 3 4])


(defn sum
  [[h & t]]
  (if h
    (+ h (sum t))
    0))


(println (sum [1 2 3 4]))
