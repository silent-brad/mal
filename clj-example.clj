;; clj-example.clj -- A real program demonstrating the Clojure-style interpreter
(ns example)


;; Utils
(defn adder
  [n]
  (fn [x] (+ x n)))


(defn compose
  [f g]
  (fn [x] (f (g x))))


;; Core data processing
(defn count-where
  [pred xs]
  (let [s (seq xs)]
    (if (null? s)
      0
      (+ (if (pred (car s)) 1 0)
         (count-where pred (cdr s))))))


(defn index-of
  [x xs]
  (let [s (seq xs)]
    (if (null? s)
      -1
      (if (= x (car s))
        0
        (let [r (index-of x (cdr s))]
          (if (= r -1) -1 (inc r)))))))


(defn range
  [n]
  (if (< n 1)
    '()
    (append (range (- n 1)) (list (- n 1)))))


(defn append
  [xs ys]
  (let [s (seq xs)]
    (if (null? s)
      ys
      (cons (car s) (append (cdr s) ys)))))


;; Map/Filter/Reduce helpers
(defn map-inc
  [xs]
  (map inc xs))


(defn filter-even
  [xs]
  (filter (fn [x] (= (/ x 2) (/ x 2))) xs))


(defn sum-list
  [xs]
  (reduce + 0 xs))


;; Destructuring examples
(defn point-sum
  [{:keys [x y]}]
  (+ x y))


(defn unpack
  [[a b c]]
  (+ a (+ b c)))


;; Using in a real workflow
(defn process-data
  [items]
  (-> items
      (filter (fn [x] (> x 0)))
      (map inc)
      (reduce + 0)))


;; Main entry
(defn main
  []
  (println "=== Example Program ===")
  (println (str "Sum of [1 2 3]: " (sum-list [1 2 3])))
  (println (str "Point sum: " (point-sum {:x 10 :y 20})))
  (println (str "Unpack: " (unpack [1 2 3])))
  (println "Done"))


(main)
