(defn o [f g] (fn [x] (f (g x))))
(def caar (o car car))
(def cadr (o car cdr))
(def caddr (o cadr cdr))
(def cadar (o car (o cdr car)))
(def caddar (o car (o cdr (o cdr car))))

(def cons pair)

(def newline (itoc 10))
(def space (itoc 32))

(defn println [s]
  (let [ok (print s)]
    (print newline)))

(defmacro when [cond body]
  `(if ,cond ,body))

(defmacro unless [cond body]
  `(if ,cond nil ,body))

(defn getline []
  (let [ic (getchar)
        c (itoc ic)]
    (if (or (= c newline) (= ic -1))
      empty-symbol
      (cat c (getline)))))

(defn null? [xs]
  (= xs '()))

(defn length [ls]
  (if (null? ls)
    0
    (+ 1 (length (cdr ls)))))

(defn take [n ls]
  (if (or (< n 1) (null? ls))
    '()
    (cons (car ls) (take (- n 1) (cdr ls)))))

(defn drop [n ls]
  (if (or (< n 1) (null? ls))
    ls
    (drop (- n 1) (cdr ls))))

(defn merge [xs ys]
  (if (null? xs)
    ys
    (if (null? ys)
      xs
      (if (< (car xs) (car ys))
        (cons (car xs) (merge (cdr xs) ys))
        (cons (car ys) (merge xs (cdr ys)))))))

(defn mergesort [ls]
  (if (null? ls)
    ls
    (if (null? (cdr ls))
      ls
      (let [size (length ls)
            half (/ size 2)
            first (take half ls)
            second (drop half ls)]
        (merge (mergesort first) (mergesort second))))))
