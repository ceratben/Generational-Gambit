(declare (extended-bindings))

(define c1 #\A)
(define c2 #\B)

(define (test2 x y)
  (println (and x y))
  (println (if (and x y) 11 22))
  (println (and (##not x) y))
  (println (if (and (##not x) y) 11 22))
  (println (and x (##not y)))
  (println (if (and x (##not y)) 11 22))
  (println (and (##not x) (##not y)))
  (println (if (and (##not x) (##not y)) 11 22))
  (println (##not (and x y)))
  (println (if (##not (and x y)) 11 22))
  (println (##not (and (##not x) y)))
  (println (if (##not (and (##not x) y)) 11 22))
  (println (##not (and x (##not y))))
  (println (if (##not (and x (##not y))) 11 22))
  (println (##not (and (##not x) (##not y))))
  (println (if (##not (and (##not x) (##not y))) 11 22)))

(define (test x)
  (test2 x c1)
  (test2 x c2))

(test c1)
(test c2)
