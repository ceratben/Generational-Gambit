(declare
 (standard-bindings)
 (extended-bindings)
 (not safe))

(define x01 '(1 2 3 4))
(define x02 '((1 2) 3 4))
(define x03 '(((1 2)) 3 4))
(define x04 '(1 (2) 3 4))
(define x05 '((1 2 3) 4))
(define x06 '((((1 2 3))) 4))
(define x07 '(1 ((2 3)) 4))
(define x08 '((1 ((2))) 3 4))
(define x09 '(1 2 (3) 4))
(define x10 '(((1 2)) 3 4))
(define x11 '(1 (2 (3 4))))
(define x12 '((1 (2 3) 4)))
(define x13 '(1 2 ((3)) 4))
(define x14 '(1 (2 3 4)))
(define x15 '((1 2 3 4)))
(define x16 '(1 2 3 4 5))

(println (##car x01))
(println (##cdr x01))
(println (##caar x02))
(println (##cadr x01))
(println (##cdar x02))
(println (##cddr x01))
(println (##caaar x03))
(println (##caadr x04))
(println (##cadar x02))
(println (##caddr x01))
(println (##cdaar x03))
(println (##cdadr x04))
(println (##cddar x05))
(println (##cdddr x01))
(println (##caaaar x06))
(println (##caaadr x07))
(println (##caadar x08))
(println (##caaddr x09))
(println (##cadaar x10))
(println (##cadadr x11))
(println (##caddar x05))
(println (##cadddr x01))
(println (##cdaaar x06))
(println (##cdaadr x07))
(println (##cdadar x12))
(println (##cdaddr x13))
(println (##cddaar x03))
(println (##cddadr x14))
(println (##cdddar x15))
(println (##cddddr x16))
