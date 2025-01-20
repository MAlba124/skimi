(define fib
    (lambda (n)
        (if (< n 3)
            1
            (+ (fib (- n 1)) (fib (- n 2))))))

(display (fib 10))
(newline)

(define fib-fast
  (lambda (n)
    (define a 0)
    (define b 1)
    (do ((i 0 (+ i 1)))
        ((>= i n) a)
      (define tmp a)
      (set! a (+ a b))
      (set! b tmp))))

(display (fib-fast 45))
(newline)
