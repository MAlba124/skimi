(define fizz-buzz
  (lambda (i n)
    (cond
     ((= (% i 15) 0) (display "FizzBuzz"))
     ((= (% i 3) 0) (display "Fizz"))
     ((= (% i 5) 0) (display "Buzz"))
     (#t (display i)))
 (newline)
 (if (< i n) (fizz-buzz (+ i 1) n))))

(fizz-buzz 1 100)
