(define create-list
  (lambda (n)
    (if (= n 0)
        '()
        (cons n (create-list (- n 1))))))

(display (create-list 10))
(newline)
