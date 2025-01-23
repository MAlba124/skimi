(do ((x 0 (+ x 1)))
    ((>= x 10) (display "Loop finished") (newline))
    (display x)
    (newline))
