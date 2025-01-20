# Skimi

Interpreter for a scheme like language.

## Examples

Fibonacci sequence

```scheme
(define fib
    (lambda (n)
        (if (< n 3)
            1
            (+ (fib (- n 1)) (fib (- n 2))))))
(fib 20)
```

FizzBuzz

```scheme
(define fizz-buzz
    (lambda (i n)
        (if (= (% i 15) 0)
            (display "FizzBuzz")
            (if (= (% i 3) 0)
                (display "Fizz")
                (if (= (% i 5) 0)
                    (display "Buzz")
                    (display i))))
    (newline)
    (if (< i n) (fizz-buzz (+ i 1) n))))
(fizz-buzz 1 100)
```

Do loop

```scheme
(do ((x 0 (+ x 1)))
    ((>= x 10) (display "Loop finished") (newline))
    (display x)
    (newline))
```

This will output:

```console
0
1
2
3
4
5
6
7
8
9
Loop finished
```

#### References

- [https://github.com/rust-bakery/nom/blob/main/examples/s_expression.rs](https://github.com/rust-bakery/nom/blob/main/examples/s_expression.rs)
