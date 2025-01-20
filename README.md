# Skimi

Interpreter for a scheme like language.

## Examples

Some small examples running in the REPL

```console
skimi > (display "Hello, World!") (newline)
Hello, World!
skimi > (= 1 1)
#t
skimi > (= 1 2)
#f
skimi > (> 10 9 8 7 6)
#t
skimi > (define my-variable 20)
skimi > (+ my-variable 10)
30
skimi > (if (< my-variable 100) (display my-variable "is less than 100")) (newline)
20 is less than 100
```

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
    (cond
     ((= (% i 15) 0) (display "FizzBuzz"))
     ((= (% i 3) 0) (display "Fizz"))
     ((= (% i 5) 0) (display "Buzz"))
     (#t (display i)))
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
- [https://www.r6rs.org/final/html/r6rs-lib/r6rs-lib-Z-H-6.html#node_chap_5](https://www.r6rs.org/final/html/r6rs-lib/r6rs-lib-Z-H-6.html#node_chap_5)
