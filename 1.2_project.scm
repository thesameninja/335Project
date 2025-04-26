;; Simple Scheme Syntax Checker based on The Little Schemer ideas

;; Check if an expression is valid
(define (tls-syntax-checker expr)
  (cond
    ((number? expr) #t)
    ((boolean? expr) #t)
    ((symbol? expr)
     (if (or (eq? expr 'lambda)
             (eq? expr 'cond)
             (eq? expr 'quote))
         #f
         #t))
    ((pair? expr)
     (let ((first (car expr)))
       (cond
         ((eq? first 'lambda)
          (check-lambda (cdr expr)))

         ((eq? first 'cond)
          (check-cond (cdr expr)))

         ((eq? first 'quote)
          (check-quote (cdr expr)))

         ((primitive-one? first)
          (check-primitive-one (cdr expr)))

         ((eq? first 'cons)
          (check-cons (cdr expr)))

         (else
          (check-application expr)))))
    (else #f)))

;; Check a lambda expression
(define (check-lambda stuff)
  (and (proper-list? stuff)
       (pair? stuff)
       (list-of-symbols? (car stuff))
       (tls-syntax-checker (cadr stuff))))

;; Check a cond expression
(define (check-cond clauses)
  (cond
    ((null? clauses) #t)
    (else
     (and (pair? (car clauses))
          (pair? (cdr (car clauses)))
          (null? (cddr (car clauses)))
          (tls-syntax-checker (car (car clauses)))
          (tls-syntax-checker (cadr (car clauses)))
          (check-cond (cdr clauses))))))

;; Check a quote expression
(define (check-quote stuff)
  (and (pair? stuff)
       (null? (cdr stuff))))

;; Check one-argument primitives
(define (check-primitive-one args)
  (and (pair? args)
       (null? (cdr args))
       (tls-syntax-checker (car args))))

;; Check cons
(define (check-cons args)
  (and (pair? args)
       (pair? (cdr args))
       (null? (cddr args))
       (tls-syntax-checker (car args))
       (tls-syntax-checker (cadr args))))

;; General application
(define (check-application expr)
  (and (tls-syntax-checker (car expr))
       (check-args (cdr expr))))

;; Check all arguments in a list
(define (check-args lst)
  (cond
    ((null? lst) #t)
    (else (and (tls-syntax-checker (car lst))
               (check-args (cdr lst))))))

;; Check if a list only has symbols
(define (list-of-symbols? lst)
  (cond
    ((null? lst) #t)
    (else (and (symbol? (car lst))
               (list-of-symbols? (cdr lst))))))

;; Check if a list is proper
(define (proper-list? x)
  (cond
    ((null? x) #t)
    ((pair? x) (proper-list? (cdr x)))
    (else #f)))

;; Recognize one-argument primitives
(define (primitive-one? name)
  (or (eq? name 'add1)
      (eq? name 'sub1)
      (eq? name 'zero?)
      (eq? name 'number?)
      (eq? name 'car)
      (eq? name 'cdr)
      (eq? name 'null?)
      (eq? name 'eq?)
      (eq? name 'atom?)))

;; ---------- Testing area -----------

(display (tls-syntax-checker '(add1 5))) (newline) ; #t
(display (tls-syntax-checker '(lambda (x) (add1 x)))) (newline) ; #t
(display (tls-syntax-checker '(lambda x (add1 x)))) (newline) ; #f
(display (tls-syntax-checker '(cons 1 2))) (newline) ; #t
(display (tls-syntax-checker '(cond ((zero? n) 1) (else 0)))) (newline) ; #t
(display (tls-syntax-checker '(quote (1 2 3)))) (newline) ; #t
(display (tls-syntax-checker '(quote))) (newline) ; #f
