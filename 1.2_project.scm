#lang racket

(define (tls-syntax-checker expr)
  (cond
    ;; Base cases
    ((number? expr) #t)
    ((boolean? expr) #t)
    ((symbol? expr) (not (memq expr '(lambda cond quote)))) ; Symbols can't be keywords
  
    ;; Procedure application
    ((pair? expr)
     (let ((head (car expr)))
       (cond
         ;; Lambda expressions
         ((eq? head 'lambda)
          (and (proper-list? (cdr expr))
               (let ((params (cadr expr)))
                 (and (list? params)
                      (andmap symbol? params)
                      (tls-syntax-checker (caddr expr))))))

         ;; Cond expressions
         ((eq? head 'cond)
          (and (proper-list? (cdr expr))
               (andmap (lambda (clause)
                         (and (proper-list? clause)
                              (= (length clause) 2)
                              (tls-syntax-checker (car clause))
                              (tls-syntax-checker (cadr clause))))
                       (cdr expr))))

         ;; Quote expressions
         ((eq? head 'quote)
          (and (proper-list? (cdr expr))
               (= (length (cdr expr)) 1)))

         ;; Primitive applications (one argument)
         ((memq head '(add1 sub1 zero? number? car cdr null? eq? atom?))
          (and (proper-list? (cdr expr))
               (= (length (cdr expr)) 1)
               (tls-syntax-checker (cadr expr))))

         ;; Primitive applications (two arguments)
         ((eq? head 'cons)
          (and (proper-list? (cdr expr))
               (= (length (cdr expr)) 2)
               (and (tls-syntax-checker (cadr expr))
                    (tls-syntax-checker (caddr expr)))))

         ;; General procedure application
         (else
          (and (tls-syntax-checker head)
               (andmap tls-syntax-checker (cdr expr)))))))

    ;; Everything else is invalid
    (else #f)))

;; Helper function to check for proper lists
(define (proper-list? x)
  (cond
    ((null? x) #t)
    ((pair? x) (proper-list? (cdr x)))
    (else #f)))

;; Helper to check for unbound variables
(define (check-unbound-vars expr env)
  (cond
    ((symbol? expr)
     (if (memq expr env) #t (error "Unbound variable:" expr)))

    ((pair? expr)
     (let ((head (car expr)))
       (cond
         ((eq? head 'lambda)
          (let ((new-env (append (cadr expr) env)))
            (check-unbound-vars (caddr expr) new-env)))

         (else
          (and (check-unbound-vars head env)
               (andmap (lambda (e) (check-unbound-vars e env)) (cdr expr)))))))

    (else #t)))
  

;; --- Test cases ---

(display (tls-syntax-checker '(add1 5))) (newline)
(display (tls-syntax-checker '(lambda (x) (add1 x)))) (newline)
(display (tls-syntax-checker '(lambda x (add1 x)))) (newline) ;; Should be #f
