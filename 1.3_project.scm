;; Project 1.3 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Specification for the Environment Subsystem

;; An environment is a sequence of bindings: ((name . value) ...)
;; Operations:
;; - (empty-env): returns an empty environment
;; - (extend-env var val env): extends env with a new var-value binding
;; - (apply-env env var): returns the value bound to var in env

;; NOTE:
;; - The base constructs (cons, car, cdr, null?, list?) are provided by R5RS Scheme.
;; - This environment subsystem is built on top of that using custom logic.
;; - Our functions implement a structure that simulates lexical environments for TLS.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type predicate for environments (for compatibility with closure definition)
;; (Not provided by R5RS which is custom to TLS implementation)
(define environment?
  (lambda (x)
    (list? x)))

;; Core Environment Implementation (custom, not from R5RS)
(define empty-env
  (lambda ()
    '()))

(define extend-env
  (lambda (var val env)
    (cons (cons var val) env)))

(define apply-env
  (lambda (env var)
    (cond
      ((null? env) (error "Unbound variable" var))
      ((eq? (caar env) var) (cdar env))
      (else (apply-env (cdr env) var)))))


;; Tests (Custom test cases to validate the specification)
(define test-env1 (empty-env))
(define test-env2 (extend-env 'x 10 test-env1))
(define test-env3 (extend-env 'y 20 test-env2))
(apply-env test-env3 'x) ;; => 10
(apply-env test-env3 'y) ;; => 20

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Compatibility with 1.2 closures:
;; Closure is defined as (closure id body env), and env must satisfy environment?
;; Our env format is a list of (symbol . value) pairs, so it satisfies the predicate

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof of Correctness:
;; - empty-env yields an empty list
;; - extend-env constructs a new binding on top
;; - apply-env recursively finds the latest binding
;; - The interface is consistent and can be safely used in the TLS interpreter