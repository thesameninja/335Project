;; shared_definitions.scm
;; Contains definitions shared between the TLS interpreter and syntax checker,
;; such as primitive procedure names, their arities, and language keywords.
;; This ensures consistency across different parts of the project.

;; tls-primitives-with-arity:
;; An association list defining TLS primitive procedures and their expected arities.
;; Structure: '((primitive-name . arity) ...)
;; Used by the syntax checker for arity validation and by the interpreter
;; to identify primitive operations.
(define tls-primitives-with-arity
  '((cons . 2) (car . 1) (cdr . 1) (null? . 1) (eq? . 2)
    (atom? . 1) (zero? . 1) (add1 . 1) (sub1 . 1) (number? . 1)))

;; (get-primitive-arity prim-name) -> number? | #f
;; Input: 'prim-name', a symbol.
;; Output: The arity (number of arguments) if 'prim-name' is a known TLS primitive,
;;         otherwise returns #f.
(define get-primitive-arity
  (lambda (prim-name)
    (let ((entry (assoc prim-name tls-primitives-with-arity)))
      (if entry
          (cdr entry)
          #f))))

;; (is-tls-primitive-symbol? sym) -> boolean?
;; Input: 'sym', any R5RS value.
;; Output: #t if 'sym' is a symbol representing a TLS primitive, #f otherwise.
(define is-tls-primitive-symbol?
  (lambda (sym)
    (and (symbol? sym)
         (assoc sym tls-primitives-with-arity)))) ; 'assoc' returns a pair (truthy) if found, #f otherwise.

;; tls-keywords:
;; A list of symbols that are TLS keywords. These symbols have special syntactic
;; meaning and are not treated as regular variable identifiers.
;; Includes 'let' for the TLS-LET extension.
(define tls-keywords '(quote lambda cond else let))

;; (is-tls-keyword-symbol? sym) -> boolean?
;; Input: 'sym', any R5RS value.
;; Output: #t if 'sym' is a symbol representing a TLS keyword, #f otherwise.
(define is-tls-keyword-symbol?
  (lambda (sym)
    (and (symbol? sym)
         (member sym tls-keywords))))