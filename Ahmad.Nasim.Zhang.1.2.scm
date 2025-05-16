;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Project: CSc 335 Project Spring 2025 
;;
;; Team: Sohail Ahmad, Umaima Nasim, Jia Xiang Zhang
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; part_1.2_syntax_checker.scm
;; Implements a purely functional R5RS syntax checker for TLS (TLS-LET).
;; This checker verifies syntax without evaluating expressions, detecting issues like
;; malformed special forms, incorrect arity for primitives, and unbound variables.

(load "shared_definitions.scm") ; Load shared primitive and keyword definitions




;;;;;
;; Inductive Definition of TLS-LET Expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This definition specifies what makes a syntactically valid expression
;; in the TLS-LET language. The definition is inductive, expressions are
;; built up from simpler components.
;;
;; I. Initial Definitions:
;;
;;    A. Constants:
;;       1. <Number>: Any R5RS integer (e.g., 0, 42, -7).
;;       2. <Boolean>: The R5RS boolean values #t or #f.
;;       A <Constant> is either a <Number> or a <Boolean>.
;;
;;    B. Symbols:
;;       1. <PrimitiveSymbol>: A symbol predefined as a TLS primitive operation
;;          (e.g., 'cons, 'add1, 'car). See `shared_definitions.scm`.
;;       2. <KeywordSymbol>: A symbol predefined with special syntactic meaning
;;          (e.g., 'quote, 'lambda, 'cond, 'let, 'else). See `shared_definitions.scm`.
;;       3. <VariableSymbol>: Any R5RS symbol that is not a <PrimitiveSymbol>
;;          or a <KeywordSymbol>.
;;
;;    C. Environment (`env`): For checking some rules, we assume an `env` which is
;;       a list of <VariableSymbol> currently considered to be defined.
;;
;; II. Definition of a TLS-LET Expression (`<tls-exp>`):
;;
;; An S-expression `E` is a `<tls-exp>` if it satisfies one of the following rules:
;;
;;    Rule 1: Base Cases (Atomic Expressions)
;;       a. `E` is a <Constant>.
;;          Example: `100`, `#f`
;;       b. `E` is a <PrimitiveSymbol>.
;;          Example: `'car` (when used as a value itself, not as an operator)
;;       c. `E` is a <VariableSymbol> AND `E` is present in the current `env`.
;;          Example: `'x` (if `x` is in `env`)
;;
;;    Rule 2: Quoted Expression
;;       `E` is of the form `('quote S)`, where `S` is any R5RS S-expression.
;;       The syntax checker does not further validate `S` against `<tls-exp>` rules.
;;       Example: `(quote (a b (+ 1 2)))`
;;
;;    Rule 3: Lambda Expression (Procedure Definition)
;;       `E` is of the form `('lambda P B)`, where:
;;       a. `P` (parameters) is a proper list of zero or more distinct <VariableSymbol>s.
;;          No symbol in `P` may be a <KeywordSymbol> or <PrimitiveSymbol>.
;;       b. `B` (body) is a `<tls-exp>`, checked in an `env` extended with the symbols in `P`.
;;       Example: `(lambda (x y) (cons x y))`
;;
;;    Rule 4: Conditional Expression
;;       `E` is of the form `('cond C1 C2 ... Ck)`, where `k >= 1`, and:
;;       a. Each `Ci` (for `i < k`, or all `i` if no `else` clause) is a clause of
;;          the form `(T_i A_i)`, where `T_i` (test) and `A_i` (answer) are each a `<tls-exp>`
;;          (checked in the current `env`).
;;       b. Optionally, the last clause `Ck` can be an `else-clause` of the form
;;          `('else A_k)`, where `A_k` is a `<tls-exp>` (checked in current `env`).
;;          Only one `else-clause` is permitted, and it must be last.
;;       Example: `(cond ((null? z) 0) (else (add1 z)))`
;;
;;    Rule 5: Let Expression (Local Bindings)
;;       `E` is of the form `('let BL B1 B2 ... Bk)`, where `k >= 1`, and:
;;       a. `BL` (binding list) is a proper list of zero or more binding pairs.
;;          Each binding pair is of the form `(V_i E_i)`, where:
;;          i.  `V_i` is a <VariableSymbol>. All `V_i` in `BL` must be distinct.
;;              No `V_i` may be a <KeywordSymbol> or <PrimitiveSymbol>.
;;          ii. `E_i` (initial value expression) is a `<tls-exp>` (checked in current `env`).
;;       b. Each `B_j` (body expression) is a `<tls-exp>`, checked in an `env`
;;          extended with all `V_i` from `BL`.
;;       Example: `(let ((a 10) (b (add1 a-outer))) (cons a b))`
;;
;;    Rule 6: Application (Procedure Call)
;;       `E` is of the form `(O A1 A2 ... Am)`, where `m >= 0`, and:
;;       a. `O` (operator) is a `<tls-exp>` (checked in current `env`).
;;          Syntactically, `O` cannot be a <Constant> or the empty list `'()`.
;;       b. Each `A_j` (argument) is a `<tls-exp>` (checked in current `env`).
;;       c. Arity Check: If `O` is a <PrimitiveSymbol>, then `m` (the number of
;;          arguments) must match the defined arity for that <PrimitiveSymbol>.
;;       Example: `(add1 count)`, `(my-func (car list1) 'val2)`
;;
;; III. Closure Clause:
;;    Only S-expressions formed by a finite number of applications of the above
;;    rules (starting from Base Cases) are considered valid `<tls-exp>`s.
;;    The empty list `'()` by itself is not a valid `<tls-exp>`. Most forms
;;    (lambda, cond, let, application) also require proper list structure for
;;    themselves and their main components.




;;;-----------------------------------------------------------------------------
;;; Helper Predicates for Syntax Checking
;;;-----------------------------------------------------------------------------

;; (is-proper-list? obj) -> boolean?
;; Checks if 'obj' is a proper list (ends with '()').
(define (is-proper-list? obj)
  (cond ((null? obj) #t)
        ((pair? obj) (is-proper-list? (cdr obj)))
        (else #f)))

;; (all-symbols? lst) -> boolean?
;; Checks if every element in the proper list 'lst' is a symbol.
(define (all-symbols? lst)
  (or (null? lst) (and (symbol? (car lst)) (all-symbols? (cdr lst)))))

;; (has-duplicates? lst) -> boolean?
;; Checks if 'lst' contains any duplicate symbols.
(define (has-duplicates? lst)
  (cond ((null? lst) #f)
        ((member (car lst) (cdr lst))) ; 'member' uses eq? for symbols
        (else (has-duplicates? (cdr lst)))))

;; (any-forbidden-symbols-in-formals? lst) -> boolean?
;; Checks if any symbol in 'lst' (formals or let-bound vars) is a TLS keyword or primitive.
(define (any-forbidden-symbols-in-formals? lst)
  (cond ((null? lst) #f)
        ((let ((item (car lst)))
           (or (is-tls-keyword-symbol? item) (is-tls-primitive-symbol? item))) #t)
        (else (any-forbidden-symbols-in-formals? (cdr lst)))))

;;;-----------------------------------------------------------------------------
;;; Main Syntax Checking Dispatcher
;;;-----------------------------------------------------------------------------

;; (check-tls-syntax exp) -> #t or string (error message)
;; Public entry point. Checks 'exp' in an initially empty environment.
(define (check-tls-syntax exp) (check-tls-syntax-aux exp '()))

;; (check-tls-syntax-aux exp env) -> #t or string
;; Core syntax checker: checks 'exp' in 'env' (list of bound variable symbols).
(define (check-tls-syntax-aux exp env)
  (cond
    ((number? exp) (if (integer? exp) #t "Syntax Error: Number literal must be an R5RS integer."))
    ((boolean? exp) #t)
    ((symbol? exp)
     (cond
       ((is-tls-primitive-symbol? exp) #t)
       ((is-tls-keyword-symbol? exp) (string-append "Syntax Error: Keyword '" (symbol->string exp) "' used as variable."))
       ((member exp env) #t)
       (else (string-append "Syntax Error: Unbound variable: '" (symbol->string exp) "'."))))
    ((pair? exp)
     (if (not (is-proper-list? exp))
         "Syntax Error: Expression is not a proper list."
         (let ((op (car exp)))
           (cond
             ((symbol? op)
              (cond ((eq? op 'quote) (check-quote exp env))
                    ((eq? op 'lambda) (check-lambda exp env))
                    ((eq? op 'cond) (check-cond exp env))
                    ((eq? op 'let) (check-let exp env))
                    (else (check-application exp env))))
             ((pair? op) (check-application exp env)) ; Operator is compound, e.g. ((lambda...) ...)
             (else (string-append "Syntax Error: Invalid operator form (not symbol or pair): "
                                  (if (null? op) "()" (if (number? op) "number" (if (boolean? op) "boolean" "unknown")))))))))
    ((null? exp) "Syntax Error: The empty list '() is not a valid TLS expression.")
    (else "Syntax Error: Malformed expression or non-S-expression component.")))

;;;-----------------------------------------------------------------------------
;;; Specific Form Checkers
;;;-----------------------------------------------------------------------------

;; (check-quote exp env) -> #t or string
;; Checks (quote <datum>). Datum can be any S-expression.
(define (check-quote exp env)
  (if (and (list? exp) (= (length exp) 2)) #t "Syntax Error: Malformed 'quote'. Expected (quote <datum>)."))

;; (check-lambda exp env) -> #t or string
;; Checks (lambda (formals...) body).
(define (check-lambda exp env)
  (if (not (and (list? exp) (= (length exp) 3)))
      "Syntax Error: Malformed 'lambda'. Expected (lambda (formals...) body)."
      (let ((formals (second exp)) (body (third exp)))
        (if (not (is-proper-list? formals))
            "Syntax Error: Lambda formals must be a proper list."
        (cond
          ((not (all-symbols? formals)) "Syntax Error: Lambda formals must all be symbols.")
          ((has-duplicates? formals) "Syntax Error: Lambda formals must not contain duplicates.")
          ((any-forbidden-symbols-in-formals? formals) "Syntax Error: Lambda formals cannot be keywords or primitives.")
          (else (check-tls-syntax-aux body (append formals env)))))))) ; Check body in extended env

;; (check-cond exp env) -> #t or string
;; Checks (cond <clause1> ...).
(define (check-cond exp env)
  (if (or (null? (cdr exp)) (not (is-proper-list? (cdr exp))))
      "Syntax Error: 'cond' requires at least one clause and clauses must form a proper list."
      (check-cond-clauses (cdr exp) env #f)))

;; (check-cond-clauses clauses env else-seen?) -> #t or string
;; Helper for check-cond. Checks list of cond clauses.
(define (check-cond-clauses clauses env else-seen?)
  (cond
    ((null? clauses) #t)
    (else
     (let ((current-clause (car clauses)))
       (if (not (and (is-proper-list? current-clause) (= (length current-clause) 2)))
           "Syntax Error: Malformed 'cond' clause. Expected (<test> <expression>)."
           (let ((test-exp (car current-clause)) (ans-exp (cadr current-clause)))
             (if (and (symbol? test-exp) (eq? test-exp 'else))
                 (cond
                   (else-seen? "Syntax Error: Multiple 'else' clauses in 'cond'.")
                   ((not (null? (cdr clauses))) "Syntax Error: 'else' must be the last clause in 'cond'.")
                   (else (check-tls-syntax-aux ans-exp env))) ; Check 'else' answer
                 (if else-seen? "Syntax Error: Clause found after 'else' clause."
                     (let ((test-check (check-tls-syntax-aux test-exp env)))
                       (if (not (eq? test-check #t)) test-check ; Error in test
                           (let ((ans-check (check-tls-syntax-aux ans-exp env)))
                             (if (not (eq? ans-check #t)) ans-check ; Error in answer
                                 (check-cond-clauses (cdr clauses) env #f))))))))))))) ; Check next

;; (check-let exp env) -> #t or string
;; Checks (let ((v1 e1) ...) body1 body2 ...).
(define (check-let exp env)
  (if (not (and (list? exp) (>= (length exp) 2))) ; Must be (let bindings . body)
      "Syntax Error: Malformed 'let'. Expected (let ((var exp) ...) body...)."
      (let ((bindings (second exp)) (body-exps (cddr exp)))
        (if (not (is-proper-list? bindings))
            "Syntax Error: 'let' bindings part must be a proper list."
        (if (null? body-exps) ; TLS 'let' (desugared to lambda) should have a body.
            "Syntax Error: 'let' must have at least one body expression."
            (check-let-bindings bindings body-exps env))))))

;; (check-let-bindings bindings body-exps env) -> #t or string
;; Helper: checks 'let' binding pairs and then the body.
;; Binding expressions e_i are checked in 'env' (outer scope).
;; Body expressions are checked in 'env' extended with let-bound variables.
(define (check-let-bindings bindings body-exps env)
  (let collect-vars-and-check-val-exps ((b-list bindings) (collected-vars '()) (val-exp-status #t))
    (if (null? b-list) ; Finished processing all binding pairs
        (if (not (eq? val-exp-status #t)) val-exp-status ; Propagate error from a val-exp
            ;; All val-exps are fine, now check collected-vars for validity
            (cond
              ((has-duplicates? collected-vars)
               "Syntax Error: Duplicate variable in 'let' bindings.")
              ((any-forbidden-symbols-in-formals? collected-vars) ; Reuse checker for formals
               "Syntax Error: 'let' bound variable cannot be a TLS keyword or primitive name.")
              (else ; Vars are fine, now check body expressions in extended environment
               (check-expression-list body-exps (append collected-vars env)))))
        ;; Process current binding pair
        (let ((current-binding (car b-list)))
          (if (not (and (is-proper-list? current-binding) (= (length current-binding) 2)))
              "Syntax Error: Malformed 'let' binding pair. Expected (variable expression)."
              (let ((var (car current-binding)) (val-exp (cadr current-binding)))
                (if (not (symbol? var))
                    "Syntax Error: Variable in 'let' binding must be a symbol."
                    ;; Check the value expression in the *current* (outer) environment
                    (let ((current-val-exp-check (check-tls-syntax-aux val-exp env)))
                      (if (not (eq? current-val-exp-check #t))
                          (collect-vars-and-check-val-exps '() '() current-val-exp-check) ; Error, stop and return it
                          (collect-vars-and-check-val-exps (cdr b-list) (cons var collected-vars) #t))))))))))


;; (check-expression-list exps env) -> #t or string
;; Checks a list of expressions (e.g., 'let' body). All must be valid.
;; Returns #t if all valid, or the first error message.
(define (check-expression-list exps env)
  (cond
    ((null? exps) #t) ; No expressions, or all checked. (Note: 'let' requires at least one body by prior check)
    (else
     (let ((first-exp-check (check-tls-syntax-aux (car exps) env)))
       (if (not (eq? first-exp-check #t))
           first-exp-check ; Error in this expression
           (check-expression-list (cdr exps) env)))))) ; Check remaining expressions

;; (check-application exp env) -> #t or string
;; Checks (<operator> <operand1> ...).
(define (check-application exp env)
  (let ((operator-exp (car exp)) (operand-exps (cdr exp)))
    (let ((op-validity (check-operator-syntax operator-exp env)))
      (if (not (eq? op-validity #t)) op-validity
          (let ((args-validity (check-operand-list-syntax operand-exps env)))
            (if (not (eq? args-validity #t)) args-validity
                (if (and (symbol? operator-exp) (is-tls-primitive-symbol? operator-exp))
                    (let ((expected-arity (get-primitive-arity operator-exp))
                          (actual-arity (length operand-exps)))
                      (if (and expected-arity (= actual-arity expected-arity)) #t
                          (string-append "Syntax Error: Primitive '" (symbol->string operator-exp)
                                         "' expects " (if expected-arity (number->string expected-arity) "arity")
                                         " arguments, got " (number->string actual-arity) ".")))
                    #t ))))))) ; Not a primitive or arity matches

;; (check-operator-syntax op-exp env) -> #t or string
;; Checks the operator part of an application. Cannot be literal number, boolean, or '().
(define (check-operator-syntax op-exp env)
  (cond
    ((number? op-exp) "Syntax Error: Operator cannot be a literal number.")
    ((boolean? op-exp) "Syntax Error: Operator cannot be a literal boolean.")
    ((null? op-exp) "Syntax Error: Operator cannot be the empty list '().")
    (else (check-tls-syntax-aux op-exp env)))) ; Must be a valid expression itself

;; (check-operand-list-syntax operand-exps env) -> #t or string
;; Checks a list of operand expressions.
(define (check-operand-list-syntax operand-exps env)
  (cond
    ((null? operand-exps) #t)
    (else
     (let ((first-operand-check (check-tls-syntax-aux (car operand-exps) env)))
       (if (not (eq? first-operand-check #t)) first-operand-check
           (check-operand-list-syntax (cdr operand-exps) env))))))