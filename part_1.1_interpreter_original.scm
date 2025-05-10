;; part_1.1_interpreter_original.scm
;; Implements the TLS interpreter based on Chapter 10 of "The Little Schemer".
;; This version uses the original environment representation (names-values pairs)
;; and includes the 'let' special form, desugared into lambda application.

(load "shared_definitions.scm") ; Load shared primitive and keyword definitions

;;;-----------------------------------------------------------------------------
;;; Basic Predicates and Operations
;;;-----------------------------------------------------------------------------

;; (atom? x) -> boolean?
;; R5RS definition of atom: not a pair and not the empty list.
;; Used internally by the interpreter. TLS's 'atom?' primitive is distinct (:atom?).
(define atom?
  (lambda (x)
    (and (not (pair? x)) (not (null? x)))))

;; (add1 n) -> number?
;; Precondition: n is a number. Returns n + 1.
(define add1 (lambda (n) (+ n 1)))

;; (sub1 n) -> number?
;; Precondition: n is a number. Returns n - 1.
(define sub1 (lambda (n) (- n 1)))

;; (eq-val? v1 v2) -> boolean?
;; General equality predicate for TLS values, used by the TLS 'eq?' primitive.
;; - Numbers are compared with R5RS 'equal?' (handles numeric types).
;; - Other R5RS atoms (symbols, booleans) are compared with R5RS 'eq?'.
;; - Lists/pairs (e.g., internal representations) are compared with R5RS 'equal?'.
(define eq-val?
  (lambda (v1 v2)
    (cond
      ((and (number? v1) (number? v2)) (equal? v1 v2))
      ((or (number? v1) (number? v2)) #f)
      ((or (atom? v1) (atom? v2)) (eq? v1 v2)) ; R5RS atom? for non-numeric atoms
      (else (equal? v1 v2)))))

;;;-----------------------------------------------------------------------------
;;; List Accessors (Convenience)
;;;-----------------------------------------------------------------------------
(define first car)
(define second cadr)
(define third caddr)

;;;-----------------------------------------------------------------------------
;;; Environment/Table Representation and Operations (Original: Names-Values Pairs)
;;;   - An 'entry' (scope/frame) is `(list list-of-names list-of-values)`.
;;;   - A 'table' (environment) is a list of 'entries'.
;;; How tables shrink: When a procedure call (which extends the table) returns,
;;; the extended environment specific to that call becomes inaccessible. The R5RS
;;; garbage collector reclaims the memory for these temporary environment structures.
;;; The TLS interpreter logic itself doesn't explicitly "shrink" tables; scope
;;; is managed by passing and returning environments through function calls.
;;;-----------------------------------------------------------------------------

;; (build s1 s2) -> list?
;; Utility to create a two-element list. Used for entries and tagged values.
(define build (lambda (s1 s2) (cons s1 (cons s2 '()))))

;; (new-entry names values) -> entry?
;; Creates an environment entry from parallel lists of names and values.
(define new-entry build)

;; (lookup-in-entry-help name names values entry-f) -> any/c or (entry-f)
;; Helper for `lookup-in-entry`: searches for 'name' in 'names' list.
(define lookup-in-entry-help
  (lambda (name names values entry-f)
    (cond
      ((null? names) (entry-f))
      ((eq? (car names) name) (car values))
      (else (lookup-in-entry-help name (cdr names) (cdr values) entry-f)))))

;; (lookup-in-entry name entry entry-f) -> any/c or (entry-f)
;; Looks up 'name' in a single 'entry'. Calls 'entry-f' on failure.
(define lookup-in-entry
  (lambda (name entry entry-f)
    (lookup-in-entry-help name (first entry) (second entry) entry-f)))

;; (extend-table entry table) -> table?
;; Adds 'entry' to the front of 'table', creating a new, extended environment.
(define extend-table cons)

;; (lookup-in-table name table table-f) -> any/c or (table-f)
;; Looks up 'name' in 'table' (list of entries), from innermost to outermost.
;; Calls 'table-f' if 'name' is not found in any entry.
(define lookup-in-table
  (lambda (name table table-f)
    (cond
      ((null? table) (table-f))
      (else
       (lookup-in-entry name (car table)
                        (lambda () (lookup-in-table name (cdr table) table-f)))))))

;;;-----------------------------------------------------------------------------
;;; Interpreter Core: Evaluation Functions
;;;-----------------------------------------------------------------------------

;; (value exp) -> any/c
;; Main entry point: evaluates 'exp' in an initial empty environment.
(define value (lambda (exp) (meaning exp '())))

;; (meaning exp table) -> any/c
;; Evaluates 'exp' within the environment 'table'. Dispatches to an action procedure.
(define meaning (lambda (exp table) ((expression-to-action exp) exp table)))

;; (expression-to-action exp) -> procedure?
;; Returns the appropriate action procedure for 'exp' based on its type.
(define expression-to-action
  (lambda (exp)
    (cond
      ((atom? exp) (atom-to-action exp))
      ((pair? exp) (list-to-action exp))
      (else (lambda (e table) (error "TLS Error: Invalid S-expression type:" e))))))

;; (atom-to-action atm) -> procedure?
;; Determines action for an R5RS atom 'atm'.
(define atom-to-action
  (lambda (atm)
    (cond
      ((number? atm) *const)
      ((boolean? atm) *const)
      ((is-tls-primitive-symbol? atm) *const) ; Primitive names like 'cons
      (else *identifier))))                  ; Assumed variable

;; (list-to-action lst) -> procedure?
;; Determines action for a list 'lst', checking for special forms or application.
;; Includes 'let' as a special form.
(define list-to-action
  (lambda (lst)
    (cond
      ((atom? (car lst)) ; Operator is usually a symbol
       (cond
         ((eq? (car lst) 'quote) *quote)
         ((eq? (car lst) 'lambda) *lambda)
         ((eq? (car lst) 'cond) *cond)
         ((eq? (car lst) 'let) *let)     ; Handle 'let' special form
         (else *application)))
      (else *application)))) ; Operator is a compound expression, e.g., ((lambda...) ...)

;;;-----------------------------------------------------------------------------
;;; Interpreter Actions
;;;-----------------------------------------------------------------------------

;; (*const e table) -> any/c
;; Action for constants. Self-evaluating values are returned directly.
;; Primitive names are tagged, e.g., (primitive cons).
(define *const
  (lambda (e table)
    (cond
      ((or (number? e) (boolean? e)) e)
      (else (build 'primitive e)))))

;; (*quote e table) -> any/c
;; Action for (quote exp). Returns 'exp' unevaluated.
(define *quote (lambda (e table) (second e)))

;; (initial-table name) -> error
;; Failure continuation for global unbound variable lookup.
(define initial-table (lambda (name) (error "TLS Error: Unbound variable:" name)))

;; (*identifier e table) -> any/c
;; Action for identifiers: looks up 'e' in 'table'.
(define *identifier (lambda (e table) (lookup-in-table e table (lambda () (initial-table e)))))

;; (formals-of-lambda e) -> list, (body-of-lambda e) -> exp
;; Helpers for lambda expressions.
(define formals-of-lambda second)
(define body-of-lambda third)

;; (*lambda e table) -> closure-representation
;; Action for (lambda (formals...) body). Creates a closure capturing 'table'.
(define *lambda
  (lambda (e table)
    (build 'non-primitive
           (list table (formals-of-lambda e) (body-of-lambda e)))))

;; (*cond ...) and its helpers
(define cond-lines-of cdr)
(define question-of first)
(define answer-of second)
(define else? (lambda (x) (and (atom? x) (eq? x 'else))))
(define evcon
  (lambda (lines table)
    (let ((current-clause (car lines)))
      (cond
        ((else? (question-of current-clause)) (meaning (answer-of current-clause) table))
        ((meaning (question-of current-clause) table) (meaning (answer-of current-clause) table))
        (else (evcon (cdr lines) table))))))
(define *cond (lambda (e table) (evcon (cond-lines-of e) table)))

;;;-----------------------------------------------------------------------------
;;; Action for 'let' (desugaring to lambda)
;;;-----------------------------------------------------------------------------

;; (let-bindings exp) -> list of binding pairs, e.g., '((x 1) (y 2))
(define let-bindings second)

;; (let-body exps) -> list of body expressions, e.g., '((cons x y) (add1 x))
(define let-body cddr) ; (cdr (cdr exp))

;; (map-car-of-bindings bindings) -> list of vars
;; Extracts variables from let bindings: ((v1 e1) (v2 e2)) -> (v1 v2)
(define (map-car-of-bindings bindings)
  (if (null? bindings) '() (cons (caar bindings) (map-car-of-bindings (cdr bindings)))))

;; (map-cadr-of-bindings bindings) -> list of expressions
;; Extracts initial value expressions from let bindings: ((v1 e1) (v2 e2)) -> (e1 e2)
(define (map-cadr-of-bindings bindings)
  (if (null? bindings) '() (cons (cadar bindings) (map-cadr-of-bindings (cdr bindings)))))

;; (last-element lst) -> element
;; Helper to get the last element of a non-empty list.
(define (last-element lst)
  (if (null? (cdr lst)) (car lst) (last-element (cdr lst))))

;; (*let e table) -> any/c
;; Action for (let ((var1 exp1) ...) body1 body2 ...).
;; Desugars 'let' into an application of a 'lambda' expression:
;;   `((lambda (var1 ...) effective-body) exp1 ...)`
;; and then calls 'meaning' on this desugared form.
;; The 'effective-body' is the last expression in the 'let' body, as TLS lambda
;; (from Ch10) takes a single body expression.
(define *let
  (lambda (e table)
    (let* ((bindings (let-bindings e))
           (body-exps (let-body e))
           (vars (map-car-of-bindings bindings))
           (initial-val-exps (map-cadr-of-bindings bindings))
           ;; Determine the single body expression for the desugared lambda.
           ;; If 'let' body is empty, result is undefined (or an error could be signaled).
           ;; If multiple body expressions, TLS lambda semantics mean only last is evaluated for value.
           (lambda-body (if (null? body-exps)
                            '(quote tls-undefined-let-body-value) ; Placeholder for empty let body
                            (last-element body-exps)))) ; Use the last body expression
      (let ((desugared-exp (cons (list 'lambda vars lambda-body) ; Construct ((lambda (vars) body) exprs)
                                 initial-val-exps)))
        (meaning desugared-exp table))))) ; Evaluate the desugared expression

;;;-----------------------------------------------------------------------------
;;; Interpreter Core: Application
;;;-----------------------------------------------------------------------------
(define function-of car)
(define arguments-of cdr)

;; (evlis args table) -> list of values
;; Evaluates a list of argument expressions 'args' in 'table'.
(define evlis
  (lambda (args table)
    (cond
      ((null? args) '())
      (else (cons (meaning (car args) table) (evlis (cdr args) table))))))

;; (*application e table) -> any/c
;; Action for procedure application.
(define *application
  (lambda (e table)
    (tls-apply (meaning (function-of e) table) (evlis (arguments-of e) table))))

;; (primitive? proc-val) -> boolean?, (non-primitive? proc-val) -> boolean?
;; Predicates for tagged procedure values.
(define primitive? (lambda (l) (and (pair? l) (eq? (first l) 'primitive))))
(define non-primitive? (lambda (l) (and (pair? l) (eq? (first l) 'non-primitive))))

;; (:atom? x) -> boolean?
;; TLS's 'atom?' primitive considers interpreter's procedure representations as atoms.
(define :atom?
  (lambda (x)
    (cond
      ((atom? x) #t) ((null? x) #f) ((primitive? x) #t) ((non-primitive? x) #t)
      (else #f))))

;; (apply-primitive-handler name vals) -> any/c
;; Applies TLS primitive 'name' to evaluated arguments 'vals'.
(define apply-primitive-handler
  (lambda (name vals)
    (cond
      ((eq? name 'cons) (cons (first vals) (second vals)))
      ((eq? name 'car) (car (first vals)))
      ((eq? name 'cdr) (cdr (first vals)))
      ((eq? name 'null?) (null? (first vals)))
      ((eq? name 'eq?) (eq-val? (first vals) (second vals)))
      ((eq? name 'atom?) (:atom? (first vals)))
      ((eq? name 'zero?) (zero? (first vals)))
      ((eq? name 'add1) (add1 (first vals)))
      ((eq? name 'sub1) (sub1 (first vals)))
      ((eq? name 'number?) (number? (first vals)))
      (else (error "TLS Error: Unknown primitive in apply-primitive-handler:" name)))))

;; Closure data accessors: (table formals body)
(define table-of-closure-data first)
(define formals-of-closure-data second)
(define body-of-closure-data third)

;; (apply-closure closure-val vals) -> any/c
;; Applies a user-defined 'closure-val' to arguments 'vals'.
;; Extends closure's captured environment with new bindings for formals.
(define apply-closure
  (lambda (closure-val vals)
    (let ((closure-data (second closure-val)))
      (meaning (body-of-closure-data closure-data)
               (extend-table
                 (new-entry (formals-of-closure-data closure-data) vals)
                 (table-of-closure-data closure-data))))))

;; (tls-apply fun vals) -> any/c
;; Main application dispatcher: applies 'fun' (primitive or closure) to 'vals'.
(define tls-apply
  (lambda (fun vals)
    (cond
      ((primitive? fun) (apply-primitive-handler (second fun) vals))
      ((non-primitive? fun) (apply-closure fun vals))
      (else (error "TLS Error: Attempt to apply non-procedure value:" fun)))))