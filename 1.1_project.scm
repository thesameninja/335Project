;;CSC 335 Final Project
;;;;;;;;;;;;;;;;;;;;;;;

;;1.1 Implementing TLS interpreter in r5rs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Team Members;; Sohail Ahmad, Umaima Nasim, Jia Xiang Zhang;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;TLS is from chapter 10 of "The Little Schemer".

;;; basic predicates and operations;;;

;;; (atom? x) -> boolean?
;;; to check if x is an atom; this is same as r5rs, we do the tls :atom? later on using this
(define atom?
  (lambda (x)
    (and (not (pair? x)) (not (null? x))))
  )

;;; (add1 n) -> number?
;;; precond: n must be a number.
;;; retrun n + 1.
(define add1
  (lambda (n)
    (+ n 1))
  )

;;; (sub1 n) -> number?
;;; precond: n must be a number
;;; returns n -1
(define sub1
  (lambda (n)
    (- n 1))
  )

;;; (eqan? a1 a2) -> boolean?
;;; Precondition: a1 and a2 must be atoms (by R5RS definition).
;;; Checks if two atoms are equal. Numbers are compared using '=',
;;; all other atoms (symbols, booleans) are compared using 'eq?'.
(define eqan?
  (lambda (a1 a2)
    (cond
      ((and (number? a1) (number? a2))
       (= a1 a2))
      ((or (number? a1) (number? a2)) ; Must be same type if not numbers
       #f)
      (else ; Symbols, booleans, etc.
       (eq? a1 a2)))))


;;; (eqlist? l1 l2) -> boolean?
;;; Precondition: l1 and l2 must be lists (proper lists).
;;; Checks if two lists are equal by comparing elements recursively
;;; using the general 'equal?' predicate.
(define eqlist?
  (lambda (l1 l2)
    (cond
      ((and (null? l1) (null? l2)) #t)
      ((or (null? l1) (null? l2)) #f)
      ;; Recursively check elements and rest of lists
      (else
       (and (equal? (car l1) (car l2)) ; Use general equal? for elements
            (eqlist? (cdr l1) (cdr l2)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; adding names to cars and cdrs to access list elements
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (first l) -> any/c
;; Returns the first element of the list l (equivalent to car).
(define first car)

;;; (second l) -> any/c
;;; Returns the second element of the list l (equivalent to cadr).
(define second cadr)

;;; (third l) -> any/c
;;; Returns the third element of the list l (equivalent to caddr).
(define third caddr)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Environment/Table Representation and Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An 'entry' is a pair: (list-of-names list-of-values)
;;; A 'table' (environment) is a list of entries.

;;; (build s1 s2) -> list?
;;; Creates a list containing s1 and s2, used for structuring entries and closures
;;; Equivalent to (list s1 s2).
(define build
  (lambda (s1 s2)
    (cons s1 (cons s2 '()))))

;;; (new-entry names values) -> entry?
;;; Creates a new environment entry from a list of names (symbols) and a
;;; corresponding list of values.
;;; Example: (new-entry '(x y) '(1 2)) -> '((x y) (1 2))
(define new-entry build)

;;; (lookup-in-entry-help name names values entry-f) -> any/c
;;; Helper function for lookup-in-entry. Recursively searches the names list.
;;; - name: The symbol to look for.
;;; - names: The list of names in the current entry being searched.
;;; - values: The list of corresponding values.
;;; - entry-f: A zero-argument failure continuation (procedure) called if
;;;            'name' is not found in this entry.
;;; Returns the corresponding value if found, otherwise calls entry-f.
(define lookup-in-entry-help
  (lambda (name names values entry-f)
    (cond
      ((null? names) (entry-f)) ; Name not found in this entry
      ((eq? (car names) name)
       (car values)) ; Name found, return corresponding value
      (else ; Check rest of the names/values
       (lookup-in-entry-help name
                             (cdr names)
                             (cdr values)
                             entry-f)))))

;;; (lookup-in-entry name entry entry-f) -> any/c
;;; Looks up 'name' (a symbol) within a single environment 'entry'.
;;; - name: The symbol to look for.
;;; - entry: The environment entry '(names values)' to search.
;;; - entry-f: A zero-argument failure continuation (procedure) called if
;;;            'name' is not found in this entry.
;;; Returns the corresponding value if found, otherwise calls entry-f.
(define lookup-in-entry
  (lambda (name entry entry-f)
    (lookup-in-entry-help name
                          (first entry)  ; list of names
                          (second entry) ; list of values
                          entry-f)))

;;; (extend-table entry table) -> table?
;;; Adds a new 'entry' to the front of the environment 'table'.
;;; Returns the new, extended table.
(define extend-table cons)

;;; (lookup-in-table name table table-f) -> any/c
;;; Looks up 'name' (a symbol) in the environment 'table' (a list of entries).
;;; Searches entries one by one from front to back.
;;; - name: The symbol to look for.
;;; - table: The environment (list of entries) to search.
;;; - table-f: A zero-argument failure continuation (procedure) called if
;;;            'name' is not found in the entire table.
;;; Returns the value associated with the first occurrence of 'name', or calls
;;; table-f if not found.
(define lookup-in-table
  (lambda (name table table-f)
    (cond
      ((null? table) (table-f)) ; Reached end of table, name not found
      (else ; Look in the first entry
       (lookup-in-entry name
                      (car table) ; The current entry
                      ;; Failure continuation for lookup-in-entry:
                      ;; If not found in this entry, search the rest of the table.
                      (lambda ()
                        (lookup-in-table name (cdr table) table-f)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreter Core: Evaluation Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; (value exp) -> any/c
;;; The main entry point for the interpreter. Evaluates the TLS Scheme
;;; expression 'exp' in an initially empty environment.
;;; Returns the result of the evaluation.
(define value
  (lambda (exp)
    (meaning exp '()))) ; Start with an empty table '()

;;; (meaning exp table) -> any/c
;;; The heart of the interpreter. Determines the meaning (value) of 'exp'
;;; within the current environment 'table'.
;;; It dispatches to the appropriate action function based on the type of 'exp'.
(define meaning
  (lambda (exp table)
    ((expression-to-action exp) exp table)))

;;; (expression-to-action exp) -> procedure?
;;; Determines the type of the expression 'exp' and returns the
;;; corresponding action procedure (e.g., *const, *identifier, *lambda).
(define expression-to-action
  (lambda (exp)
    (cond
      ((atom? exp) (atom-to-action exp))
      ((pair? exp) (list-to-action exp))
      ;; Note: null? case could be added, but atoms/pairs cover it
      (else
       ;; Should not happen with valid S-expressions
       (lambda (e table) (error "Invalid expression type:" e))))))


;;; (atom-to-action atm) -> procedure?
;;; Precondition: atm is an atom (by R5RS definition).
;;; Determines the action for an atomic expression.
;;; - If it's a self-evaluating constant (number, #t, #f) or a primitive
;;;   procedure name, returns the *const action.
;;; - Otherwise, assumes it's a variable identifier and returns the *identifier action.
(define atom-to-action
  (lambda (atm)
    (cond
      ;; Self-evaluating constants
      ((number? atm) *const)
      ((eq? atm #t) *const)
      ((eq? atm #f) *const)
      ;; Built-in primitive names (treated like constants at this stage)
      ((eq? atm 'cons) *const)
      ((eq? atm 'car) *const)
      ((eq? atm 'cdr) *const)
      ((eq? atm 'null?) *const)
      ((eq? atm 'eq?) *const) ; Note: TLS eq? is R5RS eq?
      ((eq? atm 'atom?) *const) ; Note: TLS atom? is defined as :atom? below
      ((eq? atm 'zero?) *const)
      ((eq? atm 'add1) *const)
      ((eq? atm 'sub1) *const)
      ((eq? atm 'number?) *const)
      ;; Otherwise, it's a variable name
      (else *identifier))))

;;; (list-to-action lst) -> procedure?
;;; Precondition: lst is a pair (non-empty list).
;;; Determines the action for a list expression based on its first element (car).
;;; - Checks for special forms ('quote', 'lambda', 'cond').
;;; - If none match, assumes it's a procedure application and returns *application.
(define list-to-action
  (lambda (lst)
    (cond
      ;; Check if car is an atom first to avoid errors on ((lambda ...) ...)
      ((atom? (car lst))
       (cond
         ((eq? (car lst) 'quote) *quote)
         ((eq? (car lst) 'lambda) *lambda)
         ((eq? (car lst) 'cond) *cond)
         ;; Default: procedure application
         (else *application)))
      ;; If car is not an atom (e.g., ((lambda (x) ...) y)), it's an application
      (else *application))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreter actions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Action procedures take the expression 'e' and current 'table' and return
;;; the evaluated result.

;;; (*const e table) -> any/c
;;; Action for constants and primitive procedure names.
;;; - Returns numbers and booleans directly.
;;; - Wraps primitive names in a 'primitive' tag for later identification by 'apply'.
(define *const
  (lambda (e table)
    (cond
      ((or (number? e) (boolean? e)) e) ; Return self-evaluating constants
      ;; Otherwise, it's a primitive name
      (else (build 'primitive e))))) ; Tag primitive names

;;; (*quote e table) -> any/c
;;; Action for (quote exp). Returns the expression 'exp' unevaluated.
(define *quote
  (lambda (e table)
    (second e))) ; The quoted expression is the second element

;;; (initial-table name) -> error
;;; This procedure is the ultimate failure continuation for 'lookup-in-table'.
;;; It's called when a variable 'name' is not found in any environment table.
;;; Signals an "unbound variable" error.
;;; Note: The original code `(car '())` is not portable R5RS and might cause
;;; an error or return an undefined value. Using `error` is clearer.
(define initial-table
  (lambda (name)
    ;; In standard R5RS, `error` is often available.
    ;; If not, returning a specific marker or handling it differently is needed.
    (error "TLS: Unbound variable:" name)
    ;; Alternative purely functional approach (without error side-effect):
    ;; (list 'unbound-variable name)
    ))

;;; (*identifier e table) -> any/c
;;; Action for variable identifiers. Looks up the identifier 'e' in the 'table'.
;;; Uses 'initial-table' as the failure continuation if not found.
(define *identifier
  (lambda (e table)
    (lookup-in-table e table (lambda () (initial-table e)))))

;;; Helper: Extracts formals from a lambda expression '(lambda (formals...) body)'
(define formals-of-lambda second)
;;; Helper: Extracts body from a lambda expression '(lambda (formals...) body)'
(define body-of-lambda third)

;;; (*lambda e table) -> procedure?
;;; Action for (lambda (formals...) body). Creates a closure.
;;; A closure is represented as: '(non-primitive (current-table formals body))'
;;; It captures the current environment 'table' along with the parameters and body.
(define *lambda
  (lambda (e table)
    (build 'non-primitive
           (list table ; The captured environment (lexical scope)
                 (formals-of-lambda e) ; The list of formal parameters
                 (body-of-lambda e))))) ; The procedure body expression

;;; (cond-lines-of e) -> list?
;;; Extracts the list of clauses from a 'cond' expression 'e'.
;;; e.g., for '(cond (q1 a1) (q2 a2))', returns '((q1 a1) (q2 a2))'.
(define cond-lines-of cdr)

;;; (question-of clause) -> any/c
;;; Extracts the question (predicate) part of a 'cond' clause.
;;; e.g., for '(q1 a1)', returns 'q1'.
(define question-of first)

;;; (answer-of clause) -> any/c
;;; Extracts the answer (consequent) part of a 'cond' clause.
;;; e.g., for '(q1 a1)', returns 'a1'.
(define answer-of second)

;;; (else? exp) -> boolean?
;;; Checks if the expression 'exp' is the symbol 'else', specifically for 'cond'.
(define else?
  (lambda (x)
    (and (atom? x) (eq? x 'else))))

;;; (evcon lines table) -> any/c
;;; Evaluates the clauses ('lines') of a 'cond' expression within the 'table'.
;;; Recursively processes clauses:
;;; - If the question is 'else', evaluates the corresponding answer.
;;; - If evaluating the question yields #t, evaluates the corresponding answer.
;;; - Otherwise, proceeds to the next clause.
;;; Assumes at least one clause exists and the last one is often (else ...).
(define evcon
  (lambda (lines table)
    (let ((current-clause (car lines)))
      (cond
        ((else? (question-of current-clause))
         (meaning (answer-of current-clause) table))
        ((meaning (question-of current-clause) table) ; If question evaluates to true
         (meaning (answer-of current-clause) table))
        (else ; Question evaluated to false, try next clause
         (evcon (cdr lines) table))))))

;;; (*cond e table) -> any/c
;;; Action for (cond clauses...). Extracts the clauses and evaluates them using 'evcon'.
(define *cond
  (lambda (e table)
    (evcon (cond-lines-of e) table)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreter Core: Application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; (function-of e) -> any/c
;;; Extracts the function/operator part of an application expression 'e'.
;;; e.g., for '(f x y)', returns 'f'.
(define function-of car)

;;; (arguments-of e) -> list?
;;; Extracts the list of argument expressions from an application 'e'.
;;; e.g., for '(f x y)', returns '(x y)'.
(define arguments-of cdr)

;;; (evlis args table) -> list?
;;; Evaluates a list of argument expressions 'args' within the environment 'table'.
;;; Returns a list of the evaluated argument values.
(define evlis
  (lambda (args table)
    (cond
      ((null? args) '())
      (else
       (cons (meaning (car args) table) ; Evaluate the first argument
             (evlis (cdr args) table)))))) ; Evaluate the rest

;;; (*application e table) -> any/c
;;; Action for procedure application (func arg1 arg2 ...).
;;; 1. Evaluates the function part 'func' to get a procedure value (primitive or closure).
;;; 2. Evaluates the argument expressions 'arg1 arg2 ...' using 'evlis'.
;;; 3. Applies the procedure value to the evaluated argument values using 'apply'.
(define *application
  (lambda (e table)
    (tls-apply (meaning (function-of e) table) ; Evaluate function part
           (evlis (arguments-of e) table)))) ; Evaluate arguments

;;; (primitive? proc-val) -> boolean?
;;; Checks if the evaluated procedure value 'proc-val' represents a primitive operation.
;;; Primitive values are tagged like '(primitive cons)'.
(define primitive?
  (lambda (l)
    (and (pair? l) (eq? (first l) 'primitive)))) ; Check tag

;;; (non-primitive? proc-val) -> boolean?
;;; Checks if the evaluated procedure value 'proc-val' represents a closure (user-defined lambda).
;;; Closures are tagged like '(non-primitive (table formals body))'.
(define non-primitive?
  (lambda (l)
    (and (pair? l) (eq? (first l) 'non-primitive)))) ; Check tag

;;; (:atom? x) -> boolean?
;;; The interpreter's internal version of atom?. It considers values that are
;;; R5RS atoms (#t, #f, symbols, numbers) AND the interpreter's internal
;;; representations of procedures (tagged lists like '(primitive cons)' or
;;; '(non-primitive ...)') to be "atoms" from the perspective of the
;;; *language being interpreted*. The empty list '() is *not* an atom in TLS.
(define :atom?
  (lambda (x)
    (cond
      ((atom? x) #t) ; Standard R5RS atoms are TLS atoms
      ((null? x) #f) ; () is not a TLS atom
      ((primitive? x) #t) ; Primitive procedure values are TLS atoms
      ((non-primitive? x) #t) ; Closures are TLS atoms
      (else #f)))) ; Regular lists/pairs are not TLS atoms

;;; (apply-primitive name vals) -> any/c
;;; Applies the primitive operation identified by 'name' to the list of
;;; evaluated argument values 'vals'.
;;; Assumes the correct number of arguments are provided.
(define apply-primitive ; Corrected spelling
  (lambda (name vals)
    (cond
      ((eq? name 'cons) (cons (first vals) (second vals)))
      ((eq? name 'car) (car (first vals)))
      ((eq? name 'cdr) (cdr (first vals)))
      ((eq? name 'null?) (null? (first vals)))
      ((eq? name 'eq?) (eqan? (first vals) (second vals))) ; TLS eq? compares numbers using =.
      ((eq? name 'atom?) (:atom? (first vals))) ; Use the interpreter's :atom?
      ((eq? name 'zero?) (zero? (first vals)))
      ((eq? name 'add1) (add1 (first vals)))
      ((eq? name 'sub1) (sub1 (first vals)))
      ((eq? name 'number?) (number? (first vals)))
      (else
       ;; Should not happen if atom-to-action is correct
       (error "TLS: Unknown primitive:" name)))))

;;; Closure structure: '(table formals body)' as created by *lambda
;;; Accessors for the parts of a closure's data '(table formals body)'

;;; (table-of closure-data) -> table?
;;; Extracts the captured environment (table) from the closure data structure.
(define table-of first)

;;; (formals-of closure-data) -> list?
;;; Extracts the list of formal parameters from the closure data structure.
(define formals-of second)

;;; (body-of closure-data) -> list?
;;; Extracts the body expression from the closure data structure.
(define body-of third)

;;; (apply-closure closure-val vals) -> any/c
;;; Applies a user-defined closure 'closure-val' to the list of evaluated
;;; argument values 'vals'.
;;; 1. Extracts the closure's data: captured table, formals, and body.
;;; 2. Creates a new environment entry binding the 'formals' to the 'vals'.
;;; 3. Extends the closure's captured 'table' with this new entry.
;;; 4. Evaluates the closure's 'body' in this newly extended environment.
(define apply-closure
  (lambda (closure-val vals) ; closure-val is '(non-primitive (table formals body))'
    (let ((closure-data (second closure-val))) ; Get the '(table formals body)' part
      (meaning (body-of closure-data)
               (extend-table
                 (new-entry (formals-of closure-data) vals) ; Bind formals to values
                 (table-of closure-data)))))) ; Extend the closure's captured table

;;; (apply fun vals) -> any/c
;;; The main application dispatcher.
;;; Takes an evaluated procedure 'fun' (which is either a primitive marker
;;; or a closure) and a list of evaluated argument values 'vals'.
;;; Calls either 'apply-primitive' or 'apply-closure' based on the type of 'fun'.
(define tls-apply
  (lambda (fun vals)
    (cond
      ((primitive? fun)
       (apply-primitive (second fun) vals)) ; Extract primitive name
      ((non-primitive? fun)
       (apply-closure fun vals)) ; Pass the whole closure structure
      (else
       ;; This usually indicates an error, like trying to apply a non-procedure
       (error "TLS: Not a procedure:" fun)))))


;;;;;;;;;;;;;;;;;;;
;; some tests 
;;;;;;;;;;;;;;;;


;; Example 1: Constants
(display "Evaluating 10: ")
(display (value 10)) (newline) ; Expected: 10

(display "Evaluating #t: ")
(display (value #t)) (newline) ; Expected: #t

;; Example 2: Quoting
(display "Evaluating (quote (a b c)): ")
(display (value '(quote (a b c)))) (newline) ; Expected: (a b c)

(display "Evaluating '(a b c): ") ; Using R5RS reader sugar for quote
(display (value ''(a b c))) (newline) ; Expected: (a b c) ; Note the double quote!

;; Example 3: Primitives
(display "Evaluating (add1 5): ")
(display (value '(add1 5))) (newline) ; Expected: 6

(display "Evaluating (cons 'a '(b c)): ")
(display (value '(cons 'a '(b c)))) (newline) ; Expected: (a b c)

(display "Evaluating (car '(a b c)): ")
(display (value '(car '(a b c)))) (newline) ; Expected: a

(display "Evaluating (cdr '(a b c)): ")
(display (value '(cdr '(a b c)))) (newline) ; Expected: (b c)

(display "Evaluating (null? '()): ")
(display (value '(null? '()))) (newline) ; Expected: #t

(display "Evaluating (null? '(a)): ")
(display (value '(null? '(a)))) (newline) ; Expected: #f

(display "Evaluating (eq? 'a 'a): ")
(display (value '(eq? 'a 'a))) (newline) ; Expected: #t

(display "Evaluating (eq? 'a 'b): ")
(display (value '(eq? 'a 'b))) (newline) ; Expected: #f

(display "Evaluating (atom? 'atom): ")
(display (value '(atom? 'atom))) (newline) ; Expected: #t

(display "Evaluating (atom? '(a b)): ")
(display (value '(atom? '(a b)))) (newline) ; Expected: #f

(display "Evaluating (atom? (lambda (x) x)): ")
;; lambda evaluates to a non-primitive closure structure, which :atom? treats as true
(display (value '(atom? (lambda (x) x)))) (newline) ; Expected: #t

(display "Evaluating (zero? 0): ")
(display (value '(zero? 0))) (newline) ; Expected: #t

(display "Evaluating (zero? 1): ")
(display (value '(zero? 1))) (newline) ; Expected: #f

;; Example 4: Cond
(display "Evaluating (cond (#f 1) ('t 2)): ") ; Note: Using 't instead of #t for symbol eq?
(display (value '(cond (#f 1) (#t 2)))) (newline) ; Expected: 2

(display "Evaluating (cond ((zero? 1) 'zero) (else 'not-zero)): ")
(display (value '(cond ((zero? 1) 'zero) (else 'not-zero)))) (newline) ; Expected: not-zero

;; Example 5: Lambda and Application
(display "Evaluating ((lambda (x) (add1 x)) 10): ")
(display (value '((lambda (x) (add1 x)) 10))) (newline) ; Expected: 11

(display "Evaluating ((lambda (x y) (cons x (cdr y))) 'a '(z b c)): ")
(display (value '((lambda (x y) (cons x (cdr y))) 'a '(z b c)))) (newline) ; Expected: (a b c)

;; Example 6: Closures (Lexical Scope)
(display "Evaluating (((lambda (x) (lambda (y) (cons x y))) 'a) 'b): ")
;; x='a is captured in the inner lambda's environment
(display (value '(((lambda (x) (lambda (y) (cons x y))) 'a) 'b))) (newline) ; Expected: (a . b) <- Correction: cons creates a pair.

;; Example 7: Simple Recursion using the Y-combinator-like pattern from the book
;; Define a length function for TLS lists
;; len-maker takes a function 'mk' and returns the actual length function.
;; The actual length function 'len' takes a list 'lat'.
;; It works by passing the recursive function itself as an argument.
(define tls-length-expr
  '((lambda (len) (len '(a b c d))) ; Call the length function
    ;; The actual recursive length function:
    (lambda (lat) ; Takes the list
      ((lambda (length-rec) ; Define the recursive helper 'length-rec'
         (length-rec length-rec lat)) ; Call helper with itself and the list
       ;; The body of the recursive helper:
       (lambda (rec list)
         (cond
           ((null? list) 0)
           (else (add1 (rec rec (cdr list)))))))))) ; Recursive call

(display "Evaluating recursive length of '(a b c d): ")
(display (value tls-length-expr)) (newline) ; Expected: 4

;; Example 8: Another recursive example (Factorial-like, using add/sub1)
;; Calculates 5 + 4 + 3 + 2 + 1 + 0
(define tls-sum-down-expr
 '((lambda (sum) (sum 5)) ; Call the sum function
   (lambda (n)
     ((lambda (sum-rec)
        (sum-rec sum-rec n))
      (lambda (rec num)
        (cond
          ((zero? num) 0)
          ;; This interpreter lacks '+', so we use add1 recursively
          ;; It won't compute factorial, but demonstrates recursion structure.
          ;; Let's redefine to calculate sum = n + (n-1) + ... + 0
          ;; Need '+' primitive for real sum, or re-implement using add1/sub1
          ;; Let's just return N for now to show recursion works
          #| ; requires '+' primitive:
             (else (+ num (rec rec (sub1 num))))
          |#
           (else ; demo: counts down and adds 1 for each step > 0
             (add1 (rec rec (sub1 num))) ) ; calculates n
          ))))))

;; Let's redefine the factorial example to just count down using add1
(define tls-countdown-factorial-style
 '((lambda (fact) (fact 5)) ; Call the function
   (lambda (n) ; argument n
     ((lambda (fact-rec) (fact-rec fact-rec n)) ; Call recursive helper w/ self
      ;; Recursive helper definition:
      (lambda (rec k)
        (cond
         ((zero? k) 0) ; Base case
         (else (add1 (rec rec (sub1 k)))) ; Recursive step (counts how many times add1 is called)
         ))))))

(display "Evaluating recursive countdown of 5 (returns 5): ")
(display (value tls-countdown-factorial-style)) (newline) ; Expected: 5

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

