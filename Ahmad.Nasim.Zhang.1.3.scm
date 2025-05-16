;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Project: CSc 335 Project Spring 2025 
;;
;; Team: Sohail Ahmad, Umaima Nasim, Jia Xiang Zhang
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; part_1.3_interpreter_list_env.scm
;; Implements the TLS interpreter with the environment representation changed
;; to use lists of bindings (frames of (name value) pairs), in Part 1.3.
;; Includes the 'let' special form, desugared into lambda application.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 1.3: Environment Subsystem Specification and Proof (List-of-Bindings)
;;
;; This section outlines the specification for the TLS environment subsystem
;; and argues that the "list-of-bindings" representation implemented in this
;; file satisfies this specification and works correctly with the interpreter.
;;
;; I. Specification for the Environment Subsystem (General)
;;
;;    An environment is a mechanism for associating names (symbols) with their
;;    values. It must support:
;;    1. Representing an empty set of bindings (an initial state).
;;    2. Creating a new scope (or "frame") of bindings, where a set of names
;;       are bound to a corresponding set of values.
;;    3. Extending an existing environment with a new scope, such that bindings
;;       in the new scope can shadow (hide) bindings for the same names in
;;       outer scopes.
;;    4. Looking up the value associated with a name, respecting lexical scope
;;       (i.e., finding the binding in the innermost scope where the name is defined).
;;    5. Signaling an error or failure if a name cannot be found.
;;
;;    Data Abstraction:
;;    - <Name>: A symbol.
;;    - <Value>: Any TLS value.
;;    - <Frame>: A collection of <Name>-<Value> associations for a single scope.
;;    - <Environment>: A sequence of <Frame>s, ordered from innermost to outermost.
;;
;;    Operations:
;;    - `empty-environment`: Returns an <Environment> with no bindings.
;;    - `make-frame(names-list, values-list)`: Takes lists of <Name>s and <Value>s
;;      (of equal length) and returns a new <Frame>.
;;    - `extend-environment(frame, environment)`: Takes a <Frame> and an <Environment>,
;;      returns a new <Environment> with `frame` as the innermost scope.
;;    - `lookup(name, environment, failure-action)`: Searches `environment` for `name`.
;;      Returns the <Value> if found; otherwise, performs `failure-action`.
;;
;; II. List-of-Bindings Implementation (in this file)
;;
;;    A. Data Structures:
;;       - <Binding>: A list `(list <Name> <Value>)`. Example: `'(x 10)`
;;       - <Frame>: A list of <Binding>s. Example: `'((x 10) (y 20))`
;;       - <Table> (our <Environment>): A list of <Frame>s. Example: `'(((x 10)) ((y 30) (x 5)))`
;;         (innermost frame is first).
;;
;;    B. Mapping to Operations:
;;       - `empty-environment`: The empty list `'()`.
;;       - `make-frame(names, values)`: Implemented by `(new-entry names values)`.
;;         Code: `(define new-entry (lambda (ns vs) (if (null? ns) '() (cons (list (car ns) (car vs)) (new-entry (cdr ns) (cdr vs))))))`
;;       - `extend-environment(frame, table)`: Implemented by `(extend-table frame table)`.
;;         Code: `(define extend-table cons)`
;;       - `lookup(name, table, failure-action)`: Implemented by `(lookup-in-table name table failure-action)`.
;;         This uses `lookup-in-entry` for searching within a single frame.
;;         Code for `lookup-in-entry(name, frame, fail-f)`:
;;           `(cond ((null? frame) (fail-f)) ((eq? name (caar frame)) (cadar frame)) (else (lookup-in-entry name (cdr frame) fail-f)))`
;;         Code for `lookup-in-table(name, table, fail-f)`:
;;           `(cond ((null? table) (fail-f)) (else (lookup-in-entry name (car table) (lambda () (lookup-in-table name (cdr table) fail-f)))))`
;;
;; III. Proof that Implementation Satisfies Specification
;;
;;    1. `empty-environment`: `'()` correctly represents no bindings.
;;
;;    2. `new-entry` (implements `make-frame`):
;;       - (PRE-CONDITION): `names` and `values` are lists of equal length.
;;       - BASE STEP: If `names` is null, returns `'()`, an empty frame, which is correct.
;;       - INDUCTIVE HYPOTHESIS (on structure of `names` list): Assume
;;         `(new-entry (cdr names) (cdr values))` correctly creates a frame for the
;;         rest of the names/values.
;;       - INDUCTION STEP: `(new-entry names values)` computes
;;         `(cons (list (car names) (car values)) recursive-result)`.
;;         `(list (car names) (car values))` correctly forms the first <Binding>.
;;         `cons` prepends this <Binding> to the correctly formed frame for the rest.
;;       - (POST-CONDITION): Returns a proper list of <Binding>s, i.e., a valid <Frame>. Correct.
;;
;;    3. `extend-table` (implements `extend-environment`):
;;       - `(cons frame table)` prepends the new `frame` to the `table` (list of frames).
;;       - (POST-CONDITION): This makes `frame` the new head of the list, meaning it
;;         will be searched first by `lookup-in-table`. This correctly implements
;;         the "innermost scope" and shadowing behavior. Correct.
;;
;;    4. `lookup-in-entry` (helper for `lookup` within a <Frame>):
;;       - (PRE-CONDITION): `name` is a symbol, `frame` is a list of <Binding>s, `entry-f` is a thunk.
;;       - BASE STEP: If `frame` is null, calls `(entry-f)`. Correct (name not in this frame).
;;       - INDUCTIVE HYPOTHESIS (on structure of `frame` list): Assume
;;         `(lookup-in-entry name (cdr frame) entry-f)` works correctly.
;;       - INDUCTION STEP:
;;         - Checks `(eq? name (caar frame))` (name of current binding).
;;         - If true, returns `(cadar frame)` (value of current binding). Correct.
;;         - Else, recursively calls `(lookup-in-entry name (cdr frame) entry-f)`.
;;           By IH, this correctly searches the rest of the frame.
;;       - (POST-CONDITION): Returns value if `name` is found in `frame`, else calls `(entry-f)`. Correct.
;;
;;    5. `lookup-in-table` (implements `lookup`):
;;       - (PRE-CONDITION): `name` is a symbol, `table` is a list of <Frame>s, `table-f` is a thunk.
;;       - BASE STEP: If `table` is null, calls `(table-f)`. Correct (name not in any frame).
;;       - INDUCTIVE HYPOTHESIS (on structure of `table` list): Assume
;;         `(lookup-in-table name (cdr table) table-f)` works correctly.
;;       - INDUCTION STEP:
;;         - Calls `(lookup-in-entry name (car table) failure-thunk-for-entry)`.
;;           `(car table)` is the innermost frame. By correctness of `lookup-in-entry` (III.4),
;;           this correctly searches the innermost frame.
;;         - If found, the value is returned. Correct (innermost binding found).
;;         - If not found in `(car table)`, `failure-thunk-for-entry` is called, which is
;;           `(lambda () (lookup-in-table name (cdr table) table-f))`.
;;           By IH, this recursive call correctly searches the rest of the `table`.
;;       - (POST-CONDITION): Returns value of innermost binding of `name` across all frames,
;;         or calls `(table-f)`. This fulfills the lexical lookup requirement. Correct.
;;
;; IV. Compatibility with the Rest of the Interpreter
;;
;;    The change in environment representation primarily affects `*lambda` (when capturing
;;    the environment) and `apply-closure` (when extending the captured environment).
;;
;;    - `*lambda e table)`: Produces `(non-primitive (list table formals body))`.
;;      The `table` captured is now a list of <Frame>s. This is fine, as it's just
;;      data being stored.
;;
;;    - `apply-closure closure-val vals)`:
;;      1. Extracts `captured-table` (a list of <Frame>s), `formals`, and `body`.
;;      2. Calls `(new-entry formals vals)`. As shown in III.2, this correctly
;;         produces a new <Frame> (a list of <Binding>s for the arguments).
;;      3. Calls `(extend-table new-argument-frame captured-table)`. As shown in III.3,
;;         this correctly creates a new <Table> (environment) where the argument frame
;;         is innermost, followed by the frames of the `captured-table`.
;;      4. Calls `(meaning body new-execution-table)`. The `new-execution-table`
;;         has the correct structure for `lookup-in-table` (and its helper
;;         `lookup-in-entry` for this representation) to implement lexical scope.
;;
;;    - `*identifier e table)`: Calls `(lookup-in-table e table ...)`. Since `lookup-in-table`
;;      is proven correct for the new representation (III.5), identifiers are resolved correctly.
;;
;;    - `*let e table)`: Desugars to a lambda application. The correctness of `let`
;;      then relies on the correctness of `*lambda` and `apply-closure` with the
;;      new environment representation, which holds as argued above.
;;
;;    Conclusion: The altered representation (list of frames, where each frame is a
;;    list of bindings) correctly satisfies the abstract specification of an environment
;;    that supports lexical scoping. The interpreter's core logic for closure creation,
;;    application, and variable lookup interacts correctly with this new representation
;;    because the functions implementing the environment operations (`new-entry`,
;;    `extend-table`, `lookup-in-table`) are adapted to work with this structure
;;    while upholding their specified behavior. The interpreter remains functionally
;;    equivalent.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(load "shared_definitions.scm")

;;;-----------------------------------------------------------------------------
;;; Basic Predicates and Operations (Identical to part_1.1)
;;;-----------------------------------------------------------------------------
(define atom? (lambda (x) (and (not (pair? x)) (not (null? x)))))
(define add1 (lambda (n) (+ n 1)))
(define sub1 (lambda (n) (- n 1)))
(define eq-val?
  (lambda (v1 v2)
    (cond
      ((and (number? v1) (number? v2)) (equal? v1 v2))
      ((or (number? v1) (number? v2)) #f)
      ((or (atom? v1) (atom? v2)) (eq? v1 v2))
      (else (equal? v1 v2)))))
(define first car)
(define second cadr)
(define third caddr)
(define build (lambda (s1 s2) (cons s1 (cons s2 '()))))

;;;-----------------------------------------------------------------------------
;;; Environment/Table Representation and Operations (: List of Bindings)
;;;   - A 'binding' is `(list name value)`.
;;;   - A 'frame' (scope) is a list of 'bindings'.
;;;   - A 'table' (environment) is a list of 'frames'.
;;; How tables shrink: Similar to the original, upon each function call return, the top of the stack is released leading to table shrinking. TLS logic manages active scope via environment passing.
;;;-----------------------------------------------------------------------------

;; (new-entry names values) -> frame?
;; Creates a new environment frame (a list of `(name value)` bindings).
(define new-entry
  (lambda (names values)
    (cond
      ((null? names) '())
      (else (cons (list (car names) (car values))
                  (new-entry (cdr names) (cdr values)))))))

;; (lookup-in-entry name frame entry-f) -> any/c or (entry-f)
;; Looks up 'name' (a symbol) within a single environment 'frame'.
;; - frame: A list of bindings, e.g., '((n1 v1) (n2 v2) ...)'.
;; - entry-f: A zero-argument failure continuation.
;; Returns the value if 'name' is found in 'frame', otherwise calls 'entry-f'.
(define lookup-in-entry
  (lambda (name frame entry-f)
    (cond
      ((null? frame) (entry-f)) ; Name not found in this frame
      ((eq? name (caar frame))   ; (caar frame) is (car (car frame)), i.e., the name of the first binding
       (cadar frame))            ; (cadar frame) is (cadr (car frame)), i.e., the value of the first binding
      (else                      ; Corrected: no condition for the final else
       (lookup-in-entry name (cdr frame) entry-f))))) ; Check rest of the frame


;; (extend-table frame table) -> table?
;; Adds 'frame' to 'table', creating a new, extended environment.
(define extend-table cons)

;; (lookup-in-table name table table-f) -> any/c or (table-f)
;; Looks up 'name' in 'table' (list of frames), innermost to outermost.
(define lookup-in-table
  (lambda (name table table-f)
    (cond
      ((null? table) (table-f))
      (else
       (lookup-in-entry name (car table)
                        (lambda () (lookup-in-table name (cdr table) table-f)))))))

;;;-----------------------------------------------------------------------------
;;; Interpreter Core: Evaluation Functions (mostly identical to part_1.1)
;;;-----------------------------------------------------------------------------
(define value (lambda (exp) (meaning exp '())))
(define meaning (lambda (exp table) ((expression-to-action exp) exp table)))
(define expression-to-action
  (lambda (exp)
    (cond
      ((atom? exp) (atom-to-action exp))
      ((pair? exp) (list-to-action exp))
      (else (lambda (e table) (error "TLS (list-env) Error: Invalid S-expression type:" e))))))
(define atom-to-action
  (lambda (atm)
    (cond
      ((number? atm) *const) ((boolean? atm) *const)
      ((is-tls-primitive-symbol? atm) *const) (else *identifier))))
(define list-to-action
  (lambda (lst)
    (cond
      ((atom? (car lst))
       (cond ((eq? (car lst) 'quote) *quote) ((eq? (car lst) 'lambda) *lambda)
             ((eq? (car lst) 'cond) *cond) ((eq? (car lst) 'let) *let)
             (else *application)))
      (else *application))))

;;;-----------------------------------------------------------------------------
;;; Interpreter Actions (mostly identical to part_1.1)
;;;-----------------------------------------------------------------------------
(define *const (lambda (e table) (if (or (number? e) (boolean? e)) e (build 'primitive e))))
(define *quote (lambda (e table) (second e)))
(define initial-table (lambda (name) (error "TLS (list-env) Error: Unbound variable:" name)))
(define *identifier (lambda (e table) (lookup-in-table e table (lambda () (initial-table e)))))
(define formals-of-lambda second)
(define body-of-lambda third)
(define *lambda (lambda (e table) (build 'non-primitive (list table (formals-of-lambda e) (body-of-lambda e)))))
(define cond-lines-of cdr) (define question-of first) (define answer-of second)
(define else? (lambda (x) (and (atom? x) (eq? x 'else))))
(define evcon
  (lambda (lines table)
    (let ((current-clause (car lines)))
      (cond ((else? (question-of current-clause)) (meaning (answer-of current-clause) table))
            ((meaning (question-of current-clause) table) (meaning (answer-of current-clause) table))
            (else (evcon (cdr lines) table))))))
(define *cond (lambda (e table) (evcon (cond-lines-of e) table)))

;;;-----------------------------------------------------------------------------
;;; Action for 'let' (Desugaring logic identical to part_1.1)
;;;-----------------------------------------------------------------------------
(define let-bindings second)
(define let-body cddr)
(define (map-car-of-bindings bindings) (if (null? bindings) '() (cons (caar bindings) (map-car-of-bindings (cdr bindings)))))
(define (map-cadr-of-bindings bindings) (if (null? bindings) '() (cons (cadar bindings) (map-cadr-of-bindings (cdr bindings)))))
(define (last-element lst) (if (null? (cdr lst)) (car lst) (last-element (cdr lst))))
(define *let
  (lambda (e table)
    (let* ((bindings (let-bindings e)) (body-exps (let-body e))
           (vars (map-car-of-bindings bindings)) (initial-val-exps (map-cadr-of-bindings bindings))
           (lambda-body (if (null? body-exps) '(quote tls-undefined-let-body-value) (last-element body-exps))))
      (meaning (cons (list 'lambda vars lambda-body) initial-val-exps) table))))

;;;-----------------------------------------------------------------------------
;;; Interpreter Core: Application (Largely identical to part_1.1)
;;;-----------------------------------------------------------------------------
(define function-of car) (define arguments-of cdr)
(define evlis (lambda (args table) (if (null? args) '() (cons (meaning (car args) table) (evlis (cdr args) table)))))
(define *application (lambda (e table) (tls-apply (meaning (function-of e) table) (evlis (arguments-of e) table))))
(define primitive? (lambda (l) (and (pair? l) (eq? (first l) 'primitive))))
(define non-primitive? (lambda (l) (and (pair? l) (eq? (first l) 'non-primitive))))
(define :atom? (lambda (x) (cond ((atom? x) #t) ((null? x) #f) ((primitive? x) #t) ((non-primitive? x) #t) (else #f))))
(define apply-primitive-handler
  (lambda (name vals)
    (cond ((eq? name 'cons) (cons (first vals) (second vals)))
          ((eq? name 'car) (car (first vals))) ((eq? name 'cdr) (cdr (first vals)))
          ((eq? name 'null?) (null? (first vals))) ((eq? name 'eq?) (eq-val? (first vals) (second vals)))
          ((eq? name 'atom?) (:atom? (first vals))) ((eq? name 'zero?) (zero? (first vals)))
          ((eq? name 'add1) (add1 (first vals))) ((eq? name 'sub1) (sub1 (first vals)))
          ((eq? name 'number?) (number? (first vals)))
          (else (error "TLS (list-env) Error: Unknown primitive in apply-primitive-handler:" name)))))
(define table-of-closure-data first) (define formals-of-closure-data second) (define body-of-closure-data third)
(define apply-closure
  (lambda (closure-val vals)
    (let ((closure-data (second closure-val)))
      (meaning (body-of-closure-data closure-data)
               (extend-table (new-entry (formals-of-closure-data closure-data) vals)
                             (table-of-closure-data closure-data))))))
(define tls-apply
  (lambda (fun vals)
    (cond ((primitive? fun) (apply-primitive-handler (second fun) vals))
          ((non-primitive? fun) (apply-closure fun vals))
          (else (error "TLS (list-env) Error: Attempt to apply non-procedure value:" fun)))))