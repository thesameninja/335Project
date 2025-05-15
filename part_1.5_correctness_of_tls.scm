;; part_1.5_correctness_of_tls.scm
;;
;; This file contains the write-up for Part 1.5 of the TLS project.
;; It carefully identifies a standard of correctness for the TLS interpreter
;; and provides a structured argument (proof outline) demonstrating that the
;; entire R5RS implementation of TLS adheres to this standard.
;; The proof arguments for recursive procedures attempt to follow the
;; "Proof for Recursive Procedures / Data Induction" template.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 1.5: Correctness of the TLS Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;-----------------------------------------------------------------------------
;;; I. Standard of Correctness for the TLS Interpreter
;;;-----------------------------------------------------------------------------
;;;
;;; Standard:
;;; Our TLS interpreter is considered "correct" if, for any syntactically valid
;;; TLS program (as defined by the inductive definition in Part 1.2 and accepted
;;; by the syntax checker), the `(value exp)` function produces a result that is
;;; semantically equivalent to the outcome one would expect by manually applying
;;; the evaluation rules described in Chapter 10 of "The Little Schemer."
;;;
;;; This implies implementation of:
;;; 1. Self-evaluation for numbers and booleans.
;;; 2. `quote` behavior (returning the datum unevaluated).
;;; 3. Standard Scheme semantics for TLS primitives (`cons`, `car`, `cdr`, `null?`,
;;;    `eq?` (using `eq-val?`), `atom?` (using `:atom?`), `zero?`, `add1`, `sub1`, `number?`).
;;; 4. `cond` evaluation logic (sequential test, first true branch, `else`).
;;; 5. Lexical variable resolution (innermost binding or error for unbound).
;;; 6. `lambda` evaluating to first-class closures that correctly capture their
;;;    lexical (definition-time) environment.
;;; 7. Procedure application (operator/operand evaluation, then applying the
;;;    procedure value to argument values, with correct environment setup for closures).
;;; 8. `let` expressions behaving according to their standard desugaring into
;;;    lambda application (binding expressions evaluated in outer scope, body in new scope).
;;;
;;; Let CorrectValue(exp, table) denote this correct semantic value of
;;; a TLS expression `exp` in environment `table`.

;;;-----------------------------------------------------------------------------
;;; II. Proof of Correctness for Auxiliary Procedures and Data Structures
;;;-----------------------------------------------------------------------------
;;;
;;; Before proving the main `meaning` function, we establish the correctness of
;;; key auxiliary components it relies upon.
;;;
;;; A. Environment Subsystem Operations
;;;    (Focusing on `lookup-in-table` as a key recursive example. `new-entry` and
;;;    `extend-table` are simpler list constructions, correct by inspection given R5RS `list` and `cons`.)
;;;
;;;    Function: `(lookup-in-table name table table-f)`
;;;
;;;    1. (PRE-CONDITION) INPUT:
;;;       - `name`: A symbol to be looked up.
;;;       - `table`: A well-formed TLS environment (a list of frames/entries).
;;;       - `table-f`: A nullary failure thunk.
;;;
;;;    2. BASE STEP (How terminates):
;;;       - If `table` is null (empty list `'()`): Calls `(table-f)`. Correct.
;;;
;;;    3. (IH) INDUCTION HYPOTHESIS (on the structure of `table`):
;;;       Assume `(lookup-in-table name (cdr table) table-f)` is correct.
;;;       Assume `lookup-in-entry` is correct for a single frame.
;;;
;;;    4. (IS) INDUCTION STEP (When `table` is not null):
;;;       - Calls `(lookup-in-entry name (car table) entry-failure-thunk)`,
;;;         where `entry-failure-thunk` recursively calls `(lookup-in-table name (cdr table) table-f)`.
;;;       - If found in `(car table)`, returns value (correct).
;;;       - Else, by IH, recursive call correctly searches rest of table. Correct.
;;;
;;;    5. (POST-CONDITION) OUTPUT:
;;;       Returns value of innermost binding of `name` or calls `(table-f)`. Correct.
;;;
;;; B. Value Representation Predicates and Helpers
;;;    - `primitive?`, `non-primitive?`, `:atom?`, `eq-val?`, `build`, `let` helpers:
;;;      Correct by inspection of their definitions and reliance on R5RS primitives.
;;;
;;; C. List of Argument Expressions Evaluation (`evlis`)
;;;
;;;    Function: `(evlis args-exps table)`
;;;
;;;    1. (PRE-CONDITION) INPUT:
;;;       - `args-exps`: A proper list of valid TLS expressions.
;;;       - `table`: A well-formed TLS environment.
;;;
;;;    2. BASE STEP:
;;;       - If `args-exps` is null: Returns `'()`. Correct.
;;;
;;;    3. (IH) INDUCTION HYPOTHESIS (on structure of `args-exps`):
;;;       Assume `(evlis (cdr args-exps) table)` is correct.
;;;       Assume `(meaning (car args-exps) table)` is correct (main IH for `meaning`).
;;;
;;;    4. (IS) INDUCTION STEP (When `args-exps` is not null):
;;;       - Computes `V1 = (meaning (car args-exps) table)`.
;;;       - Recursively calls `L_rest = (evlis (cdr args-exps) table)`.
;;;       - Returns `(cons V1 L_rest)`. Correctly constructs list of values.
;;;
;;;    5. (POST-CONDITION) OUTPUT:
;;;       Returns a list of evaluated argument values. Correct.
;;;
;;; D. Application Dispatch and Execution (`tls-apply`, `apply-primitive-handler`, `apply-closure`)
;;;    - `tls-apply`: Correctly dispatches based on `primitive?`/`non-primitive?`.
;;;    - `apply-primitive-handler`: Correctly maps primitive names to R5RS host operations.
;;;    - `apply-closure`: Correctly sets up lexical environment and calls `meaning` (main IH applies).
;;;      Relies on correct environment operations (II.A) and closure structure.

;;;-----------------------------------------------------------------------------
;;; III. Proof of Correctness for Core Evaluation Function `(meaning exp table)`
;;;-----------------------------------------------------------------------------
;;;
;;; We use structural induction on the TLS expression `exp`.
;;;
;;; 1. (PRE-CONDITION) INPUT for `meaning(exp, table)`:
;;;    - `exp`: A syntactically valid TLS S-expression.
;;;    - `table`: A well-formed TLS environment.
;;;
;;; 2. BASE CASES (when `exp` is an atom):
;;;    - Constants (number/boolean): `(*const exp table)` returns `exp`.
;;;      POST-CONDITION: Returns CorrectValue(exp, table). Correct.
;;;    - Primitive Names: `(*const exp table)` returns `(primitive exp)`.
;;;      POST-CONDITION: Returns CorrectValue(exp, table) (the tagged marker). Correct.
;;;    - Identifiers: `(*identifier exp table)` calls `lookup-in-table`.
;;;      POST-CONDITION: By II.A, returns CorrectValue(exp, table). Correct.
;;;
;;; 3. (IH) INDUCTION HYPOTHESIS for `meaning(exp, table)`:
;;;    Assume for any proper structural sub-component `sub_exp` of `exp`,
;;;    `(meaning sub_exp table')` correctly computes CorrectValue(sub_exp, table').
;;;
;;; 4. (IS) INDUCTION STEP (when `exp` is a list/compound expression):
;;;
;;;    a. `exp = ('quote datum)` (Action: `*quote`):
;;;       - `(*quote exp table)` returns `datum`.
;;;       - POST-CONDITION: Returns CorrectValue(exp, table). Correct.
;;;
;;;    b. `exp = ('lambda formals body-exp)` (Action: `*lambda`):
;;;       - `(*lambda exp table)` returns closure `(non-primitive (list table formals body-exp))`.
;;;       - POST-CONDITION: Returns CorrectValue(exp, table) (the closure). Correct.
;;;
;;;    c. `exp = ('cond clauses...)` (Action: `*cond` via `evcon`):
;;;       - `evcon` uses `meaning` on questions/answers (sub-expressions). By IH, these are correct.
;;;       - `evcon`'s logic correctly combines these to implement `cond` semantics.
;;;       - POST-CONDITION: Returns CorrectValue(selected_answer, table). Correct.
;;;
;;;    d. `exp = ('let bindings body-exps...)` (Action: `*let`):
;;;       - `(*let exp table)` desugars to `desugared_exp = ((lambda ...) initial_vals...)`.
;;;         Calls `(meaning desugared_exp table)`.
;;;       - This call is handled by case (e) (Application). Desugaring correctly maps `let` semantics.
;;;       - POST-CONDITION: Returns CorrectValue(exp, table). Correct.
;;;
;;;    e. `exp = (operator operand1 ...)` (Action: `*application`):
;;;       - `(*application exp table)` calls `(tls-apply proc_val arg_vals)`.
;;;       - `proc_val = (meaning operator table)` (Correct by IH).
;;;       - `arg_vals = (evlis operands table)` (Correct by II.C, which uses IH).
;;;       - `tls-apply proc_val arg_vals`:
;;;         - By II.D, `tls-apply` correctly dispatches.
;;;         - If primitive: `apply-primitive-handler` correctly executes it.
;;;         - If closure `C = (non-primitive (list Env_Definition formals body_exp))`:
;;;           `apply-closure` calls `(meaning body_exp Env_Execution)`.
;;;           `Env_Execution` (the environment for the body, formed from Env_Definition
;;;           and the arguments) is correctly formed (by II.A, II.D, and Part 1.4 reasoning).
;;;           The call to `meaning` on `body_exp` is correct by IH.
;;;           This correctly implements lambda application with lexical scope.
;;;       - POST-CONDITION: Returns CorrectValue(exp, table). Correct.
;;;
;;; 5. (POST-CONDITION) OUTPUT for `meaning(exp, table)`:
;;;    In all cases, `(meaning exp table)` computes CorrectValue(exp, table).
;;;
;;; --- IV. Overall Conclusion of Correctness ---
;;;
;;; The TLS interpreter's components (environment, value representation, core evaluation
;;; logic) are individually argued to be correct. The main evaluation function `meaning`,
;;; by structural induction on expressions, correctly implements the semantics of each TLS
;;; construct, relying on these correct components. Therefore, the entire R5RS
;;; implementation of TLS is correct with respect to the defined standard.
;;;

;;;-----------------------------------------------------------------------------
;;; V. Demonstrating Key Language Features in TLS
;;;-----------------------------------------------------------------------------
;;;
;;; The correctness proof establishes that our TLS interpreter adheres to its
;;; defined semantics. This adherence means TLS naturally supports fundamental
;;; features like closures and first-class functions, which are direct consequences
;;; of how `lambda`, environments, and application are implemented.
;;;
;;; A. Closures
;;;
;;; A closure is a procedure that "remembers" the environment in which it was
;;; created. This is primarily achieved by the `*lambda` action capturing the
;;; current `table` (environment) and `apply-closure` using this captured `table`
;;; when the procedure is invoked.
;;;
;;; TLS Example Demonstrating Closures:
;;;
;;;   (let ((make-creator (lambda (captured-val)
;;;                         (lambda (new-val)
;;;                           (cons captured-val new-val)))))
;;;     (let ((creator-for-10 (make-creator 10))
;;;           (creator-for-abc (make-creator (quote abc))))
;;;       ;; Now, creator-for-10 is a closure that has captured '10'.
;;;       ;; And creator-for-abc is a closure that has captured 'abc'.
;;;       ;; We can apply them to see this:
;;;       (cons (creator-for-10 5)         ; Expected: (10 . 5)
;;;             (creator-for-abc #t))))    ; Expected: ((abc . #t)) -> resulting in ((10 . 5) . ((abc . #t) . ()))
;;;
;;; How TLS handles this (and why it's correct):
;;; 1. `(make-creator 10)`:
;;;    - `make-creator` is called. `captured-val` becomes 10.
;;;    - The inner `(lambda (new-val) (cons captured-val new-val))` is evaluated.
;;;    - `*lambda` creates a closure. This closure packages:
;;;      - The formals: `(new-val)`
;;;      - The body: `(cons captured-val new-val)`
;;;      - The current environment: This environment contains the binding `(captured-val . 10)`.
;;;    - This closure is returned and bound to `creator-for-10`.
;;; 2. `(make-creator (quote abc))` proceeds similarly, creating a closure for `creator-for-abc`
;;;    where its captured environment contains `(captured-val . abc)`.
;;; 3. `(creator-for-10 5)`:
;;;    - `creator-for-10` (the closure) is applied to `5`.
;;;    - `apply-closure` takes this closure and `5`.
;;;    - It extends the closure's *captured* environment (where `captured-val` is 10)
;;;      with the new binding `(new-val . 5)`.
;;;    - The body `(cons captured-val new-val)` is evaluated in this extended environment.
;;;      `captured-val` resolves to 10 (from the captured environment).
;;;      `new-val` resolves to 5 (from the arguments).
;;;    - Result is `(10 . 5)`.
;;; 4. `(creator-for-abc #t)` works analogously, resulting in `(abc . #t)`.
;;;
;;; The successful execution of such an expression (producing `((10 . 5) abc . #t)`
;;; if `cons` behaves as expected for the final `cons`) demonstrates that TLS correctly
;;; implements closures, as each generated procedure remembers its distinct lexical environment.
;;;
;;; B. First-Class Functions
;;;
;;; First-class functions mean that functions are treated like any other value in the
;;; language: they can be passed as arguments to other functions, returned as results
;;; from functions, and assigned to variables (or bound in `let` expressions).
;;;
;;; TLS Example Demonstrating First-Class Functions (Passing as Argument):
;;;
;;;   (let ((apply-it (lambda (func arg)
;;;                     (func arg))))
;;;     (let ((increment (lambda (n) (add1 n))))
;;;       (apply-it increment 100))) ; Expected: 101
;;;
;;; How TLS handles this:
;;; 1. `(lambda (func arg) (func arg))` evaluates to a closure, bound to `apply-it`.
;;; 2. `(lambda (n) (add1 n))` evaluates to a closure, bound to `increment`.
;;; 3. `(apply-it increment 100)`:
;;;    - `apply-it` (the closure) is called.
;;;    - `func` is bound to the closure `increment`.
;;;    - `arg` is bound to `100`.
;;;    - The body `(func arg)` is evaluated. This becomes an application of the
;;;      closure `increment` to the argument `100`.
;;;    - `(increment 100)` is evaluated, which `apply-closure` handles by looking up
;;;      `increment`'s body `(add1 n)`, extending its (empty in this case) captured
;;;      environment with `(n . 100)`, and evaluating `(add1 n)`, yielding `101`.
;;;
;;; Returning functions as results is already demonstrated by the `make-creator`
;;; example in the Closures section, where `make-creator` returns a new function (a closure).
;;;
;;; Storing in Data Structures (Conceptual):
;;; While TLS's `cons` can store anything, including the internal representation of
;;; closures, more complex examples might involve `let` bindings.
;;;
;;;   (let ((op (lambda (x) (add1 x)))) ; op is bound to a function
;;;     (let ((data (cons op (quote (some-other-data))))) ; Function in car of a pair
;;;       ((car data) 10))) ; Retrieve function from pair and apply it. Expected: 11
;;;
;;; How TLS handles this:
;;; 1. `(lambda (x) (add1 x))` evaluates to a closure, bound to `op`.
;;; 2. `(cons op ...)` creates a pair where the `car` is this closure. This pair is bound to `data`.
;;; 3. `(car data)` evaluates `data` to the pair, then `car` extracts the closure.
;;; 4. This extracted closure is then applied to `10`. `apply-closure` proceeds as usual.
;;;
;;; The ability of the TLS interpreter to execute these examples correctly, as per
;;; the semantics outlined in the proof (especially how `*lambda` produces tagged
;;; procedure values and `*application` with `tls-apply` handles them), confirms that
;;; functions are indeed first-class citizens in TLS. They are data that can be
;;; created, passed, returned, and applied, all consistent with the interpreter's
;;; core evaluation rules.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;