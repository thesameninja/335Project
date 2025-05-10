;; part_1.4_closures_lexical_scope.scm
;;
;; This file contains the write-up for Part 1.4 of the TLS project.
;; It discusses closures and lexical scope, and provides an argument
;; that the TLS implementation correctly implements these concepts,
;; 
;;
;; The relevant TLS interpreter code being analyzed is primarily:
;; - The `*lambda` action procedure (in `part_1.1_interpreter_original.scm` and
;;   `part_1.3_interpreter_list_env.scm`) which creates closures.
;; - The `apply-closure` procedure (in the same files) which applies these closures.
;; - The environment lookup mechanism (`lookup-in-table` and its helpers).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 1.4: Understanding Closures and Lexical Scope in TLS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;-----------------------------------------------------------------------------
;;; I. What are Lexical Scope and Closures?
;;;-----------------------------------------------------------------------------

;;; A. Lexical Scope (or Static Scope):
;;;
;;; Imagine you're reading program code. Where a variable (like 'x' or 'my-name')
;;; is written down in the text of the program determines what that variable refers to.
;;; If you use a variable inside a function, Scheme (and our TLS) first looks to see
;;; if that variable is one of the function's own inputs (its parameters).
;;;
;;; If it's not a parameter, Scheme then looks in the area of code *immediately
;;; surrounding where that function was originally defined*. If it's still not found,
;;; Scheme keeps looking outwards, block by block, towards the beginning of the file
;;; or the main program area.
;;;
;;; The most important idea here is that this "looking up" rule is decided when the
;;; function is *first created or defined* in the code, not when the function is
;;; *actually used or called* later on. So, a function "remembers" where its
;;; non-parameter variables should come from, based on where it was born in the code.

;;; B. Closures:
;;;
;;; A closure is a special package that our interpreter creates. This package contains
;;; two things:
;;;   1. The function itself (its parameters and its body code).
;;;   2. A "memory" or "snapshot" of the environment (all the variable names and
;;;      their values) that existed at the exact moment and place where that
;;;      function was defined in the code.
;;;
;;; Think of a baker (the function) who has a recipe (the function code). When the
;;; baker first writes the recipe, they might be in a special kitchen (the definition
;;; environment) that has unique local ingredients (variable values like 'x = 10').
;;; A closure is like taking that recipe *and* a small box containing samples of all
;;; those unique local ingredients from that original kitchen.
;;;
;;; Later, if the baker (or someone else) uses that recipe and its ingredient box in
;;; a completely different kitchen, they still use the ingredients from the box for
;;; anything the recipe calls for that isn't a new input.
;;;
;;; Closures are the technical way that programming languages like Scheme (and our TLS)
;;; make lexical scope work. The function "closes over" its original environment.

;;;-----------------------------------------------------------------------------
;;; II. How TLS Implements Closures and Lexical Scope
;;;-----------------------------------------------------------------------------
;;;
;;; Our TLS interpreter correctly handles lexical scope by creating and using closures.
;;; Here’s a breakdown of how the relevant parts of our interpreter code work:

;;; A. Creating a Closure (The `*lambda` action):
;;;
;;;    - When our interpreter sees a `(lambda (param1 ...) body-expression)` in TLS code,
;;;      the `*lambda` procedure is called.
;;;    - `*lambda` takes the current `table` (which is our interpreter's name for the
;;;      environment at that moment) and packages it together with the list of
;;;      `param1 ...` (the parameter names) and the `body-expression`.
;;;    - This package is exactly the TLS closure. Our interpreter stores it in a
;;;      special format: `(non-primitive (list current-table parameters body-expression))`.
;;;    - The `current-table` saved here is vital: it’s a snapshot of all variable
;;;      bindings that are visible right where the `lambda` was written in the TLS code.
;;;      This is the function's "birth environment."

;;; B. Using a Closure (The `apply-closure` procedure):
;;;
;;;    - When a TLS lambda (which has been turned into a closure) is called with some
;;;      arguments, our `apply-closure` procedure takes over.
;;;    - `apply-closure` receives the closure package and the list of (already evaluated)
;;;      argument values.
;;;    - It does the following:
;;;      1. Unpacks the closure: It gets out the `captured-table` (the "birth environment"
;;;         snapshot), the original `parameters` list, and the `body-expression`.
;;;      2. Creates argument bindings: It makes a new, small, temporary environment frame.
;;;         In this frame, each parameter name from the `parameters` list is paired up
;;;         with the corresponding argument value it was just called with.
;;;      3. Forms the execution environment: It takes this new argument frame and puts
;;;         it *in front of* the `captured-table`. This combined table is now the
;;;         complete environment that the `body-expression` will use when it runs.
;;;         The arguments are closest (most local), and then the "birth environment"
;;;         bindings are available.
;;;      4. Runs the body: Finally, `apply-closure` tells the main interpreter function
;;;         (`meaning`) to execute the `body-expression` using this newly formed
;;;         execution environment.

;;;-----------------------------------------------------------------------------
;;; III. Argument: Why This TLS Implementation is Correct for Lexical Scope
;;;-----------------------------------------------------------------------------
;;;
;;; We can be confident that our TLS interpreter implements lexical scope correctly
;;; because of how `*lambda` and `apply-closure` work together.
;;;
;;; When the `body-expression` of a called lambda is being evaluated by `meaning`,
;;; and it encounters a variable name, the `lookup-in-table` function searches the
;;; execution environment (set up by `apply-closure`):
;;;
;;;   1. Check for Parameters:
;;;      `lookup-in-table` first looks in the innermost part of the execution
;;;      environment. This innermost part is the argument frame (created in step B.2
;;;      above), which contains the bindings for the lambda's own parameters.
;;;      If the variable name matches one of the parameters, its corresponding
;;;      argument value is used. This is correct for how function parameters work.
;;;
;;;   2. Check for Free Variables (using the Captured Environment):
;;;      If the variable name is NOT one of the lambda's parameters (meaning it's a
;;;      "free variable" relative to that lambda), `lookup-in-table` won't find it
;;;      in the argument frame.
;;;      The search then automatically continues to the next part of the execution
;;;      environment. This next part is exactly the `captured-table` – the snapshot
;;;      of the environment from where the lambda was originally defined (saved by `*lambda`).
;;;      So, if the free variable was defined in the scope where the lambda was created,
;;;      its value will be found in this `captured-table`.
;;;
;;; This process ensures that:
;;;   - Parameters get their values from the function call.
;;;   - Any other variable (free variable) inside the lambda body gets its value
;;;     from the environment where the lambda was *written*, not from the
;;;     environment where the lambda *happened to be called*.
;;;
;;; This is the definition of lexical scope. The environment of the call site
;;; (where the function is used) does not influence how free variables inside the
;;; function are resolved, because the function carries its definitional environment
;;; (the `captured-table`) around with it inside its closure.
;;;
;;;
;;; Example to Illustrate Correctness:
;;;
;;;   Consider this TLS code:
;;;   (let ((x 10))                ; Outer scope: x is 10. Call this environment Env_Outer.
;;;     (let ((my-adder           ; Inner scope, extending Env_Outer. Call this Env_Inner_Def_Site.
;;;             (lambda (y)       ; 'my-adder' is defined here.
;;;               (add1 x)))      ; 'x' is free in 'my-adder'. It will refer to x from Env_Outer.
;;;           (x 20))            ; 'x' is now shadowed to 20 within Env_Inner_Def_Site for other uses.
;;;       (my-adder 5)))          ; 'my-adder' is called here, from Env_Inner_Body.
;;;
;;;   Trace:
;;;   - The outer `let` binds `x` to `10`. The environment `Env_Outer` now has `x=10`.
;;;   - The inner `let` is evaluated. Its binding expressions are evaluated in `Env_Outer`.
;;;     - The `(lambda (y) (add1 x))` is evaluated by `*lambda`. At this point, the
;;;       active environment for resolving free variables for *this lambda's definition*
;;;       is `Env_Outer` (where `x` is `10`). `*lambda` creates a closure for `my-adder`.
;;;       This closure, let's call it `Closure_my_adder`, captures `Env_Outer`.
;;;     - The inner `let` also binds its own `x` to `20`.
;;;     - The environment for the body of this inner `let` (where `(my-adder 5)` is)
;;;       is `Env_Inner_Body`. In `Env_Inner_Body`, `my-adder` refers to `Closure_my_adder`,
;;;       and its local `x` is `20`.
;;;   - `(my-adder 5)` is evaluated in `Env_Inner_Body`.
;;;     - `my-adder` resolves to `Closure_my_adder`.
;;;     - `apply-closure` is called with `Closure_my_adder` and argument `5`.
;;;     - Inside `apply-closure`:
;;;       - The captured environment from `Closure_my_adder` is `Env_Outer` (where `x` is `10`).
;;;       - A new argument frame `((y 5))` is created.
;;;       - The execution environment for the body `(add1 x)` becomes:
;;;         `Env_Execution_for_my_adder_body` which is `(((y 5)) . Env_Outer)`.
;;;         (The dot notation indicates extending `Env_Outer` with the `y` binding).
;;;     - `(meaning '(add1 x) Env_Execution_for_my_adder_body)` is called:
;;;       - `add1` is a primitive.
;;;       - `x` is looked up in `Env_Execution_for_my_adder_body`:
;;;         - It's not found in the innermost frame `((y 5))`.
;;;         - The search continues to `Env_Outer`. In `Env_Outer`, `x` is found with value `10`.
;;;       - So, `(add1 x)` becomes `(add1 10)`, which is computed as `11`.
;;;
;;;   The final result of the whole expression is `11`.
;;;   This is correct lexical scoping because the `x` inside `my-adder` used the `x=10`
;;;   from `Env_Outer` (the environment where `my-adder` was defined), not the `x=20`
;;;   from `Env_Inner_Body` (the environment where `my-adder` was called).
;;;
;;; Therefore, the TLS interpreter, through its specific mechanisms for `*lambda` (closure
;;; creation with environment capture) and `apply-closure` (using the captured environment
;;; for body evaluation), correctly implements lexical scope.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
