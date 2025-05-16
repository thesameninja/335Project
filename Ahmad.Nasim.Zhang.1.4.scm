;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Project: CSc 335 Project Spring 2025 
;;
;; Team: Sohail Ahmad, Umaima Nasim, Jia Xiang Zhang
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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

;;;-----------------------------------------------------------
;;; IV. Structural Induction Proof for Lexical Scope Correctness
;;;-----------------------------------------------------------------------------
;;;
;;; We want to prove that for any valid TLS expression `exp`, when evaluated as
;;; `(meaning exp table)`, all variable lookups adhere to lexical scope rules.
;;; Lexical scope means that a variable is resolved based on its textual position
;;; in the source code; specifically, a free variable within a function body refers
;;; to the binding of that variable in the environment where the function was *defined*,
;;; not where it was *called*.
;;;
;;; Let `CorrectLexicalValue(name, table)` denote the value of `name` that would be
;;; found by correctly applying lexical scoping rules within the environment `table`.
;;; Our `lookup-in-table` function is assumed to correctly search an environment `table`
;;; (a list of frames) from innermost to outermost. The core of the lexical scope
;;; argument rests on ensuring `lookup-in-table` is always called with the
;;; *lexically appropriate* `table`.
;;;
;;; We proceed by structural induction on the expression `exp` being evaluated
;;; by `(meaning exp table)`.
;;;
;;; Base Cases (Atomic Expressions):
;;;
;;;   1. `exp` is a Constant (number, boolean, primitive name):
;;;      `(meaning exp table)` calls `(*const exp table)`.
;;;      `*const` returns `exp` or `(primitive exp)`. No variable lookups occur
;;;      within `*const` itself for `exp`. Correct (vacuously true for lexical scope
;;;      of variables within `exp`).
;;;
;;;   2. `exp` is an Identifier (variable `name`):
;;;      `(meaning exp table)` calls `(*identifier name table)`.
;;;      `*identifier` calls `(lookup-in-table name table initial-table)`.
;;;      The variable `name` is looked up directly in the current environment `table`
;;;      passed to `meaning`. This is correct for variables not enclosed in any
;;;      further lexical constructs within `exp` itself. `table` here represents the
;;;      current lexical context. If `table` has been correctly constructed by
;;;      outer constructs (see inductive steps), then `lookup-in-table` will yield
;;;      `CorrectLexicalValue(name, table)`.
;;;
;;; Inductive Hypothesis (IH):
;;;   Assume that for any proper subexpression `sub_exp` of `exp`, evaluating
;;;   `(meaning sub_exp table')` correctly adheres to lexical scope for all
;;;   variable lookups within `sub_exp`. This means that `table'` is the
;;;   lexically appropriate environment for evaluating `sub_exp`.
;;;
;;; Inductive Steps (Compound Expressions):
;;;
;;;   1. `exp = ('quote datum)`:
;;;      `(meaning exp table)` calls `(*quote exp table)`, which returns `datum`.
;;;      No evaluation of subexpressions, no variable lookups within `datum`.
;;;      Correct for lexical scope.
;;;
;;;   2. `exp = ('lambda formals body-exp)`:
;;;      `(meaning exp table)` calls `(*lambda exp table)`.
;;;      `*lambda` creates a closure `(non-primitive (list table formals body-exp))`.
;;;      The crucial step here is that the *current* environment `table` (the
;;;      definition-time environment) is captured and stored within the closure structure.
;;;      This is the cornerstone of lexical scope. The creation itself doesn't evaluate
;;;      `body-exp` yet. Correct.
;;;
;;;   3. `exp = ('cond (q1 a1) (q2 a2) ...)`:
;;;      `(meaning exp table)` calls `(*cond exp table)`, which calls `(evcon lines table)`.
;;;      `evcon` evaluates `q_i` using `(meaning q_i table)`. By IH, variable
;;;      lookups in `q_i` are lexically correct with respect to `table`.
;;;      If `q_i` is true, `evcon` evaluates `a_i` using `(meaning a_i table)`.
;;;      By IH, variable lookups in `a_i` are lexically correct with respect to `table`.
;;;      The environment `table` remains the same lexical environment for all parts
;;;      of the `cond`. Correct.
;;;
;;;   4. `exp = (operator operand1 ... operand_k)` (Application):
;;;      `(meaning exp table)` calls `(*application exp table)`.
;;;      `*application` first evaluates the operator: `proc_val = (meaning operator table)`.
;;;      By IH, any variable lookups within `operator` (if it's complex) are
;;;      lexically correct with respect to `table`.
;;;      Then, arguments are evaluated: `arg_vals = (evlis operands table)`.
;;;      `evlis` calls `(meaning operand_i table)` for each operand. By IH, variable
;;;      lookups within each `operand_i` are lexically correct with respect to `table`.
;;;
;;;      `*application` then calls `(tls-apply proc_val arg_vals)`:
;;;      a. If `proc_val` is a primitive:
;;;         `(apply-primitive-handler name arg_vals)` is called. Primitives operate
;;;         on values; they don't perform lexical variable lookups in user code context.
;;;         Correct.
;;;      b. If `proc_val` is a closure `(non-primitive (list E_def formals_closure body_closure))`:
;;;         `(apply-closure proc_val arg_vals)` is called.
;;;         Inside `apply-closure`:
;;;         i.  The captured definition-time environment `E_def` is extracted.
;;;         ii. A new environment frame `E_args` is created by binding `formals_closure` to `arg_vals`.
;;;             `(new-entry formals_closure arg_vals)`
;;;         iii.The execution environment for the body is `E_exec = (extend-table E_args E_def)`.
;;;             This `E_exec` places argument bindings innermost, followed by the
;;;             bindings from the definition-time environment `E_def`.
;;;         iv. `(meaning body_closure E_exec)` is called.
;;;             Now, when `body_closure` is evaluated:
;;;             - If an identifier in `body_closure` is one of `formals_closure`,
;;;               `lookup-in-table` finds it in `E_args`. Correct.
;;;             - If an identifier in `body_closure` is a free variable (not one of
;;;               `formals_closure`), `lookup-in-table` searches beyond `E_args`
;;;               into `E_def`. This is precisely lexical scope: free variables
;;;               are resolved in the environment captured at the time of the
;;;               lambda's definition (`E_def`).
;;;             By IH (applied to `body_closure` as a subexpression evaluated in the
;;;             newly constructed `E_exec`), variable lookups within `body_closure`
;;;             will be resolved correctly according to this `E_exec`. Since `E_exec`
;;;             is constructed to prioritize arguments and then fall back to `E_def`,
;;;             this correctly implements lexical scope.
;;;
;;;   5. `exp = ('let ((v1 e1) ... (vk ek)) body1 ... body_m)`:
;;;      `(meaning exp table)` calls `(*let exp table)`.
;;;      `*let` desugars `exp` into an equivalent application:
;;;      `desugared_exp = ((lambda (v1 ... vk) effective_body) e1_eval ... ek_eval)`
;;;      (where `effective_body` is `body_m`, and `e_i_eval` are the expressions to get initial values).
;;;      It then calls `(meaning desugared_exp table)`.
;;;      This reduces the correctness of `let` to the correctness of application
;;;      and lambda, which are covered in step 4 and step 2 (for lambda creation).
;;;      - The expressions `e1 ... ek` (in `initial-val-exps` inside `*let`) are evaluated
;;;        effectively in the context of `table` when the desugared lambda is applied
;;;        (as they become arguments to the desugared lambda).
;;;        More precisely, the arguments to the created lambda `(lambda (v1 ... vk) effective_body)`
;;;        are the *values* resulting from evaluating `e1 ... ek` in the original `table`.
;;;        This is handled by `evlis` during the evaluation of `desugared_exp`.
;;;        So, any free variables in `e1 ... ek` are looked up in `table`. Correct.
;;;      - When the `effective_body` of the desugared lambda is evaluated, its environment
;;;        will be the `table` (captured by the implicit lambda) extended by `v1 ... vk`.
;;;        This correctly implements `let` semantics: bindings are local to the body,
;;;        and free variables in the body refer to bindings outside the `let` or
;;;        to outer `let` bindings if nested, following lexical rules due to the
;;;        lambda's captured environment.
;;;
;;; Conclusion:
;;;   Through structural induction, we have shown that for each type of TLS expression,
;;;   the evaluation process either directly uses the passed lexical environment `table`
;;;   or, in the crucial case of lambda application, constructs a new environment
;;;   `E_exec` that correctly chains the argument bindings with the lambda's
;;;   definition-time environment `E_def`. This ensures that all variable lookups,
;;;   particularly for free variables within function bodies, adhere to the rules of
;;;   lexical scope by referring to the environment where the function was defined.
;;;   The implementation mechanisms of closure creation (capturing `table` in `*lambda`)
;;;   and closure application (using the captured `table` in `apply-closure`) are
;;;   fundamental to this correctness.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;