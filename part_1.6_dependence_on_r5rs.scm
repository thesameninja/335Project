;; part_1.6_dependence_on_r5rs.scm
;;
;; This file contains the write-up for Part 1.6 of the TLS project.
;; It carefully explains the dependence of the TLS interpreter on the
;; underlying R5RS Scheme system (e.g., as provided by DrRacket).
;; Particular focus is given to the mechanics of function calling,
;; delineating the responsibilities of the TLS interpreter versus the
;; R5RS host system.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 1.6: Dependence of TLS on the Underlying R5RS System
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; I. General Dependencies of TLS on the R5RS Host System
;;;-------------------------------------------------------
;;;
;;; The TLS interpreter, while defining and executing its own language variant
;;; (TLS Scheme), is itself a program written in R5RS Scheme. As such, it is
;;; fundamentally dependent on the underlying R5RS implementation (e.g., DrRacket's
;;; R5RS environment) for its own execution, data representation, and core
;;; computational primitives.
;;;
;;; Key areas of dependence include:
;;;
;;; 1.  S-expression Parsing and Representation:
;;;     - Input: TLS programs are provided to the interpreter as R5RS S-expressions
;;;       (e.g., `'(add1 5)` or `'(lambda (x) x)`). The underlying R5RS system's
;;;       `read` procedure (or an equivalent mechanism used when loading files or
;;;       entering expressions in a REPL) is responsible for parsing raw character
;;;       streams into these S-expression data structures (nested lists, symbols,
;;;       numbers, booleans). The TLS interpreter does not implement its own parser
;;;       from text to S-expressions; it consumes these pre-parsed structures.
;;;     - Internal Data: All internal data structures used by the TLS interpreter,
;;;       such as the representation of TLS expressions themselves, environments
;;;       (lists of frames/entries), and closures, are constructed using R5RS's
;;;       native data types: pairs (`cons` cells), the empty list (`'()`), symbols,
;;;       numbers, and booleans.
;;;
;;; 2.  Basic R5RS Data Types and Primitive Procedures:
;;;     - The interpreter's code is written entirely in R5RS Scheme.
;;;     - It extensively uses R5RS primitive procedures for its internal logic,
;;;       structural manipulation, and decision-making. Examples include:
;;;       - List processing: `car`, `cdr`, `cons`, `null?`, `pair?`, `list`, `append`,
;;;         `member`, `assoc`, `length`.
;;;       - Type predicates: `symbol?`, `number?`, `boolean?`, `integer?`.
;;;       - Equality predicates: `eq?`, `equal?`.
;;;       - Arithmetic (for implementing TLS `add1`, `sub1`, `zero?`): `+`, `-`, `=`.
;;;       - Control structures (used to build the interpreter's logic): R5RS `cond`,
;;;         `if`, `let`, `let*`.
;;;       - Procedure definition: R5RS `lambda` (for defining all the interpreter's
;;;         functions like `meaning`, `*lambda`, `apply-closure`) and `define`.
;;;     - The correctness and defined behavior of these underlying R5RS primitives
;;;       are assumed and relied upon by the TLS interpreter.
;;;
;;; 3.  Execution Model and Runtime Environment:
;;;     - The R5RS system provides the complete runtime environment for executing
;;;       the R5RS code that constitutes the TLS interpreter. This includes managing
;;;       the program counter, executing R5RS instructions, and handling control flow.
;;;
;;; 4.  Memory Management (Allocation and Garbage Collection):
;;;     - All memory required for the data structures created and manipulated by the
;;;       TLS interpreter (e.g., new environment frames created during function calls,
;;;       closure objects, lists of evaluated arguments) is allocated by the
;;;       underlying R5RS system's memory manager.
;;;     - Crucially, the R5RS system's garbage collector is responsible for reclaiming
;;;       memory that is no longer reachable. For instance, when a TLS function call
;;;       completes and its local environment frame is no longer needed, the R5RS GC
;;;       will eventually reclaim the `cons` cells used to represent that frame.
;;;       The TLS interpreter logic dictates *when* a scope logically ends, but the
;;;       R5RS system handles the *physical* memory deallocation.
;;;
;;; 5.  Recursion and Call Stack Management:
;;;     - The TLS interpreter is heavily recursive. Core functions like `meaning`,
;;;       `evlis`, `evcon`, and environment lookup functions (`lookup-in-table`)
;;;       call themselves, either directly or indirectly.
;;;     - The R5RS system's call stack is used to manage these R5RS function calls
;;;       made by the interpreter. The depth of recursion that the TLS interpreter
;;;       can support (e.g., for evaluating deeply nested TLS expressions or
;;;       recursive TLS functions) is ultimately limited by the R5RS system's
;;;       call stack size.
;;;     - Tail-Call Optimization (TCO): If the underlying R5RS system implements TCO
;;;       (as standard R5RS requires), it benefits the TLS interpreter. Many of the
;;;       interpreter's own recursive calls are in tail position (e.g., in `evcon`'s
;;;       recursion, some paths in `lookup-in-table`). TCO allows these to execute
;;;       in constant stack space, enabling the interpretation of TLS programs that
;;;       perform deep recursion without exhausting the R5RS call stack.

;;;-----------------------------------------------------------------------------
;;; II. Mechanics of Function Calling: TLS System vs. R5RS Host System
;;;-----------------------------------------------------------------------------
;;;
;;; Understanding the division of labor during function calls is key to seeing
;;; the TLS-R5RS dependency. We must distinguish between:
;;;   - "TLS function calls": Applications within the TLS language being interpreted
;;;     (e.g., `(my-tls-func arg)` or `(add1 x)` written in TLS).
;;;   - "R5RS function calls": Calls to R5RS procedures made by the interpreter's
;;;     own R5RS code (e.g., the interpreter calling its own `meaning` function,
;;;     or calling R5RS `car`).
;;;
;;; A. TLS Primitive Application (e.g., `(add1 x)` in TLS code)
;;;
;;;    1.  TLS Interpreter's Work (Conceptual TLS Level):
;;;        - The `meaning` function identifies `(add1 x)` as an application.
;;;        - The `*application` action is invoked.
;;;        - `*application` calls `meaning` on the operator `add1`. This evaluates
;;;          `add1` to its TLS internal representation, e.g., `(primitive add1)`.
;;;        - `*application` calls `evlis` on `(x)` to evaluate arguments. `evlis` calls
;;;          `meaning` on `x`, which looks up `x` in the current TLS environment
;;;          (e.g., resulting in the TLS value `5`). `evlis` returns `(5)`.
;;;        - `*application` then calls `tls-apply` with the procedure value
;;;          `(primitive add1)` and the argument value list `(5)`.
;;;        - `tls-apply` sees the `'primitive` tag and dispatches to
;;;          `apply-primitive-handler` with the name `'add1` and arguments `(5)`.
;;;
;;;    2.  R5RS Host System's Work (Executing the Interpreter's R5RS Code):
;;;        - All the steps above involve the R5RS system executing the R5RS functions
;;;          (`meaning`, `*application`, `evlis`, `tls-apply`, `apply-primitive-handler`)
;;;          that make up the TLS interpreter.
;;;        - Inside `apply-primitive-handler`:
;;;          - An R5RS `cond` expression is evaluated to find the case for `'add1`.
;;;          - The R5RS code for that case is executed, e.g., `(+ (first '(5)) 1)`.
;;;            - R5RS `first` (which is R5RS `car`) is called on the R5RS list `(5)`, returning the R5RS number `5`.
;;;            - R5RS `+` (or the interpreter's R5RS `add1` function) is called with R5RS numbers `5` and `1`.
;;;            - The R5RS `+` primitive performs the actual addition, producing the R5RS number `6`.
;;;        - This R5RS value `6` is then returned up through the R5RS call chain of
;;;          `apply-primitive-handler`, `tls-apply`, `*application`, and `meaning`.
;;;
;;;    Division of Labor for Primitives:
;;;    - TLS Interpreter: Implements the logic for parsing the TLS application,
;;;      evaluating its components (operator and operands) according to TLS rules,
;;;      identifying it as a primitive call, and mapping the TLS primitive name
;;;      to an underlying operation.
;;;    - R5RS Host System: Executes all the R5RS code of the interpreter. Crucially,
;;;      it performs the *actual fundamental computation* (e.g., arithmetic, list
;;;      manipulation) defined by the R5RS primitive procedure that the TLS
;;;      primitive is mapped to.
;;;
;;; B. TLS User-Defined Lambda Application (e.g., `(my-tls-lambda arg)` in TLS code)
;;;
;;;    1.  TLS Interpreter's Work (Conceptual TLS Level):
;;;        - `meaning` identifies `(my-tls-lambda arg)` as an application.
;;;        - `*application` calls `meaning` on `my-tls-lambda`. This evaluates
;;;          `my-tls-lambda` (which must be bound to a closure in the TLS environment)
;;;          to its closure representation, e.g.,
;;;          `Closure_F = (non-primitive (list Env_captured Formals_F Body_F))`.
;;;        - `*application` calls `evlis` on `(arg)`, evaluating `arg` to its TLS
;;;          value, e.g., `Value_arg`. `evlis` returns `(Value_arg)`.
;;;        - `*application` calls `tls-apply` with `Closure_F` and `(Value_arg)`.
;;;        - `tls-apply` sees the `'non-primitive` tag and dispatches to `apply-closure`.
;;;        - `apply-closure` performs these TLS-level semantic actions:
;;;          a. Extracts `Env_captured`, `Formals_F`, and `Body_F` from `Closure_F`.
;;;          b. Creates a new TLS environment frame, `Env_args`, by binding `Formals_F`
;;;             to `(Value_arg)` using `new-entry`.
;;;          c. Forms the execution environment for `Body_F` as
;;;             `Env_exec = (extend-table Env_args Env_captured)`. This establishes
;;;             lexical scope.
;;;          d. Critically, `apply-closure` then calls `(meaning Body_F Env_exec)`.
;;;             This is a recursive invocation of the TLS interpreter's main evaluation
;;;             loop to evaluate the body of the TLS lambda.
;;;
;;;    2.  R5RS Host System's Work (Executing the Interpreter's R5RS Code):
;;;        - Executes all the R5RS functions that constitute the TLS interpreter's
;;;          logic as described above (`meaning`, `*application`, `evlis`, `tls-apply`,
;;;          `apply-closure`, `new-entry`, `extend-table`, `lookup-in-table` for
;;;          resolving `my-tls-lambda`).
;;;        - The R5RS call stack is used for all these R5RS function calls.
;;;        - When `apply-closure` makes the R5RS call `(meaning Body_F Env_exec)`, this
;;;          R5RS call is placed on the R5RS call stack. This call effectively
;;;          "enters" the TLS lambda's body for interpretation.
;;;        - If `Body_F` itself contains further TLS expressions, applications, or
;;;          control structures, their interpretation will lead to more R5RS function
;;;          calls within the interpreter, all managed by the R5RS call stack.
;;;        - When `(meaning Body_F Env_exec)` eventually returns an R5RS value
;;;          (representing the TLS value of `Body_F`), this value is returned up
;;;          through the R5RS call chain of `apply-closure`, `tls-apply`, `*application`,
;;;          and the initial `meaning` call for the application.
;;;
;;;    Division of Labor for User-Defined Lambdas:
;;;    - TLS Interpreter: Defines and manages the concept of closures, the rules for
;;;      creating them (`*lambda`), the rules for environment extension upon lambda
;;;      application (`apply-closure`), and the initiation of the lambda body's
;;;      evaluation within the correct lexically-scoped environment. It "drives" the
;;;      evaluation according to TLS semantics.
;;;    - R5RS Host System: Provides the fundamental execution engine for all R5RS
;;;      code that makes up the interpreter. The "calling" of a TLS lambda translates
;;;      into an R5RS function call to the `meaning` procedure for the lambda's body.
;;;      The R5RS call stack underpins the entire evaluation process, including any
;;;      nested or recursive TLS calls within the lambda's body. The R5RS GC manages
;;;      the memory for the closure objects and environment frames created by TLS.
;;;
;;; C. Summary of Function Calling Mechanics:
;;;
;;;    - The R5RS host system's function call mechanism is the engine that executes
;;;      the *interpreter itself*. All parts of the interpreter, like `meaning`,
;;;      `*application`, `tls-apply`, are R5RS functions.
;;;    - The TLS interpreter *simulates* a function call mechanism for the TLS language.
;;;      - For TLS primitives, this simulation involves mapping to and executing
;;;        an underlying R5RS primitive or helper.
;;;      - For TLS lambdas, this simulation involves:
;;;        1. Creating and managing closure data structures (R5RS lists).
;;;        2. Manipulating TLS environment data structures (R5RS lists of lists).
;;;        3. Recursively calling its own R5RS `meaning` function to evaluate
;;;           the lambda body within the correctly constructed (lexical) TLS environment.
;;;
;;;    Thus, a "TLS function call" is not a direct hardware-level or OS-level function
;;;    call in the same way an R5RS function call is. Instead, it's a high-level
;;;    process orchestrated by the R5RS code of the TLS interpreter, which itself
;;;    makes many R5RS function calls to achieve the simulation. The R5RS system
;;;    does the low-level work of managing stack frames for the interpreter's R5RS
;;;    functions, while the TLS interpreter defines the higher-level semantics of
;;;    what a "call" means in TLS, including lexical scope and environment handling.
;;