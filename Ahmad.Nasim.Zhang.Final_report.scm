;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Project: CSc 335 Project Spring 2025 
;;
;; Team: Sohail Ahmad, Umaima Nasim, Jia Xiang Zhang
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;-----------------------------------------------------------------------------
;;; I. Project Overview
;;;-----------------------------------------------------------------------------
;;;
;;; This project involved the development and analysis of an interpreter for
;;; "TLS Scheme," a subset of Scheme based on Chapter 10 of "The Little Schemer."
;;; The project was divided into seven parts, covering the implementation of the
;;; interpreter, a syntax checker, environment system analysis, proofs of
;;; correctness for lexical scope and the overall interpreter, an examination of
;;; dependencies on the underlying R5RS system, and an extension for recursion
;;; using the Y-combinator. All implementations were done in pure functional R5RS.

;;;-----------------------------------------------------------------------------
;;; II. Summary of Project Parts
;;;-----------------------------------------------------------------------------

;;; Part 1.1: TLS Interpreter Implementation
;;;   Goal: Implement the TLS interpreter in pure functional R5RS, provide
;;;         function specifications, and demonstrate with examples.
;;;   Achievement:
;;;     - An interpreter for TLS, including the 'let' special form (desugared to
;;;       lambda application), was implemented in `part_1.1_interpreter_original.scm`.
;;;     - Functions within the interpreter include specifications detailing their
;;;       purpose, inputs, and outputs.
;;;     - The `run_all_tests.scm` file includes examples demonstrating the
;;;       interpreter's capability to evaluate various TLS constructs.
;;;   Key Files: `part_1.1_interpreter_original.scm`, `shared_definitions.scm`, `run_all_tests.scm`

;;; Part 1.2: Inductive Definition and Syntax Checker
;;;   Goal: Provide an inductive definition for TLS, implement a purely functional
;;;         R5RS syntax checker for TLS capable of detecting malformed expressions,
;;;         arity errors for primitives, and unbound variables.
;;;   Achievement:
;;;     - A detailed inductive definition of TLS syntax (including 'let') is provided
;;;       within `part_1.2_syntax_checker.scm`.
;;;     - A non-evaluating syntax checker (`check-tls-syntax`) was implemented in
;;;       `part_1.2_syntax_checker.scm`. It recursively validates expression
;;;       structures against the defined grammar.
;;;     - The checker identifies:
;;;       (i)   Malformed `cond`, `lambda`, and `let` expressions.
;;;       (ii)  Incorrect number of arguments for primitive procedures by
;;;             consulting definitions in `shared_definitions.scm`.
;;;       (iii) The presence of unbound variables by maintaining a lexical
;;;             environment during the syntax check.
;;;     - Test cases in `run_all_tests.scm` validate the syntax checker's functionality.
;;;   Key Files: `part_1.2_syntax_checker.scm`, `shared_definitions.scm`, `run_all_tests.scm`

;;; Part 1.3: Environment Subsystem Analysis and Modification
;;;   Goal: Specify the environment subsystem, prove its correctness, change its
;;;         representation to use lists of bindings, and show the new
;;;         representation satisfies the specification and works.
;;;   Achievement:
;;;     - A specification for the environment subsystem (operations for creation,
;;;       extension, and lookup) is detailed in `part_1.3_interpreter_list_env.scm`.
;;;     - The original environment representation (names-values pairs from Part 1.1)
;;;       implicitly adheres to this specification through its simpler structure.
;;;     - The environment representation was changed in
;;;       `part_1.3_interpreter_list_env.scm` to use lists of frames, where each
;;;       frame is a list of (name . value) bindings.
;;;     - A proof is provided in the comments of `part_1.3_interpreter_list_env.scm`
;;;       demonstrating that this new list-of-bindings representation satisfies the
;;;       environment specification and integrates correctly with the interpreter.
;;;     - Examples in `run_all_tests.scm` confirm the functionality of the
;;;       interpreter with the modified environment.
;;;   Key Files: `part_1.3_interpreter_list_env.scm`, `part_1.1_interpreter_original.scm`

;;; Part 1.4: Closures and Lexical Scope
;;;   Goal: Research closures and lexical scope, and prove that the TLS
;;;         implementation handles them correctly, including a structural induction.
;;;   Achievement:
;;;     - `part_1.4_closures_lexical_scope.scm` provides a comprehensive explanation
;;;       of lexical scope and closures.
;;;     - It details how TLS implements these concepts, focusing on the `*lambda`
;;;       action (for capturing the definition-time environment) and the
;;;       `apply-closure` procedure (for using this captured environment during
;;;       application).
;;;     - An argument, supported by an illustrative example, demonstrates the
;;;       correctness of lexical scoping in TLS.
;;;     - A structural induction proof for lexical scope correctness was added,
;;;       analyzing each expression type to show that variable lookups adhere to
;;;       lexical rules by ensuring the appropriate environment is used for evaluation.
;;;   Key Files: `part_1.4_closures_lexical_scope.scm` (relies on interpreter logic from 1.1/1.3)

;;; Part 1.5: Correctness of TLS Implementation
;;;   Goal: Identify a standard of correctness for TLS and prove that the
;;;         implementation meets this standard. Include examples of closures and
;;;         first-class functions.
;;;   Achievement:
;;;     - `part_1.5_correctness_of_tls.scm` establishes a standard of correctness:
;;;       the TLS interpreter should semantically align with the evaluation rules
;;;       from "The Little Schemer" for valid TLS programs.
;;;     - A proof of correctness is outlined using structural induction on TLS
;;;       expressions, arguing that the `meaning` function and its helper
;;;       procedures correctly implement the semantics of each language construct.
;;;     - This file was updated to include a section with TLS code examples and
;;;       explanations demonstrating the interpreter's support for closures (functions
;;;       capturing their lexical environment) and first-class functions (passing
;;;       functions as arguments, returning them as results). These examples further
;;;       validate the interpreter's correct implementation of these core features.
;;;   Key Files: `part_1.5_correctness_of_tls.scm`

;;; Part 1.6: Dependence on R5RS
;;;   Goal: Explain the dependence of TLS on the underlying R5RS (DrRacket)
;;;         system, focusing on function call mechanics.
;;;   Achievement:
;;;     - `part_1.6_dependence_on_r5rs.scm` details how the TLS interpreter relies
;;;       on the host R5RS system for:
;;;       - S-expression parsing and data representation (pairs, symbols, etc.).
;;;       - Basic R5RS primitive procedures used in the interpreter's logic.
;;;       - The overall execution model, runtime environment, and memory management
;;;         (including garbage collection).
;;;       - Call stack management for the interpreter's own R5RS functions.
;;;     - A specific analysis is provided on the mechanics of function calling,
;;;       differentiating between how the TLS interpreter simulates calls for its
;;;       own primitives and user-defined lambdas, versus how the R5RS host executes
;;;       the interpreter's R5RS code.
;;;   Key Files: `part_1.6_dependence_on_r5rs.scm`

;;; Part 1.7: Recursion via Y-Combinator (TLS-REC)
;;;   Goal: Equip TLS with recursion using the Y-combinator (Z-combinator for
;;;         applicative order), research Y-combinators, prove its implementation,
;;;         explain its mechanism, and provide examples.
;;;   Achievement:
;;;     - `part_1.7_recursion_y_combinator.scm` explains that the existing TLS
;;;       interpreter inherently supports recursion via the Y-combinator due to its
;;;       correct implementation of lambda and application.
;;;     - Research into fixed-point combinators, the Y-combinator, and the
;;;       applicative-order Z-combinator is presented.
;;;     - The Z-combinator is defined as a TLS expression.
;;;     - A proof is provided showing that this Z-combinator implementation is indeed
;;;       a fixed-point combinator (i.e., `(Z G)` beta-reduces to `(G (Z G))`).
;;;     - A detailed explanation describes how the Z-combinator facilitates recursion
;;;       by "tying the knot" for self-referential function calls.
;;;     - Several examples of recursive programs (Factorial, List Length, Fibonacci,
;;;       Append) are provided in TLS-REC, demonstrating its practical use.
;;;   Key Files: `part_1.7_recursion_y_combinator.scm`

;;;-----------------------------------------------------------------------------
;;; III. Key Components and Shared Resources
;;;-----------------------------------------------------------------------------
;;;
;;; - `shared_definitions.scm`: This crucial file centralizes the definitions of
;;;   TLS primitive procedures (names and arities) and TLS keywords. It is loaded
;;;   by both the interpreter and the syntax checker, ensuring consistency in their
;;;   understanding of the language's basic vocabulary.
;;;
;;; - `run_all_tests.scm`: This file serves as a test harness, loading the various
;;;   components (interpreters, syntax checker) and running a suite of example
;;;   TLS programs. It provides practical demonstration of the implemented features
;;;   and helps verify their correctness.

;;;-----------------------------------------------------------------------------
;;; IV. Synchronization of Interpreter and Syntax Checker
;;;-----------------------------------------------------------------------------
;;;
;;; A key aspect of a robust language implementation is the synchronization between
;;; its analytical components (like the syntax checker) and its execution components
;;; (the interpreter). Both must agree on the language's syntax and semantics,
;;; particularly on fundamental elements like primitive operations and keywords.
;;;
;;; Current Approach:
;;;   Synchronization in this project is primarily achieved through the
;;;   `shared_definitions.scm` file. Both the interpreter and the syntax checker
;;;   load this file, giving them access to the same lists of primitives (with
;;;   arities) and keywords. This ensures, for example, that the syntax checker
;;;   validates arities against the same information the interpreter uses.
;;;
;;; Conceptual Module-Based Enhancement (as discussed in class):
;;;   A more advanced approach to synchronization, would involve a module system. The core TLS language definitions (primitives,
;;;   keywords, perhaps even the evaluator itself) could be encapsulated within a
;;;   "TLS module." This module would then export specific functions or data structures.
;;;
;;;   The syntax checker would then query this TLS module
;;;   dispatcher instead of relying on independently loaded shared files or
;;;   maintaining separate definitions. This would provide a single, authoritative
;;;   source of truth and a clear, controlled interface for accessing language
;;;   definitions, improving maintainability and reducing the risk of inconsistencies.
;;;
;;;   If time allowed we would have definitely looked to implement this approach
;;;   to truly refine our project but sadly we will not be able to.
;;;-----------------------------------------------------------------------------
;;; V. Overall Achievements and Learning
;;;-----------------------------------------------------------------------------
;;;
;;; This project successfully demonstrated the ability to:
;;;   - Implement a functional interpreter for a significant subset of Scheme (TLS)
;;;     in pure R5RS, including features like `let`, lexical scoping, and closures.
;;;   - Develop a rigorous syntax checker that validates TLS programs against an
;;;     inductive definition of the language.
;;;   - Analyze and formally specify components like the environment system, and
;;;     prove the correctness of different implementation strategies for it.
;;;   - Construct formal arguments and proofs for key language properties, notably
;;;     lexical scope and the overall correctness of the interpreter against a
;;;     defined standard.
;;;   - Understand and articulate the dependencies of an embedded interpreter on its
;;;     host language system (R5RS).
;;;   - Extend the language with advanced features like recursion using higher-order
;;;     programming techniques (the Y-combinator/Z-combinator) and prove the
;;;     correctness of such mechanisms.
;;;
;;; The project provided deep insights into the fundamental principles of programming
;;; language interpretation, the importance of formal specification and proof, and
;;; the elegant power of functional programming in practical language design.
;;; The disciplined approach to breaking down the problem
;;; into manageable parts, each with clear objectives and deliverables, was key to
;;; its successful completion.
;;;
;;; 