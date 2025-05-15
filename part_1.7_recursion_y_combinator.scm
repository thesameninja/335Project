;; part_1.7_recursion_y_combinator.scm
;;
;; This file addresses Part 1.7 of the TLS project:
;; - Equipping TLS with recursion to form TLS-REC using the Y-combinator.
;; - Research on Y-combinators.
;; - Proof that the implementation used is a Y-combinator.
;; - Explanation of how the Y-combinator implements recursion.
;; - Examples of recursive programs in TLS-REC.
;;
;; Our existing TLS interpreter (from part_1.1 or part_1.3) is already
;; capable of supporting this, as the Y-combinator can be expressed purely
;; with lambda, application, and variables. We will define the Y-combinator
;; (specifically the Z-combinator, suitable for applicative-order evaluation)
;; as a TLS expression.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 1.7: Recursion via the Y-Combinator in TLS-REC
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;-----------------------------------------------------------------------------
;;; I. Research on Y-Combinators and Fixed-Point Combinators
;;;-----------------------------------------------------------------------------
;;;
;;; A. What is a Fixed-Point Combinator?
;;;
;;; In mathematics and computer science (specifically lambda calculus), a
;;; fixed-point combinator is a higher-order function `Y` that, for any given
;;; function `g`, finds a "fixed point" of `g`. A fixed point `x` of a function `g`
;;; is a value such that `g(x) = x`.
;;;
;;; So, a fixed-point combinator `Y` satisfies the property:
;;;   `Y g = g (Y g)`
;;;
;;; This means `(Y g)` is a fixed point of `g`.
;;;
;;; B. The Y-Combinator and Recursion:
;;;
;;; The Y-combinator is a specific implementation of a fixed-point combinator,
;;; famously discovered by Haskell Curry. Its significance lies in its ability to
;;; enable recursion in languages that only have anonymous functions (like pure
;;; lambda calculus) without built-in recursive definition mechanisms (like `letrec`
;;; or `define` that allows self-reference in the definition).
;;;
;;; How it enables recursion:
;;; Suppose we want to define a recursive function `f` that has a body involving
;;; calls to `f` itself. For example, factorial: `fact(n) = if n=0 then 1 else n * fact(n-1)`.
;;; We can rewrite this by abstracting out the recursive call. Define a
;;; higher-order function `G` (often called the "generator" or "functional")
;;; such that `fact` would be `G(fact)`.
;;;   `G = lambda self_fact. (lambda n. (if (zero? n) 1 (mult n (self_fact (sub1 n)))))`
;;; (Using TLS-like syntax with `mult` for illustration).
;;;
;;; We are looking for a function `fact` such that `fact = G(fact)`. This means `fact`
;;; is a fixed point of `G`. The Y-combinator finds such a fixed point:
;;;   `fact = Y G`
;;;
;;; Since `Y G = G (Y G)`, substituting `fact` for `Y G`, we get `fact = G (fact)`.
;;; When `fact` (which is `Y G`) is called, `(Y G)` effectively becomes `G (Y G)`,
;;; meaning `G` gets `Y G` (i.e., `fact` itself) as its `self_fact` argument,
;;; allowing the recursion to proceed.
;;;
;;; C. Applicative-Order Y-Combinator (Z-Combinator):
;;;
;;; The classic Y-combinator: `Y = (lambda (f) ((lambda (x) (f (x x))) (lambda (x) (f (x x)))))`
;;; has an issue in call-by-value (applicative-order) languages like Scheme (and our
;;; TLS interpreter, which evaluates arguments before application). The sub-expression
;;; `(x x)` would be evaluated, and if `x` is `(lambda (x) (f (x x)))`, then `(x x)`
;;; would lead to `(f ((lambda (x) (f (x x))) (lambda (x) (f (x x)))))`, which expands
;;; indefinitely without `f` ever being called with its actual arguments.
;;;
;;; To solve this in call-by-value systems, the Z-combinator is used. It's an
;;; eta-expanded version of the Y-combinator that delays the problematic self-application:
;;;   `Z = (lambda (f)
;;;          ((lambda (x)
;;;             (f (lambda (v) ((x x) v)))) ; Delays self-application via an extra lambda
;;;           (lambda (x)
;;;             (f (lambda (v) ((x x) v))))))`
;;;
;;; This `Z` combinator satisfies `Z G = G (Z G)` in a call-by-value setting and is
;;; what we will implement and use in TLS-REC. For simplicity, we will often refer
;;; to it as "the Y-combinator" or just "Y" in the context of TLS-REC, acknowledging
;;; it's the applicative-order version.

;;;-----------------------------------------------------------------------------
;;; II. The Y-Combinator (Z-Combinator) in TLS-LET Syntax
;;;-----------------------------------------------------------------------------
;;;
;;; We define `YMake` which is a function that takes a generator `f` (like `G` above)
;;; and returns the recursive function. This `YMake` is our Z-combinator.
;;;
;;; (define YMake
;;;   (lambda (le) ; le (lambda expression generator) is 'f' in Z notation
;;;     ((lambda (f) ; f here is the self-application part 'x' in Z
;;;        (le (lambda (arg) ((f f) arg)))) ; This is 'le (lambda (v) ((x x) v))'
;;;      (lambda (f) ; f here is also 'x'
;;;        (le (lambda (arg) ((f f) arg)))))))
;;;
;;; In a more direct translation of the Z-combinator structure shown above:
;;;
;;; (define Z-combinator
;;;   (lambda (generator) ; 'generator' is 'f' in the Z-combinator formula `Z f = ...`
;;;     ((lambda (x)
;;;        (generator (lambda (v) ((x x) v))))
;;;      (lambda (x)
;;;        (generator (lambda (v) ((x x) v)))))))
;;;
;;; We will use this `Z-combinator` definition.
;;; A TLS-REC program would typically first define this `Z-combinator` (or have it
;;; predefined) and then use it to define recursive functions.

;;;-----------------------------------------------------------------------------
;;; III. Proof that the Implemented Z-Combinator is a Fixed-Point Combinator
;;;-----------------------------------------------------------------------------
;;;
;;; We need to show that for any function (generator) `G`, `(Z-combinator G)` is a
;;; fixed point of `G`. That is, `(Z-combinator G) = (G (Z-combinator G))`.
;;;
;;; Let `Z = (lambda (g) ((lambda (x) (g (lambda (v) ((x x) v))))
;;;                       (lambda (x) (g (lambda (v) ((x x) v))))))`
;;;
;;; Let `W = (lambda (x) (g (lambda (v) ((x x) v))))`.
;;; Then `Z g = (W W)`.
;;;
;;; We want to show `(Z g) beta-reduces-to (g (Z g))`.
;;; (Using beta-reduction informally here, as TLS evaluation mimics it).
;;;
;;; Consider the evaluation of `(Z g)`:
;;; `(Z g)`
;;;  => `((lambda (x) (g (lambda (v) ((x x) v)))) W)`  (by substituting W for the second lambda(x)...)
;;;  => `(g (lambda (v) ((W W) v)))`                   (by beta-reducing, substituting W for x)
;;;
;;; We know that `(W W)` is definitionally equivalent to `(Z g)`.
;;; So, `(g (lambda (v) ((W W) v)))` is equivalent to `(g (lambda (v) ((Z g) v)))`.
;;;
;;; Now, if `(Z g)` is a function, then `(lambda (v) ((Z g) v))` is eta-equivalent
;;; to `(Z g)` itself, assuming `v` is not free in `(Z g)`.
;;; (Eta-reduction: `(lambda (z) (M z)) == M`, if `z` is not free in `M`).
;;;
;;; So, `(Z g) => (g (Z g))` (after eta-reduction of the inner part).
;;;
;;; This demonstrates that `(Z g)` evaluates to an expression that, when applied,
;;; behaves as if `g` is applied to `(Z g)`. The thunk `(lambda (v) ((W W) v))`
;;; is crucial for call-by-value: it ensures that `(W W)` (which is `(Z g)`)
;;; is not evaluated until the resulting function is actually called with an argument `v`.
;;;
;;; Thus, `Z` correctly finds a fixed point for `g` in an applicative-order setting.
;;; The expression `(Z g)` represents the recursive function. When called, it expands
;;; to `(g (Z g)) applied-to-args`, effectively passing the recursive function itself
;;; (as `(Z g)`) to the generator `g`.

;;;-----------------------------------------------------------------------------
;;; IV. How the Y-Combinator (Z-Combinator) Implements Recursion in Detail
;;;-----------------------------------------------------------------------------
;;;
;;; Recursion means a function calls itself. In a language without direct support
;;; for self-referential definitions (like `define fact ... fact ...`), we need
;;; a way to "tie the knot."
;;;
;;; 1. The Generator Function (`G`):
;;;    First, we write the recursive function's body as if the function itself
;;;    were an input parameter. This is the generator `G`.
;;;    Example: Factorial generator `FactG`
;;;    `(define FactG
;;;       (lambda (self-fact) ; `self-fact` is where the recursive call will go
;;;         (lambda (n)
;;;           (cond ((zero? n) 1)
;;;                 (else (mul n (self-fact (sub1 n))))))))`
;;;    (Assuming a `mul` primitive for multiplication in TLS for this example.
;;;     If not, factorial would need to be implemented differently, e.g., via repeated addition).
;;;    `FactG` takes a function `self-fact` and returns the actual factorial function
;;;    that uses `self-fact` for the recursive step.
;;;
;;; 2. Finding the Fixed Point:
;;;    We want a function `fact` such that `fact = (FactG fact)`.
;;;    The Z-combinator, when applied to `FactG`, gives us this `fact`:
;;;    `(define fact (Z-combinator FactG))`
;;;
;;; 3. The "Magic" of `(Z G)`:
;;;    From the proof in section III, we know `(Z G)` evaluates to something that
;;;    behaves like `(G (Z G))`.
;;;    Let `fact = (Z G)`.
;;;    So, when `fact` is called, say `(fact 5)`, it's like calling `((G (Z G)) 5)`.
;;;
;;;    Let's trace `(fact n)` which is `((Z-combinator FactG) n)`:
;;;    a. `(Z-combinator FactG)` is evaluated.
;;;       Let `W_factg = (lambda (x) (FactG (lambda (v) ((x x) v))))`.
;;;       Then `(Z-combinator FactG)` becomes `(W_factg W_factg)`.
;;;       This expression `(W_factg W_factg)` IS our `fact` function. Let's call this value `ActualFactFunction`.
;;;
;;;    b. Now we call `(ActualFactFunction n)`.
;;;       This is `((W_factg W_factg) n)`.
;;;       This doesn't evaluate directly. Remember, `W_factg` expects an argument `x` (which is `W_factg` itself).
;;;       The structure `(lambda (v) ((x x) v))` is key.
;;;       When `(Z-combinator FactG)` was first created, it returned what `(W_factg W_factg)` evaluates to.
;;;       `(W_factg W_factg)` means apply `W_factg` to `W_factg`.
;;;       So, `x` inside `W_factg` becomes `W_factg`.
;;;       The expression becomes: `(FactG (lambda (v) ((W_factg W_factg) v)))`.
;;;
;;;       Let `RecursiveThunk = (lambda (v) ((W_factg W_factg) v))`.
;;;       So, `(Z-combinator FactG)` effectively evaluates to `(FactG RecursiveThunk)`.
;;;
;;;    c. So, `(fact n)` is `((FactG RecursiveThunk) n)`.
;;;       - `FactG` is called with `RecursiveThunk` as its `self-fact` argument.
;;;       - `FactG` returns its inner lambda:
;;;         `(lambda (n) (cond ((zero? n) 1) (else (mul n (RecursiveThunk (sub1 n))))))`
;;;       - This returned lambda is then applied to the original argument `n`.
;;;
;;;    d. Inside the body, if a recursive call `(self-fact (sub1 n))` happens, it's actually
;;;       `(RecursiveThunk (sub1 n))`.
;;;
;;;    e. What is `(RecursiveThunk (sub1 n))`?
;;;       It's `((lambda (v) ((W_factg W_factg) v)) (sub1 n))`.
;;;       This applies the thunk: `v` becomes `(sub1 n)`.
;;;       The result is `((W_factg W_factg) (sub1 n))`.
;;;       But `(W_factg W_factg)` is `ActualFactFunction` (our `fact`)!
;;;       So, `(RecursiveThunk (sub1 n))` is equivalent to `(fact (sub1 n))`.
;;;
;;;    Summary of the mechanism:
;;;    - `(Z G)` produces a function, let's call it `REC_G`.
;;;    - When `REC_G` is called with an argument `arg`, it behaves as if `(G some_magic_function)`
;;;      is called with `arg`.
;;;    - This `some_magic_function`, when called with an argument `v`, turns back into
;;;      `(REC_G v)`.
;;;    - So, `G` receives a function that, when called, is equivalent to calling `REC_G` again.
;;;      This "ties the knot" and provides the self-reference needed for recursion.
;;;    The intermediate `lambda (v) ...` (the "thunk") is crucial in call-by-value
;;;    to prevent the recursive expansion from happening infinitely *before* `G` gets
;;;    a chance to execute its base case logic. It delays the self-application `(x x)`
;;;    until the resulting function is actually applied to an argument.

;;;-----------------------------------------------------------------------------
;;; V. Equipping TLS with Recursion to Form TLS-REC
;;;-----------------------------------------------------------------------------
;;;
;;; Our existing TLS interpreter (Part 1.1 or 1.3) does not need modification to
;;; support recursion via the Y-combinator because it already correctly implements
;;; lambda, application, and lexical scope. TLS-REC is thus TLS used with the
;;; Y-combinator (specifically Z-combinator for our applicative order evaluation).
;;;
;;; We define the Z-combinator as a TLS-LET expression:
;;;
;;; (define Zcombinator
;;;   (lambda (generator)
;;;     ((lambda (x)
;;;        (generator (lambda (v) ((x x) v))))
;;;      (lambda (x)
;;;        (generator (lambda (v) ((x x) v)))))))
;;;
;;; Recursive functions are then defined by applying Zcombinator to their generator.

;;;-----------------------------------------------------------------------------
;;; VI. Examples of Recursive Programs in TLS-REC
;;;-----------------------------------------------------------------------------
;;;
;;; Note: For these examples to run directly, our TLS would need a `define`
;;;       special form or we'd have to use nested `let` or immediately-invoked
;;;       lambda expressions to bind `Zcombinator` and the recursive functions.
;;;       Alternatively, `Zcombinator` can be part of the expression itself.
;;;       For simplicity of presentation, we'll show them as if `define` exists at
;;;       the top level of a TLS program, or assume these are parts of a larger `let`.
;;;
;;;       Also, these examples might use primitives like `mul` (multiplication) or
;;;       `equal?` for general equality if needed, which are not in our base TLS primitive set.
;;;       We'll try to stick to available primitives or show how to build up.
;;;
;;; Example 1: Factorial
;;; (Requires `mul` and a more general number equality, or a `>` for cond)
;;; Let's implement factorial using only `add1`, `sub1`, `zero?`, and `cons`/`car`/`cdr`
;;; for representing numbers if needed, or assume `mul` is somehow available.
;;; Assuming `mul` for now for clarity of the recursive structure.
;;;
;;; (let ((Z (lambda (g) ; Z-combinator definition
;;;            ((lambda (x) (g (lambda (v) ((x x) v))))
;;;             (lambda (x) (g (lambda (v) ((x x) v))))))))
;;;   (let ((FactG (lambda (fact) ; Factorial Generator
;;;                  (lambda (n)
;;;                    (cond ((zero? n) 1)
;;;                          (else (mul n (fact (sub1 n))))))))) ; Assume 'mul' primitive
;;;     (let ((factorial (Z FactG)))
;;;       (factorial 5)))) ; Expected: 120 (if 'mul' is present)
;;;
;;; Example 1b: Factorial using only TLS primitives (more complex for product)
;;; To implement `mul` itself recursively or iteratively within TLS is possible but lengthy.
;;; For now, we'll focus on the recursive structure that Y enables.
;;; The example from `part_1.1_interpreter_original.scm` for countdown is similar:
;;;
;;; (let ((Z (lambda (g)
;;;            ((lambda (x) (g (lambda (v) ((x x) v))))
;;;             (lambda (x) (g (lambda (v) ((x x) v))))))))
;;;   (let ((CountdownG (lambda (countdown-rec)
;;;                       (lambda (k)
;;;                         (cond ((zero? k) 0)
;;;                               (else (add1 (countdown-rec (sub1 k)))))))))
;;;     (let ((actual-countdown (Z CountdownG)))
;;;       (actual-countdown 5)))) ; Expected: 5 (counts add1 calls)
;;;
;;;
;;; Example 2: List Length
;;;
;;; (let ((Z (lambda (g)
;;;            ((lambda (x) (g (lambda (v) ((x x) v))))
;;;             (lambda (x) (g (lambda (v) ((x x) v))))))))
;;;   (let ((LengthG (lambda (length-rec)
;;;                    (lambda (lst)
;;;                      (cond ((null? lst) 0)
;;;                            (else (add1 (length-rec (cdr lst)))))))))
;;;     (let ((my-length (Z LengthG)))
;;;       (my-length '(quote (a b c d e)))))) ; Expected: 5
;;;
;;;
;;; Example 3: Fibonacci Numbers
;;; (Requires `sub1`, `sub2` (or repeated `sub1`), `add` (or repeated `add1`), `equal?`)
;;; Assuming `add` and `equal?` for simplicity of expressing Fibonacci.
;;;
;;; (let ((Z (lambda (g) ((lambda (x) (g (lambda (v) ((x x) v))))
;;;                       (lambda (x) (g (lambda (v) ((x x) v)))))))
;;;       (sub2 (lambda (n) (sub1 (sub1 n))))) ; Define sub2 if not primitive
;;;   (let ((FibG (lambda (fib-rec)
;;;                 (lambda (n)
;;;                   (cond ((zero? n) 0)
;;;                         ((eq? n 1) 1) ; Assume 'eq?' works for numbers here for simplicity
;;;                         (else (add (fib-rec (sub1 n)) ; Assume 'add' primitive
;;;                                    (fib-rec (sub2 n)))))))))
;;;     (let ((fibonacci (Z FibG)))
;;;       (fibonacci 6)))) ; Expected: 8 (0,1,1,2,3,5,8)
;;;
;;;
;;; Example 4: Append two lists
;;;
;;; (let ((Z (lambda (g)
;;;            ((lambda (x) (g (lambda (v) ((x x) v))))
;;;             (lambda (x) (g (lambda (v) ((x x) v))))))))
;;;   (let ((AppendG (lambda (append-rec)
;;;                    (lambda (list1 list2)
;;;                      (cond ((null? list1) list2)
;;;                            (else (cons (car list1)
;;;                                        (append-rec (cdr list1) list2))))))))
;;;     (let ((my-append (Z AppendG)))
;;;       (my-append '(quote (1 2)) '(quote (3 4)))))) ; Expected: (1 2 3 4)
;;;
;;;
;;; These examples show how a recursive process can be defined by:
;;; 1. Writing a "generator" function that takes the recursive function itself as an argument.
;;; 2. Applying the Z-combinator to this generator to get the actual recursive function.
;;; 3. Calling the resulting recursive function.
;;; The TLS interpreter, with its support for first-class lambdas and lexical scope,
;;; can execute these Z-combinator based recursive definitions correctly.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;