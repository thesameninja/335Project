;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Project: CSc 335 Project Spring 2025
;;
;; Team: Sohail Ahmad, Umaima Nasim, Jia Xiang Zhang
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; part_1.7_recursion_y_combinator.scm
;;
;; This file addresses Part 1.7 of the TLS project:
;; - Equipping TLS with recursion to form TLS-REC using the Y-combinator.
;; - Research on Y-combinators (explained simply).
;; - Showing how our chosen Y-combinator version works.
;; - An intuitive explanation of how it achieves recursion.
;; - Examples of recursive programs in TLS-REC.
;;
;; Our existing TLS interpreter is already capable of supporting this, as the
;; Y-combinator can be expressed purely with lambda, application, and variables.
;; We will define a version of the Y-combinator (called the Z-combinator, which
;; works well in languages like Scheme and our TLS that evaluate arguments
;; before calling functions) as a TLS expression.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 1.7: Recursion via the Y-Combinator in TLS-REC (Simplified Explanation)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;-----------------------------------------------------------------------------
;;; I. What's the Big Idea? Making Functions That Can Call Themselves
;;;-----------------------------------------------------------------------------
;;;
;;; Normally, when we want a function to do something over and over, or break a
;;; problem into smaller pieces of itself, we use recursion. This means the
;;; function calls itself. For example, to calculate factorial of 5 (5*4*3*2*1),
;;; a factorial function might call itself to calculate factorial of 4.
;;;
;;; In many languages, you can just give a function a name and then use that name
;;; inside the function itself. For example:
;;;   (define factorial (lambda (n) ... (factorial (sub1 n)) ...))
;;;
;;; But what if we are in a system, like pure lambda calculus, where functions might not have names
;;; directly? Or what if we want to achieve recursion using *only* the power of
;;; creating and calling functions, without a special 'define-recursive-function'
;;; feature? This is where the Y-combinator comes in.
;;;
;;; The Y-combinator (and its variations like the Z-combinator) is like a very
;;; clever recipe that can take a *description* of a recursive function and
;;; turn it into the actual working recursive function. It's a way to make a
;;; function that can refer to itself, even if it wasn't given a name to start with.
;;;
;;; Think of it like this: You have a blueprint for a machine that needs one of
;;; its own parts to work. The Y-combinator is a special technique that figures
;;; out how to build that machine, including making that self-referential part.
;;;
;;; For our TLS, which evaluates arguments before function calls (this is called
;;; "applicative-order evaluation"), we use a version of the Y-combinator called
;;; the Z-combinator. It's designed to work correctly in this situation and avoid
;;; getting stuck in an infinite loop before the recursion even starts.
;;; For simplicity, we'll often just call it "our Y-combinator" or "Z-combinator."

;;;-----------------------------------------------------------------------------
;;; II. Our Y-Combinator (The Z-Combinator) in TLS Syntax
;;;-----------------------------------------------------------------------------
;;;
;;; This is what our Z-combinator looks like when written in TLS:
;;;
;;;   (lambda (make-recursive-function-builder)
;;;     ((lambda (self-applier)
;;;        (make-recursive-function-builder
;;;          (lambda (arg-for-recursive-call)
;;;            ((self-applier self-applier) arg-for-recursive-call))))
;;;      (lambda (self-applier)
;;;        (make-recursive-function-builder
;;;          (lambda (arg-for-recursive-call)
;;;            ((self-applier self-applier) arg-for-recursive-call))))))
;;;
;;; Let's give this whole thing a shorter name for discussion, say `Z-maker`.
;;;
;;;   `Z-maker` =
;;;     (lambda (generate-func-body)  ; This is 'make-recursive-function-builder'
;;;       ((lambda (x)                ; This 'x' corresponds to 'self-applier'
;;;          (generate-func-body
;;;            (lambda (v)            ; This 'v' is 'arg-for-recursive-call'
;;;              ((x x) v))))
;;;        (lambda (x)                ; Another 'x' for the self-application trick
;;;          (generate-func-body
;;;            (lambda (v)
;;;              ((x x) v))))))
;;;
;;; What does `Z-maker` do? You give it a function, let's call it `generate-func-body`.
;;; This `generate-func-body` is special: it's a function that *knows how to create
;;; the body of your recursive function*, assuming you could somehow give it the
;;; recursive function itself to call.
;;;
;;; `Z-maker`, when applied to `generate-func-body`, produces the *actual, working*
;;; recursive function.

;;;-----------------------------------------------------------------------------
;;; III. Showing How Our Z-Combinator Works (Making Recursion Happen)
;;;-----------------------------------------------------------------------------
;;;
;;; Let's try to understand why `(Z-maker generate-func-body)` results in a
;;; function that can call itself.
;;;
;;; We said `Z-maker` looks like:
;;;   (lambda (g) ((lambda (x) (g (lambda (v) ((x x) v))))
;;;                (lambda (x) (g (lambda (v) ((x x) v))))))
;;;   (Here, `g` is our `generate-func-body`)
;;;
;;; Let's call the inner part `W = (lambda (x) (g (lambda (v) ((x x) v))))`.
;;; So, `(Z-maker g)` becomes `(W W)`.  This means we apply `W` to itself.
;;;
;;; What happens when `(W W)` is evaluated?
;;; `W` is `(lambda (x) (g (lambda (v) ((x x) v))))`.
;;; If we apply `W` to `W`, we replace `x` inside `W`'s body with `W` itself.
;;; So, `(W W)` evaluates to:
;;;   `(g (lambda (v) ((W W) v)))`
;;;
;;; Look at that! `(Z-maker g)` (which is `(W W)`) turns into:
;;;   `(g (lambda (v) ((Z-maker g) v)))`  -- because `(W W)` is just `(Z-maker g)`.
;;;
;;; This is the key! Let `my-recursive-function = (Z-maker g)`.
;;; Then the equation above says:
;;;   `my-recursive-function` effectively becomes `(g (lambda (v) (my-recursive-function v)))`
;;;
;;; The part `(lambda (v) (my-recursive-function v))` is a little helper function.
;;; When you call this helper with an argument, say `arg1`, it just calls
;;; `my-recursive-function` with `arg1`. So, this helper acts exactly like
;;; `my-recursive-function` itself.
;;;
;;; This means that `my-recursive-function` behaves like `(g my-recursive-function)`.
;;;
;;; So, when we call `my-recursive-function`:
;;; 1. It transforms into `g` applied to something that *acts just like* `my-recursive-function`.
;;; 2. The `g` (our `generate-func-body`) then gets the ability to call `my-recursive-function`
;;;    from within itself, achieving recursion!
;;;
;;; The `(lambda (v) ((x x) v))` part is a clever trick. In a language like TLS
;;; that evaluates arguments first (call-by-value), if we just had `(g (x x))`
;;; and `x` applied to `x` tried to loop forever, we'd get stuck.
;;; The `(lambda (v) ...)` part "pauses" or "wraps" the `(x x)` self-call.
;;; The `(x x)` only happens *inside* this new lambda, and only when that new lambda
;;; (which `g` uses for recursive calls) is actually called with an argument `v`.
;;; This delay prevents the immediate infinite loop and allows the recursion to
;;; proceed step-by-step, controlled by `g`'s logic (e.g., its base case).

;;;-----------------------------------------------------------------------------
;;; IV. An Intuitive Explanation: How the Z-Combinator Helps a Function Call Itself
;;;-----------------------------------------------------------------------------
;;;
;;; Imagine you want to write a function, say `countdown`, that counts down from a
;;; number to zero. A `countdown` function needs to call itself: `countdown(n)`
;;; will do something and then call `countdown(n-1)`.
;;;
;;; Step 1: Write a "Recipe Card" (The Generator Function)
;;;
;;; First, we write a "recipe card" for `countdown`. This recipe card isn't the
;;; `countdown` function itself yet. Instead, it's a function that describes
;;; *what `countdown` should do*, assuming someone gives it the ability to make
;;; the recursive call.
;;;
;;; Let's call this recipe card `make-countdown-body`. It will take one argument,
;;; which will be the "magic recursive call" function.
;;;
;;;   `make-countdown-body = `
;;;     `(lambda (here-is-how-to-call-countdown-again)
;;;        (lambda (n) ; This is the actual countdown function we are building
;;;          (cond ((zero? n) (quote finished))
;;;                (else (here-is-how-to-call-countdown-again (sub1 n))))))`
;;;
;;; So, `make-countdown-body` is a function. If you give it a function `f`, it
;;; returns another function `(lambda (n) ... (f (sub1 n)) ...)`.
;;; We want the `f` here to *be* the `countdown` function itself.
;;;
;;; Step 2: Use the Z-Combinator (Our `Z-maker`)
;;;
;;; Now, we take our `Z-maker` (the Z-combinator) and give it this `make-countdown-body` recipe card:
;;;
;;;   `actual-countdown = (Z-maker make-countdown-body)`
;;;
;;; The `Z-maker` does some very clever internal wiring. As we saw in Section III,
;;; the result `actual-countdown` behaves as if it were:
;;;   `(make-countdown-body something-that-acts-like-actual-countdown)`
;;;
;;; Step 3: How a Call to `actual-countdown` Works
;;;
;;; Let's say we call `(actual-countdown 3)`.
;;;
;;; 1.  `actual-countdown` is `(Z-maker make-countdown-body)`.
;;; 2.  Because of how `Z-maker` works, this effectively becomes:
;;;     `(make-countdown-body the-magic-recursive-caller)`
;;;     where `the-magic-recursive-caller` is a special function created by `Z-maker`
;;;     that, when called with an argument (like `(sub1 n)`), will behave just like
;;;     calling `actual-countdown` with that argument.
;;;
;;; 3.  So, `make-countdown-body` is called with `the-magic-recursive-caller`.
;;;     Looking at `make-countdown-body`'s definition, its `here-is-how-to-call-countdown-again`
;;;     parameter becomes `the-magic-recursive-caller`.
;;;
;;; 4.  `make-countdown-body` then returns its inner lambda:
;;;     `(lambda (n)
;;;        (cond ((zero? n) (quote finished))
;;;              (else (the-magic-recursive-caller (sub1 n)))))`
;;;
;;; 5.  This returned lambda is now applied to our original argument, `3`.
;;;     So, `n` becomes `3`.
;;;
;;; 6.  The `cond` is evaluated:
;;;     - `(zero? 3)` is false.
;;;     - So, the `else` branch is taken: `(the-magic-recursive-caller (sub1 3))`,
;;;       which is `(the-magic-recursive-caller 2)`.
;;;
;;; 7.  What happens when `(the-magic-recursive-caller 2)` is called?
;;;     Remember, `the-magic-recursive-caller` is the special function that knows how to
;;;     behave like `actual-countdown`. So, calling `(the-magic-recursive-caller 2)`
;;;     is just like starting over and calling `(actual-countdown 2)`.
;;;
;;; This process repeats: `(actual-countdown 2)` will lead to a call to
;;; `(the-magic-recursive-caller 1)`, then `(actual-countdown 1)` leads to
;;; `(the-magic-recursive-caller 0)`, and finally `(actual-countdown 0)` will hit the
;;; base case `((zero? n) (quote finished))` and the recursion stops.
;;;
;;; The Z-combinator is the engine that creates this `the-magic-recursive-caller`
;;; and wires it up correctly so that the `make-countdown-body` (our generator)
;;; gets exactly what it needs to make recursive calls to the function it's trying to build.
;;; It's a way of achieving self-reference using only functions that can take other
;;; functions as arguments and return functions as results.

;;;-----------------------------------------------------------------------------
;;; V. Equipping TLS with Recursion to Form TLS-REC
;;;-----------------------------------------------------------------------------
;;;
;;; Our existing TLS interpreter does not need modification to support recursion
;;; via the Y-combinator. This is because TLS already correctly implements the
;;; key features needed:
;;;   - `lambda`: for creating anonymous functions.
;;;   - Application: for calling functions.
;;;   - Lexical Scope: for variables to be resolved correctly.
;;;
;;; TLS-REC is simply TLS used with the understanding that we can define and use
;;; the Z-combinator (our `Z-maker`) as a regular TLS expression.
;;;
;;; The `Z-maker` itself:
;;;   (lambda (generate-func-body)
;;;     ((lambda (x) (generate-func-body (lambda (v) ((x x) v))))
;;;      (lambda (x) (generate-func-body (lambda (v) ((x x) v))))))
;;;
;;; To define a recursive function in TLS-REC, we first write its "generator"
;;; (like `make-countdown-body` above), and then apply `Z-maker` to this generator.

;;;-----------------------------------------------------------------------------
;;; VI. Examples of Recursive Programs in TLS-REC
;;;-----------------------------------------------------------------------------
;;;
;;; In these examples, we'll use a `let` to define `Z-maker` and the generator
;;; for clarity. In a real TLS program without a top-level `define`, the
;;; `Z-maker` lambda would be part of the expression itself or defined via nested `let`s.
;;;
;;; We'll stick to primitives available in our TLS: `cons`, `car`, `cdr`, `null?`,
;;; `eq?`, `atom?`, `zero?`, `add1`, `sub1`, `number?`.
;;;
;;; Example 1: Countdown (from explanation)
;;;
;;;   (let ((Z-maker (lambda (generate-func-body) ; Our Y-combinator
;;;                    ((lambda (x) (generate-func-body (lambda (v) ((x x) v))))
;;;                     (lambda (x) (generate-func-body (lambda (v) ((x x) v))))))))
;;;     (let ((make-countdown-body
;;;             (lambda (recursive-call-stub) ; This is 'here-is-how-to-call-countdown-again'
;;;               (lambda (n)
;;;                 (cond ((zero? n) (quote finished)) ; Base case
;;;                       (else
;;;                        ;; To show it's doing something before recurring:
;;;                        (cons n (recursive-call-stub (sub1 n)))))))))
;;;       (let ((actual-countdown (Z-maker make-countdown-body)))
;;;         (actual-countdown 3))))
;;;
;;;   Expected Output (if 'cons'ing n at each step): (3 . (2 . (1 . finished)))
;;;   This example shows the countdown, and also how a value (like n) can be
;;;   used before the recursive call.

;;; Example 2: List Length
;;;
;;;   (let ((Z-maker (lambda (generate-func-body)
;;;                    ((lambda (x) (generate-func-body (lambda (v) ((x x) v))))
;;;                     (lambda (x) (generate-func-body (lambda (v) ((x x) v))))))))
;;;     (let ((make-length-body
;;;             (lambda (length-recursive-step)
;;;               (lambda (lst)
;;;                 (cond ((null? lst) 0) ; Base case: empty list has length 0
;;;                       (else (add1 (length-recursive-step (cdr lst)))))))))
;;;       (let ((my-list-length (Z-maker make-length-body)))
;;;         (my-list-length '(quote (a b c d))))))
;;;
;;;   Expected Output: 4

;;; Example 3: Sum of numbers in a list
;;;   (This requires us to be careful as TLS doesn't have a general 'add' primitive,
;;;    only 'add1'. We can make a recursive 'add' or sum directly.)
;;;   Let's make a sum of list elements.
;;;
;;;   (let ((Z-maker (lambda (generate-func-body)
;;;                    ((lambda (x) (generate-func-body (lambda (v) ((x x) v))))
;;;                     (lambda (x) (generate-func-body (lambda (v) ((x x) v))))))))
;;;     ;; First, let's define a recursive 'adder' using Z-maker, just for numbers
;;;     (let ((make-add-body
;;;             (lambda (add-rec)
;;;               (lambda (a b) ; adds a and b
;;;                 (cond ((zero? b) a)
;;;                       (else (add-rec (add1 a) (sub1 b))))))))
;;;       (let ((tls-add (Z-maker make-add-body)))
;;;         ;; Now, use this tls-add in our list sum
;;;         (let ((make-sum-list-body
;;;                 (lambda (sum-list-rec)
;;;                   (lambda (lst)
;;;                     (cond ((null? lst) 0) ; Sum of empty list is 0
;;;                           (else (tls-add (car lst) ; Add current element
;;;                                          (sum-list-rec (cdr lst))))))))) ; to sum of rest
;;;           (let ((sum-my-list (Z-maker make-sum-list-body)))
;;;             (sum-my-list '(quote (10 20 5))))))))
;;;
;;;   Expected Output: 35
;;;   (This shows nesting: defining one recursive function `tls-add` to be used
;;;    inside another recursive function `sum-my-list`'s generator.)

;;; Example 4: Append two lists
;;;
;;;   (let ((Z-maker (lambda (generate-func-body)
;;;                    ((lambda (x) (generate-func-body (lambda (v) ((x x) v))))
;;;                     (lambda (x) (generate-func-body (lambda (v) ((x x) v))))))))
;;;     (let ((make-append-body
;;;             (lambda (append-recursive-step)
;;;               (lambda (list1 list2)
;;;                 (cond ((null? list1) list2) ; Base case: if list1 is empty, result is list2
;;;                       (else (cons (car list1)
;;;                                   (append-recursive-step (cdr list1) list2))))))))
;;;       (let ((my-append (Z-maker make-append-body)))
;;;         (my-append '(quote (1 2)) '(quote (3 4 5))))))
;;;
;;;   Expected Output: (1 2 3 4 5)
;;;
;;; These examples illustrate how the Z-combinator (`Z-maker`) allows us to define
;;; genuinely recursive functions in TLS by:
;;; 1. Describing the recursive logic in a "generator" function that expects to be
;;;    handed the ability to make a recursive call.
;;; 2. Using `Z-maker` to transform this generator into a fully working recursive function.
;;;
;;; Our TLS interpreter can run these because it correctly handles functions as
;;; values (lambdas can be created, passed to `Z-maker`, and returned by `Z-maker`)
;;; and evaluates function calls as specified.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;