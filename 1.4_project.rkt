; 1.4 Closures and Lexical Scope


; Lexical Scoping (Static Scoping)
; Definition:
; In Lexical Scoping, variables are resolved in a program based on the static (lexical) structure of the code
; This means that a variable reference is resolved by looking up the nearest enclosing environment at the point where the
; function is defined, and not where it's called. In other words, where a variable is defined in the source code determines
; what value it holds, regardless of where the functin is called.
;
; When a function is defined, it captures the environment (variable bindings) surrounding its definition.
; Later when a function is called, variable lookups for non-local variables refer to that captured environment, not the
; environment at the call site.
;
; ex 1)
(define x 10)
(define (add-to-x y) (+ x y)) ;'x' still resolves to 10

(let ((x 20))
  (add-to-x 5)) ; return 15 not 25
;
; ex 2)
(define x 10)
(define (make-multiplier factor)
  (lambda (n) (* factor n))) ; 'factor' is captured

(define times-3 (make-multiplier 3))
(define times-5 (make-multiplier 5))

(times-3 4) ;returns 12 using factor = 3
(times-5 4) ;returns 20 using factor = 5
; We see that times-3 and times-5 are called later but they remember the factor value from when they were created
;
; Importance:
; Lexical scope ensures predictability, which means variables don't change based on where functions are invoked


; Closures
; Definition:
; A closure is a function bundled with its defining environment. The combination allows the function to "remember" variable
; bindings even when it is executed outside its original lexical scope.
; A closure is a data structure that pairs a function (its code) and its defining environment (variable bindings when function
; was created)
; A closure is often shown as: Closure = (expression, definition)
;
; ex)
(define (make-adder x)
  (lambda (y) (+ x y)))

(define add-3 (make-adder 3))
(add-3 5) ;returns 8
; add-3 is a closure where x is bound to 3
;
; Importance:
; The function add-3 would not work correctly without closures because they wouldn't retain their captured environment
