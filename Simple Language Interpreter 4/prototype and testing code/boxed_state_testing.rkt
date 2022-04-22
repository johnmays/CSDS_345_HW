#lang racket

; EVERYTHING IN THIS DOCUMENT SHOULD NOW BE FITTED FOR A BOXED STATE - John

; State access abstractions
(define state_vars car)
(define state_vals cadr)

(define find_var
  (lambda (var state)
    (find_var_helper var (state_vars state) (state_vals state))))

(define find_var_helper
  (lambda (var varlist vallist)
    (cond
      [(null? varlist) (error 'varerror "Variable not declared")]
      [(and (eq? var (car varlist)) (void? (car vallist))) (error 'varerror "Variable not assigned")]
      [(eq? var (car varlist)) (unbox (car vallist))]
      [else (find_var_helper var (cdr varlist) (cdr vallist))])))

; Checks if a variable has been declared (and is present in the variable list)
(define declared?
  (lambda (var varlist)
    (cond
      [(null? varlist) #f]
      [(eq? var (car varlist)) #t]
      [else (declared? var (cdr varlist))])))

; Adds a variable to the state and returns the state.
; If the variable already exists in the state, then raise an error.
(define add_var
  (lambda (var val state)
    (if (declared? var (state_vals state))
        (error 'declerror "Variable already declared")
        (cons (cons var (state_vars state)) (cons (cons (box val) (state_vals state)) null)))))

(define s '(()()))