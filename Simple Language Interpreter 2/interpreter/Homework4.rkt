; Group 5 - Josh Tang, John Mays, Abhay Pant
#lang racket
(require "simpleParser.rkt")

; ==================================================================================================
;                                           ABSTRACTIONS
; ==================================================================================================
; Evaluation abstractions
(define pre_op car)
(define l_operand cadr)
(define r_operand caddr)

; State access abstractions
(define state_vars car)
(define state_vals cadr)

; Variable access abstractions
(define var_name cadr)
(define var_value caddr)

; If-statement & while-loop abstractions
(define condition cadr)
(define stmt1 caddr)
(define elif cdddr)
(define stmt2 cadddr)
(define loop_body cddr)

; Statement list abstractions
(define curr_stmt car)
(define next_stmt cdr)

; Return abstraction
(define ret_val cadr)

; Empty state
(define empty_state '(()()))

; ==================================================================================================
;                                         HELPER FUNCTIONS
; ==================================================================================================

; Checks if an atom is a potential variable name.
(define var?
  (lambda (x)
    (not (or (pair? x) (null? x)))))

; Retrieves the value of a given variable.
; Here, the state takes the form ((var1 var2 var3 ...) (val1 val2 val3 ...))
(define find_var
  (lambda (var state)
    (find_var_helper var (state_vars state) (state_vals state))))

(define find_var_helper
  (lambda (var varlist vallist)
    (cond
      [(null? varlist) (error 'varerror "Variable not declared")]
      [(and (eq? var (car varlist)) (void? (car vallist))) (error 'varerror "Variable not assigned")]
      [(eq? var (car varlist)) (car vallist)]
      [else (find_var_helper var (cdr varlist) (cdr vallist))])))

; Adds a variable to the state and returns the state.
; If the variable already exists in the state, then raise an error.
(define add_var
  (lambda (var val state)
    (if (declared? var (state_vals state))
        (error 'declerror "Variable already declared")
        (cons (cons var (state_vars state)) (cons (cons val (state_vals state)) null)))))

; Checks if a variable has been declared (and is present in the variable list)
(define declared?
  (lambda (var varlist)
    (cond
      [(null? varlist) #f]
      [(eq? var (car varlist)) #t]
      [else (declared? var (cdr varlist))])))

; Removes a variable and its corresponding value from the state, if present.
; Otherwise, the state is unchanged.
(define remove_var
  (lambda (var state)
    (remove_var_helper var (state_vars state) (state_vals state))))

(define remove_var_helper
  (lambda (var varlist vallist)
    (cond
      [(null? varlist) (cons varlist (cons vallist null))]
      [(eq? var (car varlist)) (cons (cdr varlist) (cons (cdr vallist) null))]
      [else (cons (cons (car varlist) (car (remove_var_helper var (cdr varlist) (cdr vallist))))
                  (cons (cons (car vallist) (cadr (remove_var_helper var (cdr varlist) (cdr vallist)))) null))])))


; ==================================================================================================
;                                       EVALUATION FUNCTIONS
; ==================================================================================================

; Evaluates the value of a general expression.
(define M_value
  (lambda (expr state)
    (cond
      [(number? expr) expr]                                                                                       ; Numeric
      [(var? expr) (find_var expr state)]                                                                         ; Variable
      [(eq? (pre_op expr) '+) (+ (M_value (l_operand expr) state) (M_value (r_operand expr) state))]              ; Addition
      [(and (eq? (pre_op expr) '-) (not (null? (cddr expr))))
       (- (M_value (l_operand expr) state) (M_value (r_operand expr) state))]                                     ; Subtraction
      [(eq? (pre_op expr) '-) (- 0 (M_value (l_operand expr) state))]                                             ; Negation
      [(eq? (pre_op expr) '*) (* (M_value (l_operand expr) state) (M_value (r_operand expr) state))]              ; Multiplication
      [(eq? (pre_op expr) '/) (quotient (M_value (l_operand expr) state) (M_value (r_operand expr) state))]       ; Division
      [(eq? (pre_op expr) '%) (remainder (M_value (l_operand expr) state) (M_value (r_operand expr) state))]      ; Modulus
      [else (M_bool expr state)])))

; Evaluates the result of a prefix boolean expression.
(define M_bool
  (lambda (expr state)
    (cond
      [(eq? expr 'true) #t]                                                                                       ; Boolean values
      [(eq? expr 'false) #f]
      [(var? expr) (find_var expr state)]                                                                         ; Variable
      [(eq? (pre_op expr) '!) (not (M_bool (l_operand expr) state))]                                              ; Negation
      [(eq? (pre_op expr) '&&) (and (M_bool (l_operand expr) state) (M_bool(r_operand expr) state))]              ; And
      [(eq? (pre_op expr) '||) (or (M_bool (l_operand expr) state) (M_bool (r_operand expr) state))]              ; Or
      [(eq? (pre_op expr) '==) (eq? (M_value (l_operand expr) state) (M_value (r_operand expr) state))]           ; Equality
      [(eq? (pre_op expr) '!=) (not (eq? (M_value (l_operand expr) state) (M_value (r_operand expr) state)))]     ; Inequality
      [(eq? (pre_op expr) '<) (< (M_value (l_operand expr) state) (M_value (r_operand expr) state))]              ; Less than
      [(eq? (pre_op expr) '<=) (<= (M_value (l_operand expr) state) (M_value (r_operand expr) state))]            ; Less than or equals
      [(eq? (pre_op expr) '>) (> (M_value (l_operand expr) state) (M_value (r_operand expr) state))]              ; Greater than
      [(eq? (pre_op expr) '>=) (>= (M_value (l_operand expr) state) (M_value (r_operand expr) state))]            ; Greater than or equals
      [else (error 'badop "Bad operator")])))


; ==================================================================================================
;                                         STATE FUNCTIONS
; ==================================================================================================

; Returns a state that declares a variable. If a value is specified, then the variable is associated with that value.
; Otherwise, the variable is given the value #<void>.
(define M_declaration
  (lambda (stmt state)
    (if (not (null? (cddr stmt)))
        (add_var (var_name stmt) (M_value (var_value stmt) state) state)
        (add_var (var_name stmt) (void) state))))

; Returns a state that results after the execution of an if statement.
(define M_if
  (lambda (stmt state)
    (if (M_bool (condition stmt) state)
        (M_state (stmt1 stmt) state)
        (if (null? (elif stmt))
            state
            (M_state (stmt2 stmt) state)))))

; Returns a state that results after the execution of a while loop.
(define M_while
  (lambda (stmt state)
    (if (M_bool (condition stmt) state)
        (M_while stmt (M_state (loop_body stmt) state))
        state)))

; Returns the resulting state after a variable is assigned
(define M_assign
  (lambda (stmt state)
    (if (not (declared? (var_name stmt) (state_vars state)))
        (error 'assignerror "Variable not declared")
        (add_var (var_name stmt) (M_value (var_value stmt) state) (remove_var (var_name stmt) state)))))

; Returns the resulting state after a statement or sequence of statements
; A state with a singular value (not an association list) represents the return value of the program
(define M_state
  (lambda (stmts state)
    (cond
      [(or (null? stmts) (not (list? state))) state]
      [(list? (car stmts)) (M_state (next_stmt stmts) (M_state (curr_stmt stmts) state))]
      [(eq? (pre_op stmts) 'return) (M_return stmts state)]
      [(eq? (pre_op stmts) 'var) (M_declaration stmts state)]
      [(eq? (pre_op stmts) '=) (M_assign stmts state)]
      [(eq? (pre_op stmts) 'if) (M_if stmts state)]
      [(eq? (pre_op stmts) 'while) (M_while stmts state)]
      [else (error 'badop "Invalid statement")])))

; Evaluates the return value of the program, replacing instances of #t and #f with 'true and 'false
(define M_return
  (lambda (stmt state)
    (if (number? (M_value (ret_val stmt) state))
        (M_value (ret_val stmt) state)
        (if (M_bool (ret_val stmt) state)
            'true
            'false))))

; ==================================================================================================
;                                                MAIN
; ==================================================================================================
(define interpret
  (lambda (filename)
    (M_state (parser filename) empty_state)))