; Group 5 - Josh Tang, John Mays, Abhay Pant
#lang racket
(require "simpleParser.rkt")

; ==================================================================================================
;                                           ABSTRACTIONS
; ==================================================================================================
(define pre_op car)
(define l_operand cadr)
(define r_operand caddr)

(define state_vars car)
(define state_vals cadr)

(define var_name cadr)
(define var_value caddr)

(define condition cadr)
(define stmt1 cddr)
(define stmt2 cdddr)

(define loop_body cddr)

(define curr_stmt car)
(define next_stmt cdr)

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
      [(null? varlist) (error 'initerror "Variable not initialized")]
      [(eq? var (car varlist)) (car vallist)]
      [else (find_var_helper var (cdr varlist) (cdr vallist))])))

; Adds a variable to the state and returns the state.
; If the variable already exists in the state, then raise an error.
(define add_var
  (lambda (var val state)
    (if (inlist? var (car state))
        (error 'declerror "Variable already declared")
        (cons (cons var (state_vars state)) (cons (cons val (state_vals state)) null)))))

(define inlist?
  (lambda (var varlist)
    (cond
      [(null? varlist) #f]
      [(eq? var (car varlist)) #t]
      [else (inlist? var (cdr varlist))])))

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

; Evaluates the value of an prefix mathematical expression.
(define M_value
  (lambda (expr state)
    (cond
      [(number? expr) expr]                                                                                   ; Numeric
      [(var? expr) (find_var expr state)]                                                                     ; Variable
      [(eq? (pre_op expr) '+) (+ (M_value (l_operand expr) state) (M_value (r_operand expr) state))]          ; Addition
      [(and (eq? (pre_op expr) '-) (not (null? (cddr expr))))
       (- (M_value (l_operand expr) state) (M_value (r_operand expr) state))]                                 ; Subtraction
      [(eq? (pre_op expr) '-) (- 0 (l_operand expr) state)]                                                   ; Negation
      [(eq? (pre_op expr) '*) (* (M_value (l_operand expr) state) (M_value (r_operand expr) state))]          ; Multiplication
      [(eq? (pre_op expr) '/) (quotient (M_value (l_operand expr) state) (M_value (r_operand expr) state))]   ; Integer division
      [(eq? (pre_op expr) '%) (remainder (M_value (l_operand expr) state) (M_value (r_operand expr) state))]  ; Modulus
      [else (error 'badop "Bad operator")])))

; Evaluates the result of a prefix boolean expression.
(define M_bool
  (lambda (expr state)
    (cond
      [(boolean? expr) expr]                                                                                  ; Boolean
      [(var? expr) (find_var expr state)]                                                                     ; Variable
      [(eq? (pre_op expr) '!) (not (M_bool (l_operand expr) state))]                                          ; Negation
      [(eq? (pre_op expr) '&&) (and (M_bool (l_operand expr) state) (M_bool(r_operand expr) state))]          ; And
      [(eq? (pre_op expr) '||) (or (M_bool (l_operand expr) state) (M_bool (r_operand expr) state))]          ; Or
      [(eq? (pre_op expr) '==) (eq? (M_value (l_operand expr) state) (M_value (r_operand expr) state))]       ; Equality
      [(eq? (pre_op expr) '!=) (not (eq? (M_value (l_operand expr) state) (M_value (r_operand expr) state)))] ; Inequality
      [(eq? (pre_op expr) '<) (< (M_value (l_operand expr) state) (M_value (r_operand expr) state))]          ; Less than
      [(eq? (pre_op expr) '<=) (<= (M_value (l_operand expr) state) (M_value (r_operand expr) state))]        ; Less than or equals
      [(eq? (pre_op expr) '>) (> (M_value (l_operand expr) state) (M_value (r_operand expr) state))]          ; Greater than
      [(eq? (pre_op expr) '>=) (>= (M_value (l_operand expr) state) (M_value (r_operand expr) state))]        ; Greater than or equals
      [else (error 'badop "Bad operator")])))


; ==================================================================================================
;                                         STATE FUNCTIONS
; ==================================================================================================

; General state function which evaluates the change in the state given a particular statement
(define M_statement
  (lambda (stmt state)
    (cond
      [(eq? (pre_op stmt) 'var) (M_declaration stmt state)]
      [(eq? (pre_op stmt) '=) (M_assign stmt state)]
      [(eq? (pre_op stmt) 'return) 'return]
      [(eq? (pre_op stmt) 'if) (M_if stmt state)]
      [(eq? (pre_op stmt) 'while) (M_while stmt state)]
      [else (error 'badop "Invalid statement")])))

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
        (M_statementlist (stmt1 stmt) state)
        (if (null? (stmt2 stmt))
            state
            (M_statementlist (stmt2 stmt) state)))))

; Returns a state that results after the execution of a while loop.
(define M_while
  (lambda (statement state)
    (if (M_bool (condition statement) state)
        (M_while statement (M_statementlist (loop_body statement) state))
        state)))

; Returns the resulting state after a variable is assigned
(define M_assign
  (lambda (statement state)
    (add_var (var_name statement) (M_value (var_value statement) state) (remove_var (var_name statement) state))))

; Evaluates the state after a sequence of statements
(define M_statementlist
  (lambda (stmt state)
    (if (null? (next_stmt stmt))
        (M_statement (curr_stmt stmt) state)
        (M_statementlist (next_stmt stmt) (M_statement (curr_stmt stmt) state)))))