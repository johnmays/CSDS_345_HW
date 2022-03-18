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
(define outer_state caddr)

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
; Here, the state takes the form ((var1 var2 var3 ...) (val1 val2 val3 ...) [nested states here])
(define find_var
  (lambda (var state)
    (cond
      [(equal? state empty_state) (error 'varerror "Variable not declared")]
      [(null? (state_vars state)) (find_var var (outer_state state))]
      [(and (eq? var (car (state_vars state))) (void? (unbox (car (state_vals state))))) (error 'varerror "Variable not assigned")]
      [(eq? var (car (state_vars state))) (unbox (car (state_vals state)))]
      [else (find_var var (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (cddr state))))])))

; Adds a variable to the state and returns the state.
; If the variable already exists in the state, then raise an error.
(define add_var
  (lambda (var val state)
    (cond
      [(declared? var state) (error 'declerror "Variable already declared")]
      [(null? (cddr state)) (list (cons var (state_vars state)) (cons (box val) (state_vals state)))]
      [else (list (cons var (state_vars state)) (cons (box val) (state_vals state)) (outer_state state))])))

(define declared?
  (lambda (var state)
    (cond
      [(equal? state empty_state) #f]
      [(null? (state_vars state)) (declared? var (outer_state state))]
      [(eq? var (car (state_vars state))) #t]
      [else (declared? var (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (cddr state))))])))

; Assigns a particular value to a given variable.
; This utilizes set-box!, which will cause side effects by default.
(define assign_var!
  (lambda (var value state)
    (assign_var_helper! var value (state_vars state) (state_vals state) (lambda (vars vals) (list vars vals)))))

(define assign_var_helper!
  (lambda (var value varlist vallist return)
    (cond
      [(null? varlist) (error 'assignerror "Variable not declared.")]
      [(eq? var (car varlist)) (begin (set-box! (car vallist) value) (return varlist vallist))]
      [else (assign_var_helper! var value (cdr varlist) (cdr vallist)
                                (lambda (vars vals) (return (cons (car varlist) vars) (cons (car vallist) vals))))])))

; Creates a new layer for the state.
(define create_inner_state
  (lambda (state)
    (list null null state)))


; ==================================================================================================
;                                       EVALUATION FUNCTIONS
; ==================================================================================================

; Evaluates the value of a general expression.
(define M_value
  (lambda (expr state)
    (M_value_helper expr state (lambda (v) v))))

(define M_value_helper
  (lambda (expr state return)
    (cond
      [(number? expr) (return expr)]
      [(var? expr) (return (find_var expr state))]
      [(eq? (pre_op expr) '+) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (+ v1 v2))))))]
      [(and (eq? (pre_op expr) '-) (not (null? (cddr expr))))                                                  
                              (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (- v1 v2))))))]                                     
      [(eq? (pre_op expr) '-) (M_value_helper (l_operand expr) state (lambda (v) (return (- 0 v))))]
      [(eq? (pre_op expr) '*) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (* v1 v2))))))]
      [(eq? (pre_op expr) '/) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (quotient v1 v2))))))]
      [(eq? (pre_op expr) '%) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (remainder v1 v2))))))]
      [else (M_bool expr state)])))

; Evaluates the result of a prefix boolean expression.
(define M_bool
  (lambda (expr state)
    (M_bool_helper expr state (lambda (v) v))))

(define M_bool_helper
  (lambda (expr state return)
    (cond
      [(eq? expr 'true) (return #t)]
      [(eq? expr 'false) (return #f)]
      [(var? expr) (return (find_var expr state))]
      [(eq? (pre_op expr) '!)  (M_bool_helper (l_operand expr) state (lambda (v1) (return (not v1))))]
      [(eq? (pre_op expr) '&&) (M_bool_helper (l_operand expr) state (lambda (v1) (M_bool_helper (r_operand expr) state (lambda (v2) (return (and v1 v2))))))]
      [(eq? (pre_op expr) '||) (M_bool_helper (l_operand expr) state (lambda (v1) (M_bool_helper (r_operand expr) state (lambda (v2) (return (or v1 v2))))))]
      [(eq? (pre_op expr) '==) (M_bool_helper (l_operand expr) state (lambda (v1) (M_bool_helper (r_operand expr) state (lambda (v2) (return (eq? v1 v2))))))]
      [(eq? (pre_op expr) '!=) (M_bool_helper (l_operand expr) state (lambda (v1) (M_bool_helper (r_operand expr) state (lambda (v2) (return (not (eq? v1 v2)))))))]
      [(eq? (pre_op expr) '<)  (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (< v1 v2))))))]
      [(eq? (pre_op expr) '<=) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (<= v1 v2))))))]
      [(eq? (pre_op expr) '>)  (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (> v1 v2))))))]
      [(eq? (pre_op expr) '>=) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (>= v1 v2))))))]
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
    (assign_var! (var_name stmt) (M_value (var_value stmt) state) state)))

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

; Testing state
(define test_state
  (add_var 'f #f
           (add_var 'e (void)
                    (add_var 'd 3
                             (create_inner_state
                              (add_var 'c 2
                                       (add_var 'b 1
                                                (add_var 'a #t empty_state))))))))