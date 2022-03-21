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
(define curr_inner_stmt caar)
(define finally_block cadddr)
(define catch_block caddr)
(define catch_var caaddr)
(define try_block cadr)
(define throw_block cadr)


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
; Here, the state takes the form ((var1 var2 var3 ...) (val1 val2 val3 ...) [nested states here]).
(define find_var
  (lambda (var state)
    (cond
      [(equal? state empty_state) (error 'varerror "Variable not declared: ~a" var)]
      [(null? (state_vars state)) (find_var var (pop_inner_state state))]
      [(and (eq? var (car (state_vars state))) (void? (unbox (car (state_vals state))))) (error 'varerror "Variable not assigned: ~a" var)]
      [(eq? var (car (state_vars state))) (unbox (car (state_vals state)))]
      [else (find_var var (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (cddr state))))])))

; Adds a variable to the state and returns the state.
; If the variable already exists in the state, then raise an error.
(define add_var
  (lambda (var val state)
    (cond
      [(declared? var state) (error 'declerror "Variable already declared: ~a" var)]
      [(null? (cddr state)) (list (cons var (state_vars state)) (cons (box val) (state_vals state)))]
      [else (list (cons var (state_vars state)) (cons (box val) (state_vals state)) (pop_inner_state state))])))

(define declared?
  (lambda (var state)
    (cond
      [(equal? state empty_state) #f]
      [(null? (state_vars state)) #f];(declared? var (pop_inner_state state))]
      [(eq? var (car (state_vars state))) #t]
      [else (declared? var (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (cddr state))))])))

; Assigns a particular value to a given variable.
; This utilizes set-box!, which will cause side effects by default.
(define assign_var!
  (lambda (var value state)
    (call/cc (lambda (end) (assign_var_helper! var value state state)))))

(define assign_var_helper!
  (lambda (var value state end)
    (cond
      [(equal? state empty_state) (error 'varerror "Variable not declared: ~a" var)]
      [(null? (state_vars state)) (assign_var_helper! var value (pop_inner_state state) end)]
      [(eq? var (car (state_vars state))) (begin (set-box! (car (state_vals state)) value) end)]
      [else (assign_var_helper! var value (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (cddr state))) end)])))

; Creates a new layer for the state.
(define create_inner_state
  (lambda (state)
    (list null null state)))

; Pops the newest layer from the state.
(define pop_inner_state
  (lambda (state)
    (if (null? (cddr state))
        (error 'breakerror "Cannot break here.")
        (caddr state))))

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
      [(eq? (pre_op expr) '==) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (eq? v1 v2))))))]
      [(eq? (pre_op expr) '!=) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (not (eq? v1 v2)))))))]
      [(eq? (pre_op expr) '<)  (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (< v1 v2))))))]
      [(eq? (pre_op expr) '<=) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (<= v1 v2))))))]
      [(eq? (pre_op expr) '>)  (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (> v1 v2))))))]
      [(eq? (pre_op expr) '>=) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (>= v1 v2))))))]
      [else (error 'badop "Bad operator: ~a" expr)])))


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
  (lambda (stmt state return next break continue throw)
    (if (M_bool (condition stmt) state)
        (M_state (stmt1 stmt) state return next break continue throw)
        (if (null? (elif stmt))
            (next state)
            (M_state (stmt2 stmt) state return next break continue throw)))))

; Returns a state that results after the execution of a while loop.
; We invoke a helper method, loop, that does the actual looping for us.
(define M_while
  (lambda (stmt state return next prev_break continue throw)
    (loop (condition stmt) (loop_body stmt) state return next
                (lambda (break_state) (next break_state)) continue throw) continue throw))                     ; <-- This is where we specify our break continuation.

(define loop
  (lambda (condition body state return next break continue throw)
    (let ([next_loop (lambda (repeat_state) (loop condition body repeat_state return next break continue throw))])   ; <-- This is where we specify our next loop continuation.
      (if (M_bool condition state)                                                                                   ; It is used for 'continue' and 'next'.
          (M_state body state return next_loop break next_loop throw)
          (next state)))))

; Returns the resulting state after a variable is assigned.
(define M_assign
  (lambda (stmt state)
    (assign_var! (var_name stmt) (M_value (var_value stmt) state) state)))

; Returns the resulting state after a statement or sequence of statements.
(define M_state
  (lambda (stmts state return next break continue throw)
    (cond
      [(null? stmts) (next state)]
      [(list? (curr_stmt stmts)) (M_block stmts state return next break continue throw)]
      [(eq? (curr_stmt stmts) 'return) (M_return stmts state return)]
      [(eq? (curr_stmt stmts) 'var) (M_declaration stmts state)]
      [(eq? (curr_stmt stmts) '=) (M_assign stmts state)]
      [(eq? (curr_stmt stmts) 'begin) (M_state (next_stmt stmts) (create_inner_state state) return next break continue throw)]
      [(eq? (curr_stmt stmts) 'break) (break (pop_inner_state state))]
      [(eq? (curr_stmt stmts) 'continue) (continue state)]
      [(eq? (curr_stmt stmts) 'if) (M_if stmts state return next break continue throw)]
      [(eq? (curr_stmt stmts) 'throw) (throw (throw_block stmts) state)]
      [(eq? (curr_stmt stmts) 'catch) (next (M_block (catch_block stmts) state return next break continue throw))]
      [(eq? (curr_stmt stmts) 'finally) (M_state (cdr stmts) state return next break continue throw)]
      [else (error 'badop "Invalid statement: ~a" stmts)])))

; Handles the continuations that occur from block statements (like while loops).
(define M_block
  (lambda (stmts state return next break continue throw)
    (let* ([new_next (lambda (next_state) (M_state (next_stmt stmts) next_state return next break continue throw))]
           [new_break (lambda (next_state) (M_state (finally_block (car stmts)) next_state return break break continue throw))]
           [finally_cont (lambda (next_state) (M_state (finally_block (car stmts)) next_state return new_next break continue throw))]
           [new_throw (lambda (next_state) (M_state (finally_block (car stmts)) next_state return next break continue throw))]
           [my_throw (lambda (e next_state) (M_state (catch_block (car stmts)) (add_var (caadr (catch_block (car stmts))) e next_state) return finally_cont new_break continue new_throw))])
      (cond
        [(eq? (curr_inner_stmt stmts) 'while) (M_while (curr_stmt stmts) state return new_next break continue throw)]
        [(eq? (curr_inner_stmt stmts) 'if) (M_if (curr_stmt stmts) state return new_next break continue throw)]
        [(eq? (curr_inner_stmt stmts) 'try) (M_state (try_block (curr_stmt stmts)) state return finally_cont new_break continue my_throw)]
        [else (M_state (next_stmt stmts) (M_state (curr_stmt stmts) state return next break continue throw) return next break continue throw)]))))    
      
; Evaluates the return value of the program, replacing instances of #t and #f with 'true and 'false.
(define M_return
  (lambda (stmt state return)
    (if (number? (M_value (ret_val stmt) state))
        (return (M_value (ret_val stmt) state))
        (if (M_bool (ret_val stmt) state)
            (return 'true)
            (return 'false)))))

; ==================================================================================================
;                                                MAIN
; ==================================================================================================
(define interpret
  (lambda (filename)
    (call/cc (lambda (ret) (M_state (parser filename) empty_state ret 'invalid_next 'invalid_break 'invalid_continue 'invalid_throw)))))

; Testing state
; '((f e d) (#&18 #&#<void> #&3) ((c b a) (#&2 #&1 #&#t)))
(define test_state
  (add_var 'f #f
           (add_var 'e (void)
                    (add_var 'd 3
                             (create_inner_state
                              (add_var 'c 2
                                       (add_var 'b 1
                                                (add_var 'a #t empty_state))))))))