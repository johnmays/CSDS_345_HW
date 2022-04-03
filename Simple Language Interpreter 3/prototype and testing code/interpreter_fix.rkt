; Group 5 - Josh Tang, John Mays, Abhay Pant
#lang racket
(require "functionParser.rkt")

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
(define next_layer cddr)

; Variable access abstractions
(define var_name cadr)
(define var_value caddr)

; If-statement & while-loop abstractions
(define condition cadr)
(define stmt1 caddr)
(define elif cdddr)
(define stmt2 cadddr)
(define loop_body caddr)

; Statement list abstractions
(define curr_stmt car)
(define next_stmt cdr)

; Catch-try-finally abstractions
(define finally_block cadddr)
(define catch_block caddr)
(define catch_var caadr)
(define try_block cadr)
(define throw_block cadr)

; Return abstraction
(define ret_val cadr)

; Function definition abstractions
(define func_name cadr)
(define func_params caddr)
(define func_body cadddr)
(define actual_params cddr)
; Closure abstractions
(define closure_params car)
(define closure_body cadr)
(define closure_getstate caddr)

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
; Here, the state takes the form ((var1 var2 var3 ...) (val1 val2 val3 ...) [subsequent layers here]).
(define get_var
  (lambda (var state)
    (cond
      [(equal? state empty_state) (error 'varerror "Variable not declared: ~a" var)]
      [(null? (state_vars state)) (get_var var (pop_inner_state state))]
      [(and (eq? var (car (state_vars state))) (void? (unbox (car (state_vals state))))) (error 'varerror "Variable not assigned: ~a" var)]
      [(and (eq? var (car (state_vars state))) (box? (car (state_vals state)))) (unbox (car (state_vals state)))]
      [else (get_var var (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (next_layer state))))])))

; Adds a variable to the state and returns the state.
; If the variable already exists in the state, then raise an error.
(define add_var
  (lambda (var val state)
    (cond
      [(declared? var state) (error 'declerror "Variable already declared: ~a" var)]
      [(null? (next_layer state)) (list (cons var (state_vars state)) (cons (box val) (state_vals state)))]
      [else (append (list (cons var (state_vars state)) (cons (box val) (state_vals state))) (pop_inner_state state))])))

(define declared?
  (lambda (var state)
    (cond
      [(null? (state_vars state)) (if (null? (next_layer state))
                                      #f
                                      (declared? var (next_layer state)))]
      [(eq? var (car (state_vars state))) #t]
      [else (declared? var (append (list (cdr (state_vars state)) (cdr (state_vals state))) (next_layer state)))])))

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
    (append empty_state state)))

; Pops the newest layer from the state.
(define pop_inner_state
  (lambda (state)
    (if (null? (next_layer state))
        (error 'stateerror "Invalid state.")
        (next_layer state))))

; Creates the function binding along with its closure. The helper functions for the closure are below.
(define add_func
  (lambda (name param_list body state)
    (cond
      [(declared? name state) (error 'funcerror "Function name already declared: ~a" name)]
      [(null? (next_layer state)) (list (cons name (state_vars state)) (cons (make_closure param_list body state) (state_vals state)))]
      [else (append (list (cons name (state_vars state)) (cons (make_closure param_list body state) (state_vals state))) (pop_inner_state state))])))

; Creates a tuple containing the following:
;   - formal parameters
;   - function body
;   - a function that takes in the current state and returns the portion of state that's visible
(define make_closure
  (lambda (param_list body state)
    (list param_list body
          (lambda (st) (find_state st state)))))

; A helper method for the above. We only consider variables and functions on the same (or outer) lexical layers to be in scope.
(define find_state
  (lambda (given_state orig_state)
    (take-right given_state (length orig_state))))

; A function to retrieve a given function's closure.
(define get_func_closure
  (lambda (name state)
    (cond
      [(equal? state empty_state) (error 'funcerror "Function not found: ~a" name)]
      [(null? (state_vars state)) (get_func_closure name (pop_inner_state state))]
      [(and (eq? name (car (state_vars state))) (list? (car (state_vals state)))) (car (state_vals state))]
      [else (get_func_closure name (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (next_layer state))))])))
    
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
      [(var? expr) (return (get_var expr state))]
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
      [(var? expr) (return (get_var expr state))]
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

; Evaluates the return value of the program, replacing instances of #t and #f with 'true and 'false.
(define M_return
  (lambda (stmt state return)
    (if (number? (M_value (ret_val stmt) state))
        (return (M_value (ret_val stmt) state))
        (if (M_bool (ret_val stmt) state)
            (return 'true)
            (return 'false)))))

; Returns a state that declares a variable. If a value is specified, then the variable is associated with that value.
; Otherwise, the variable is given the value #<void>.
(define M_declaration
  (lambda (stmt state next)
    (if (not (null? (cddr stmt)))
        (next (add_var (var_name stmt) (M_value (var_value stmt) state) state))
        (next (add_var (var_name stmt) (void) state)))))

; Returns the resulting state after a variable is assigned.
(define M_assign
  (lambda (stmt state next)
    (next (assign_var! (var_name stmt) (M_value (var_value stmt) state) state))))

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
  (lambda (stmt state return next throw)
    (loop (condition stmt) (loop_body stmt) state return next throw)))

(define loop
  (lambda (condition body state return next throw)
    (if (M_bool condition state)
        (M_state body state return
                 (lambda (st) (loop condition body st return next throw))
                 (lambda (st) (next st))                                  ; <-- Break continuation
                 (lambda (st) (loop condition body st return next throw)) ; <-- Continue continuation (same as next)
                 throw)
        (next state))))

; Evaluates a block of code.
(define M_block
  (lambda (stmts state return next break continue throw)
    (M_statementlist (next_stmt stmts)
                     (create_inner_state state)
                     return
                     (lambda (st) (next (pop_inner_state st)))
                     (lambda (st) (break (pop_inner_state st)))
                     (lambda (st) (continue (pop_inner_state st)))
                     (lambda (ex st) (throw ex (pop_inner_state st))))))

; Evaluates a try/catch/finally statement.
; We also have helper methods to reuse M_block for the try and finally blocks (by manually inserting the "begin" keyword at those locations).
; Another helper method creates all of the next/break/continue/throw continuations as necessary.
(define M_try
  (lambda (stmt state return next break continue throw)
    (let* (
           [try_stmts (blockify_try (try_block stmt))]
           [finally_stmts (blockify_finally (finally_block stmt))]
           [new_return (lambda (v) (M_block finally_stmts state return (lambda (s) (return s)) break continue throw))]
           [new_break (lambda (v) (M_block finally_stmts state return (lambda (s) (break s)) break continue throw))]
           [new_continue (lambda (v) (M_block finally_stmts state return (lambda (s) (continue s)) break continue throw))]
           [new_throw (create_throw_continuations (catch_block stmt) state return next break continue throw finally_stmts)])
      (M_block try_stmts state new_return (lambda (st) (M_block finally_stmts st return next break continue throw)) new_break new_continue new_throw))))
    
(define blockify_try
  (lambda (try_stmt)
    (cons 'begin try_stmt)))

(define blockify_finally
  (lambda (finally_stmt)
    (cond
      [(null? finally_stmt) '(begin)]
      [(not (eq? (curr_stmt finally_stmt) 'finally)) (error 'badstmt "Incorrect finally statement.")]
      [else (cons 'begin (cadr finally_stmt))])))

(define create_throw_continuations
  (lambda (stmt state return next break continue throw finally)
    (cond
      [(null? stmt) (lambda (ex st) (M_block finally state return (lambda (st) (throw ex st)) break continue throw))]
      [(not (eq? (curr_stmt stmt) 'catch)) (error 'badstmt "Incorrect catch statement.")]
      [else (lambda (ex st) (M_statementlist
                             (stmt1 stmt)
                             (add_var (catch_var stmt) ex (create_inner_state state))
                             return
                             (lambda (st1) (M_block finally (pop_inner_state st1) return next break continue throw))
                             (lambda (st1) (break (pop_inner_state st1)))
                             (lambda (st1) (continue (pop_inner_state st1)))
                             (lambda (ex1 st1) (throw ex1 (pop_inner_state st1)))))])))

; Creates a binding for function definitions.
(define M_fundef
  (lambda (stmt state next)
    (next (add_func (func_name stmt) (func_params stmt) (func_body stmt) state))))

; Handles the continuations and the state modifications made during a function call. (TODO)
(define M_funcall
  (lambda (stmt state return next break continue throw)
    (null)))

; Returns the resulting state after a single statement.
(define M_state
  (lambda (stmt state return next break continue throw)
    (cond
      [(eq? (curr_stmt stmt) 'return) (M_return stmt state return)]
      [(eq? (curr_stmt stmt) 'var) (M_declaration stmt state next)]
      [(eq? (curr_stmt stmt) '=) (M_assign stmt state next)]
      [(eq? (curr_stmt stmt) 'if) (M_if stmt state return next break continue throw)]
      [(eq? (curr_stmt stmt) 'while) (M_while stmt state return next throw)]
      [(eq? (curr_stmt stmt) 'begin) (M_block stmt state return next break continue throw)]
      [(eq? (curr_stmt stmt) 'break) (break state)]
      [(eq? (curr_stmt stmt) 'continue) (continue state)]
      [(eq? (curr_stmt stmt) 'try) (M_try stmt state return next break continue throw)]
      [(eq? (curr_stmt stmt) 'throw) (throw (M_value (throw_block stmt) state) state)]
      [(eq? (curr_stmt stmt) 'finally) (M_state (next_stmt stmt) (create_inner_state state) return next break continue throw)]
      [(eq? (curr_stmt stmt) 'function) (M_fundef stmt state next)]
      [(eq? (curr_stmt stmt) 'funcall)
       (begin
         (define closure (get_func_closure (func_name stmt) state))
         (M_state
              (closure_body closure)
              (bind_params (closure_params closure) (actual_params stmt) state throw ((closure_getstate closure) state))
              (lambda (s v) (return s v))
              (lambda (s) (next s))
              (lambda (s) (error 'breakerror "Break outside of loop"))
              (lambda (s) (error 'conterror "Continue outside of loop"))
              (lambda (s e) (throw s e))))
       ]
      [else (error 'badstmt "Invalid statement: ~a" stmt)])))

(define bind_params
  (lambda (formal_params actual_params state throw func_state)
    (begin
      (define func_state (create_inner_state func_state))
      (if (or (null? formal_params) (null? actual_params))
          func_state
          (bind_params (cdr formal_params) (cdr actual_params) state throw (add_var (car formal_params) (M_value (car actual_params)) state))))))

; Handles lists of statements, which are executed sequentially
(define M_statementlist
  (lambda (stmts state return next break continue throw)
    (if (null? stmts)
        (next state)
        (M_state (curr_stmt stmts) state return
                 (lambda (nstate) (M_statementlist (next_stmt stmts) nstate return next break continue throw)) break continue throw)))) ; <-- This is where we make our 'next' continuation.

; ==================================================================================================
;                                                MAIN
; ==================================================================================================

; Our main function.
(define interpret
  (lambda (filename)
      (execute_main (global_state_bindings (parser filename)))))

; Our initial pass through the file. This will populate the state with the global variables and function definitions.
(define global_state_bindings
  (lambda (stmts)
    (M_statementlist stmts empty_state
                     (lambda (ret) (error 'returnerror "Invalid return location."))
                     (lambda (next) next)
                     (lambda (break) (error 'breakerr "Invalid break location."))
                     (lambda (cont) (error 'conterror "Invalid continue location."))
                     (lambda (ex val) (error 'throwerror "Invalid throw location.")))))

; Our secondary pass through the file, executing whatever is in the declared main() function.
; (If there is no main function, then get_func_closure will issue an error.)
(define execute_main
  (lambda (global_state)
    (call/cc (lambda (ret) (M_statementlist
                            (closure_body (get_func_closure 'main global_state))
                            (create_inner_state global_state)
                            ret
                            (lambda (next) next)
                            (lambda (break) (error 'breakerror "Invalid break location."))
                            (lambda (cont) (error 'conterror "Invalid continue location."))
                            (lambda (ex val) (error 'throwerror "Uncaught exception thrown.")))))))

; Testing state
; '((g) (#&#t) (f e d) (#&#f #&#<void> #&3) (c b a) (#&2 #&1 #&#t))
(define test_state
  (add_var 'g #t
           (create_inner_state
            (add_var 'f #f
                     (add_var 'e (void)
                              (add_var 'd 3
                                       (create_inner_state
                                        (add_var 'c 2
                                                 (add_var 'b 1
                                                          (add_var 'a #t empty_state))))))))))