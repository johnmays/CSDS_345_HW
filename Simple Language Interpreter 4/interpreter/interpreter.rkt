; Group 5 - Josh Tang, John Mays, Abhay Pant
#lang racket
(require "classParser.rkt")

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

; Parameter abstractions
(define curr_param car)
(define curr_ptr cadr)
(define next_param cdr)
(define next_ptr cddr)

;Class abstractions
(define class_body cadddr)

; Empty state
(define empty_state '(()()))


; ==================================================================================================
;                                         HELPER FUNCTIONS
; ==================================================================================================

; Checks if the current element is an atom, which can denote a function or variable name.
(define atom?
  (lambda (x)
    (not (or (pair? x) (null? x)))))

; Retrieves the value (or the box) of a given variable. The helper method get_ptr is used in cases with pass-by-reference.
; Here, the state takes the form ((var1 var2 var3 ...) (val1 val2 val3 ...) [subsequent layers here]).
(define get_var
  (lambda (var state)
    (cond
      [(equal? state empty_state) (error 'varerror "Variable not declared: ~a" var)]
      [(atom? (car state)) (get_var var (cdr state))]
      [(null? (state_vars state)) (get_var var (pop_outer_layer state))]
      [(eq? var (car (state_vars state)))
       (cond
         {(not (box? (car (state_vals state)))) (get_var var (cdr state))}
         {(void? (unbox (car (state_vals state)))) (error 'varerror "Variable not assigned: ~a" var)}
         {else (unbox (car (state_vals state)))})]
      [else (get_var var (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (next_layer state))))])))

(define get_ptr
  (lambda (var state)
    (cond
      [(equal? state empty_state) (error 'varerror "Variable not declared: ~a" var)]
      [(atom? (car state)) (get_ptr var (cdr state))]
      [(null? (state_vars state)) (get_ptr var (pop_outer_layer state))]
      [(and (eq? var (car (state_vars state))) (box? (car (state_vals state)))) (car (state_vals state))]
      [else (get_ptr var (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (next_layer state))))])))

; Adds a variable (or reference) to the state and returns the state. The helper method add_ptr is used whenever a reference is explicitly specified.
; If the variable already exists in the state, then raise an error.
(define add_var
  (lambda (var val state)
    (cond
      [(declared? var state) (error 'declerror "Variable already declared: ~a" var)]
      [(null? (next_layer state)) (list (cons var (state_vars state)) (cons (box val) (state_vals state)))]
      [else (append (list (cons var (state_vars state)) (cons (box val) (state_vals state))) (pop_outer_layer state))])))

(define add_ptr
  (lambda (var ptr state)
    (cond
      [(declared? var state) (error 'declerror "Variable already declared: ~a" var)]
      [(null? (next_layer state)) (list (cons var (state_vars state)) (cons ptr (state_vals state)))]
      [else (append (list (cons var (state_vars state)) (cons ptr (state_vals state))) (pop_outer_layer state))])))

(define declared?
  (lambda (var state)
    (cond
      [(atom? (car state)) (eq? (car state) var)]
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
      [(atom? (car state)) (assign_var_helper! var value (cdr state) end)] 
      [(null? (state_vars state)) (assign_var_helper! var value (pop_outer_layer state) end)]
      [(eq? var (car (state_vars state))) (begin (set-box! (car (state_vals state)) value) end)]
      [else (assign_var_helper! var value (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (cddr state))) end)])))

; Creates a new block layer for the state.
(define create_block_layer
  (lambda (state)
    (append empty_state state)))

; Creates a new function layer for the state. This will also append the function name which may be looked up later.
(define create_function_layer
  (lambda (name state)
    (append empty_state (list name) state)))

; Pops the newest (outermost) layer from the state.
(define pop_outer_layer
  (lambda (state)
    (if (or (null? (next_layer state)) (atom? (car state)))
        (error 'stateerror "Invalid state")
        (next_layer state))))

; Creates the function binding along with its closure. The helper functions for the closure are below.
(define add_func
  (lambda (name param_list body state)
    (cond
      [(declared? name state) (error 'funcerror "Function name already declared: ~a" name)]
      [(null? (next_layer state)) (list (cons name (state_vars state)) (cons (make_function_closure param_list body state) (state_vals state)))]
      [else (append (list (cons name (state_vars state)) (cons (make_function_closure param_list body state) (state_vals state))) (pop_outer_layer state))])))

; Creates a tuple containing the following:
;   - formal parameters
;   - function body
;   - a function that takes in the current state and returns the portion of state that's visible
;   - a function that returns the class the method is defined in
(define make_function_closure
  (lambda (param_list body state)
    (list param_list body
          (lambda (st) (find_state state st))
          (lambda (v) v))))

;Creates a tuple containing the following:
;   - Superclass
;   - Methods
;   - Class Fields
;   - Instance field names + initial values
(define make_class_closure
  (lambda (superclass class_body c_fields i_fields classname)
    (list superclass (filter_methods class_body classname) methods c_fields i_fields)))

(define filter_methods
  (lambda (stmts classname)
    (

;Creates a tuple containing the following:
;    - Class (Runtime type)
;    - Instance field values
(define make_instance_closure
  (lambda (class i_fields)
    (list class i_fields)))

; A helper method for the above. We only consider variables and functions on the same (or outer) lexical layers to be in scope.
(define find_state
  (lambda (orig_state given_state)
    (take-right given_state (length orig_state))))

; A function to retrieve a given function's closure.
(define get_func_closure
  (lambda (name state)
    (cond
      [(equal? state empty_state) (error 'funcerror "Function not found: ~a" name)]
      [(atom? (car state)) (get_func_closure name (cdr state))]
      [(null? (state_vars state)) (get_func_closure name (pop_outer_layer state))]
      [(and (eq? name (car (state_vars state))) (list? (car (state_vals state)))) (car (state_vals state))]
      [else (get_func_closure name (cons (cdr (state_vars state)) (cons (cdr (state_vals state)) (next_layer state))))])))

; A function to count the number of parameters.
(define num_params
  (lambda (param_list)
    (cond
      [(null? param_list) 0]
      [(eq? (car param_list) '&) (num_params (cdr param_list))]
      [else (+ 1 (num_params (cdr param_list)))])))
    
; ==================================================================================================
;                                       EVALUATION FUNCTIONS
; ==================================================================================================

; Evaluates the value of a general expression.
(define M_value
  (lambda (expr state throw)
    (M_value_helper expr state (lambda (v) v) throw)))

(define M_value_helper
  (lambda (expr state return throw)
    (cond
      [(number? expr) (return expr)]
      [(eq? expr 'true) (return #t)]
      [(eq? expr 'false) (return #f)]
      [(atom? expr) (return (get_var expr state))]
      [(eq? (pre_op expr) '+) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (+ v1 v2))) throw)) throw)]
      [(and (eq? (pre_op expr) '-) (not (null? (cddr expr))))                                                  
                              (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (- v1 v2))) throw)) throw)]                                     
      [(eq? (pre_op expr) '-) (M_value_helper (l_operand expr) state (lambda (v) (return (- 0 v))) throw)]
      [(eq? (pre_op expr) '*) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (* v1 v2))) throw)) throw)]
      [(eq? (pre_op expr) '/) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (quotient v1 v2))) throw)) throw)]
      [(eq? (pre_op expr) '%) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (remainder v1 v2))) throw)) throw)]
      [else (M_bool expr state return throw)])))

; Evaluates the result of a prefix boolean expression.
(define M_bool
  (lambda (expr state return throw)
    (M_bool_helper expr state return throw)))

(define M_bool_helper
  (lambda (expr state return throw)
    (cond
      [(eq? expr 'true) (return #t)]
      [(eq? expr 'false) (return #f)]
      [(atom? expr) (return (get_var expr state))]
      [(eq? (pre_op expr) 'funcall) (return (M_funexprcall expr state throw))]
      [(eq? (pre_op expr) '!)  (M_bool_helper (l_operand expr) state (lambda (v1) (return (not v1))) throw)]
      [(eq? (pre_op expr) '&&) (M_bool_helper (l_operand expr) state (lambda (v1) (M_bool_helper (r_operand expr) state (lambda (v2) (return (and v1 v2))) throw)) throw)]
      [(eq? (pre_op expr) '||) (M_bool_helper (l_operand expr) state (lambda (v1) (M_bool_helper (r_operand expr) state (lambda (v2) (return (or v1 v2))) throw)) throw)]
      [(eq? (pre_op expr) '==) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (eq? v1 v2))) throw)) throw)]
      [(eq? (pre_op expr) '!=) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (not (eq? v1 v2)))) throw)) throw)]
      [(eq? (pre_op expr) '<)  (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (< v1 v2))) throw)) throw)]
      [(eq? (pre_op expr) '<=) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (<= v1 v2))) throw)) throw)]
      [(eq? (pre_op expr) '>)  (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (> v1 v2))) throw)) throw)]
      [(eq? (pre_op expr) '>=) (M_value_helper (l_operand expr) state (lambda (v1) (M_value_helper (r_operand expr) state (lambda (v2) (return (>= v1 v2))) throw)) throw)]
      [else (error 'badop "Bad operator: ~a" expr)])))

; Evaluates the result of a function call as an expression.
(define M_funexprcall
  (lambda (stmt state throw)
    (let ([closure (get_func_closure (func_name stmt) state)])
      (if (not (eq? (length (closure_params closure)) (length (actual_params stmt))))
          (error 'paramerror "Parameter mismatch (expected ~a argument(s), got ~a)" (num_params (closure_params closure)) (num_params (actual_params stmt)))
          (M_statementlist (closure_body closure)
                           (bind_params (closure_params closure) (actual_params stmt) state (create_function_layer (func_name stmt) ((closure_getstate closure) state)) throw)
                           (lambda (ret) ret)
                           (lambda (nx) (error 'nexterror "Missing return value"))
                           (lambda (break) (error 'breakerror "Break outside of loop"))
                           (lambda (cont) (error 'conterror "Continue outside of loop"))
                           (lambda (ex st) (throw ex state)))))))


; ==================================================================================================
;                                         STATE FUNCTIONS
; ==================================================================================================

; Evaluates the return value of the program, replacing instances of #t and #f with 'true and 'false.
(define M_return
  (lambda (stmt state return throw)
    (let ([val (M_value (ret_val stmt) state throw)])
      (cond
        [(number? val) (return val)]
        [val (return 'true)]
        [else (return 'false)]))))

; Returns a state that declares a variable. If a value is specified, then the variable is associated with that value.
; Otherwise, the variable is given the value #<void>.
(define M_declaration
  (lambda (stmt state next throw)
    (if (not (null? (cddr stmt)))
        (next (add_var (var_name stmt) (M_value (var_value stmt) state throw) state))
        (next (add_var (var_name stmt) (void) state)))))

; Returns the resulting state after a variable is assigned.
(define M_assign
  (lambda (stmt state next throw)
    (next (assign_var! (var_name stmt) (M_value (var_value stmt) state throw) state))))

; Returns a state that results after the execution of an if statement.
(define M_if
  (lambda (stmt state return next break continue throw)
    (if (M_bool (condition stmt) state (lambda (ret) ret) throw)
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
    (if (M_bool condition state (lambda (ret) ret) throw)
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
                     (create_block_layer state)
                     return
                     (lambda (st) (next (pop_outer_layer st)))
                     (lambda (st) (break (pop_outer_layer st)))
                     (lambda (st) (continue (pop_outer_layer st)))
                     (lambda (ex st) (throw ex (pop_outer_layer st))))))

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
                             (add_var (catch_var stmt) ex (create_block_layer state))
                             return
                             (lambda (st1) (M_block finally (pop_outer_layer st1) return next break continue throw))
                             (lambda (st1) (break (pop_outer_layer st1)))
                             (lambda (st1) (continue (pop_outer_layer st1)))
                             (lambda (ex1 st1) (throw ex1 (pop_outer_layer st1)))))])))

; Creates a binding for function definitions.
(define M_fundef
  (lambda (stmt state next)
    (next (add_func (func_name stmt) (func_params stmt) (func_body stmt) state))))

; Returns the resulting state after a single statement.
(define M_state
  (lambda (stmt state return next break continue throw)
    (cond
      [(eq? (curr_stmt stmt) 'return) (M_return stmt state return throw)]
      [(eq? (curr_stmt stmt) 'var) (M_declaration stmt state next throw)]
      [(eq? (curr_stmt stmt) '=) (M_assign stmt state next throw)]
      [(eq? (curr_stmt stmt) 'if) (M_if stmt state return next break continue throw)]
      [(eq? (curr_stmt stmt) 'while) (M_while stmt state return next throw)]
      [(eq? (curr_stmt stmt) 'begin) (M_block stmt state return next break continue throw)]
      [(eq? (curr_stmt stmt) 'break) (break state)]
      [(eq? (curr_stmt stmt) 'continue) (continue state)]
      [(eq? (curr_stmt stmt) 'try) (M_try stmt state return next break continue throw)]
      [(eq? (curr_stmt stmt) 'throw) (throw (M_value (throw_block stmt) state throw) state)]
      [(eq? (curr_stmt stmt) 'finally) (M_state (next_stmt stmt) (create_block_layer state) return next break continue throw)]
      [(eq? (curr_stmt stmt) 'function) (M_fundef stmt state next)]
      [(eq? (curr_stmt stmt) 'funcall) (M_funstmtcall stmt state next throw)]
      [(eq? (curr_stmt stmt) 'class) (make_class_closure (M_statementlist (class_body stmt) state return next break continue throw)]
      [else (error 'badstmt "Invalid statement: ~a" stmt)])))

; Handles the continuations and the state modifications made during a function call.
; We handle parameter binding via a helper function.
(define M_funstmtcall
  (lambda (stmt state next throw)
    (let ([closure (get_func_closure (func_name stmt) state)])
      (if (not (eq? (num_params (closure_params closure)) (num_params (actual_params stmt))))
          (error 'paramerror "Parameter mismatch (expected ~a argument(s), got ~a)" (num_params (closure_params closure)) (num_params (actual_params stmt)))
          (M_statementlist (closure_body closure)
                           (bind_params (closure_params closure) (actual_params stmt) state (create_function_layer (func_name stmt) ((closure_getstate closure) state)) throw)
                           (lambda (ret) (next state))
                           (lambda (nex) (next state))
                           (lambda (break) (error 'breakerror "Break outside of loop"))
                           (lambda (cont) (error 'conterror "Continue outside of loop"))
                           (lambda (ex st) (throw ex state)))))))

; Takes a state and binds the formal parameters to the actual parameters inside
; Formal parameters marked with & are bound to the pointer of the actual parameter
(define bind_params
  (lambda (formal_params actual_params state func_state throw)
    (cond
      [(null? formal_params) func_state]
      [(eq? (curr_param formal_params) '&) (if (not (atom? (curr_param actual_params)))
                                               (error 'paramerror "Variable name expected, ~a received" (curr_param actual_params))
                                               (bind_params (next_ptr formal_params)
                                                            (next_param actual_params)
                                                            state
                                                            (add_ptr (curr_ptr formal_params) (get_ptr (curr_param actual_params) state) func_state)
                                                            throw))]
      [else (bind_params (next_param formal_params)
                         (next_param actual_params)
                         state
                         (add_var (curr_param formal_params) (M_value (curr_param actual_params) state throw) func_state)
                         throw)])))

; Handles lists of statements, which are executed sequentially
; This is where we make our 'next' continuation, which refers to the next string of code to be executed
(define M_statementlist
  (lambda (stmts state return next break continue throw)
    (if (null? stmts)
        (next state)
        (M_state (curr_stmt stmts) state return
                 (lambda (nstate) (M_statementlist (next_stmt stmts) nstate return next break continue throw)) break continue throw))))

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
                            (create_function_layer 'main global_state)
                            ret
                            (lambda (next) next)
                            (lambda (break) (error 'breakerror "Invalid break location."))
                            (lambda (cont) (error 'conterror "Invalid continue location."))
                            (lambda (ex val) (error 'throwerror "Uncaught exception thrown.")))))))

; Testing state
; '((g) (#&#t) (f e d) (#&#f #&#<void> #&3) (c b a) (#&2 #&1 #&#t))
(define test_state
  (add_var 'g #t
           (create_block_layer
            (add_var 'f #f
                     (add_var 'e (void)
                              (add_var 'd 3
                                       (create_block_layer
                                        (add_var 'c 2
                                                 (add_var 'b 1
                                                          (add_var 'a #t empty_state))))))))))