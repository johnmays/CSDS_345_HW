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

; ==================================================================================================
;                                         HELPER FUNCTIONS
; ==================================================================================================

; Checks if an atom is a potential variable name
(define var?
  (lambda (x)
    (not (or (pair? x) (null? x)))))

; Retrieves the value of a given variable
; Here, the state takes the form ((var1 var2 var3 ...) (val1 val2 val3 ...))
(define find_var
  (lambda (var state)
    (find_var* var (state_vars state) (state_vals state))))

(define find_var*
  (lambda (var varlist vallist)
    (cond
      [(null? varlist) (error 'initerror "Variable not initialized")]
      [(eq? var (car varlist)) (car vallist)]
      [else (find_var* var (cdr varlist) (cdr vallist))])))

; Adds a variable to the state and returns the state
(define add_var
  (lambda (var val state)
    (cons (cons var (state_vars state)) (cons (cons val (state_vals state)) null))))

; Removes a variable and its corresponding value from the state, if present
(define remove_var
  (lambda (var state)
    (remove_var* (state_vars state) (state_vals state))))

(define remove_var*
  (lambda (var varlist vallist)
    (cond
      [(null? varlist) (cons varlist (cons vallist null))]
      [(eq? var (car varlist)) (cons (cdr varlist) (cons (cdr vallist) null))]
      [else (cons (cons (car varlist) (car (remove_var* var (cdr varlist) (cdr vallist))))
                  (cons (cons (car vallist) (cadr (remove_var* var (cdr varlist) (cdr vallist)))) null))])))


; ==================================================================================================
;                                       EVALUATION FUNCTIONS
; ==================================================================================================

; Evaluates the value of an prefix mathematical expression
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

; Evaluates the result of a prefix boolean expression
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
      [(eq? (pre_op expr) '>=) (>= (M_value (l_operand expr) state) (M_value (r_operand expr) state))]        ; Greather than or equals
      [else (error 'badop "Bad operator")])))


; ==================================================================================================
;                                         STATE FUNCTIONS
; ==================================================================================================

