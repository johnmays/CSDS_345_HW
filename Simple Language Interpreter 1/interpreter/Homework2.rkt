; Group 5 - Josh Tang, John Mays, Abhay Pant

#lang racket

(require "simpleParser.rkt")

; ABSTRACTION!!!
(define pre_op car)
(define l_operand cadr)
(define r_operand caddr)

; Evaluates the value of an prefix mathematical expression
(define M_value
  (lambda (expr)
    (cond
      [(number? expr) expr]
      [(eq? (pre_op expr) '+) (+ (M_value (l_operand expr)) (M_value (r_operand expr)))]          ; Addition
      [(and (eq? (pre_op expr) '-) (not (null? (cddr expr))))
       (- (M_value (l_operand expr)) (M_value (r_operand expr)))]                                 ; Subtraction
      [(eq? (pre_op expr) '-) (- 0 (l_operand expr))]                                             ; Negation
      [(eq? (pre_op expr) '*) (* (M_value (l_operand expr)) (M_value (r_operand expr)))]          ; Multiplication
      [(eq? (pre_op expr) '/) (quotient (M_value (l_operand expr)) (M_value (r_operand expr)))]   ; Integer division
      [(eq? (pre_op expr) '%) (remainder (M_value (l_operand expr)) (M_value (r_operand expr)))]  ; Modulus
      [else (error 'badop "Bad operator")])))

; Evaluates the result of a prefix boolean expression
;(define M_bool
 ; (lambda (expr)
  ;  (cond
   ;   [(boolean? expr) expr]
    ;  [(eq? (pre_op expr) '!) (not (M_bool expr))]
     ; [(eq?


; 