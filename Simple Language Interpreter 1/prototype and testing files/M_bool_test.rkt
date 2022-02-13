#lang racket

; Abstracted Functions:
(define pre_op car)
(define l_operand cadr)
(define r_operand caddr)


(define M_bool
  (lambda (expression)
    (cond
      [(boolean? expression) expression]
      [(eq? (pre_op expression) '!) (not (l_operand expression))]
      [(eq? (pre_op expression) '==') (eq? (M_value (l_operand (expression))) (r_operand (expression)))])))

