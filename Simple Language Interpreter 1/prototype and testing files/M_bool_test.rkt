#lang racket
(require "M_value_test_jkm100.rkt")

; Abstracted Functions:
(define pre_op car)
(define l_operand cadr)
(define r_operand caddr)

; this M_bool expression only evaluates the conditional expressions (operators such as ==, <, >=, etc.)

(define M_bool
  (lambda (expression)
    (cond
      [(boolean? expression) expression]
      [(eq? (pre_op expression) '!) (not (l_operand expression))]
      [(eq? (pre_op expression) '==) (eq? (M_value (l_operand expression)) (r_operand expression))]
      [(eq? (pre_op expression) '!=) (not (eq? (M_value (l_operand expression)) (r_operand expression)))]
      [(eq? (pre_op expression) '<) (< (M_value (l_operand expression)) (r_operand expression))]
      [(eq? (pre_op expression) '<=) (<= (M_value (l_operand expression)) (r_operand expression))]
      [(eq? (pre_op expression) '>) (> (M_value (l_operand expression)) (r_operand expression))]
      [(eq? (pre_op expression) '>=) (>= (M_value (l_operand expression)) (r_operand expression))]
      ; ------ ERROR HANDLING NEEDS TO GO HERE AT SOME POINT -------
      )))

