#lang racket

; (Mvalue (lis)) returns the value of a list where the list is '(lOperand operator rOperand) or it's just a number
; keep in mind the operands can be lists of their own

(define M_value
  (lambda (expression)
    (cond
      [(number? expression) expression]
      [(eq? (car expression) '+) (+ (M_value (cadr expression)) (M_value (caddr expression)))]
      [(eq? (car expression) '-) (- (M_value (cadr expression)) (M_value (caddr expression)))]
      [(eq? (car expression) '*) (* (M_value (cadr expression)) (M_value (caddr expression)))]
      [(eq? (car expression) '/) (quotient (M_value (cadr expression)) (M_value (caddr expression)))]
      [else (error 'badop "Bad expression")])))

; except format will actually be more like: '(* (-2 1) (+ 6 5))
; we didn't use abstraction
     ; replace code w/ a name

(define operator
  (lambda (exp)
    (car exp)))

(define leftoperand cadr)

(provide (all-defined-out))