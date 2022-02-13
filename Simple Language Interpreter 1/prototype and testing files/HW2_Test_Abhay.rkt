#lang racket

(define statement-type
  (lambda (lis)
    (cond
      [(eq? (car lis) 'var) 'declare]
      [(eq? (car lis) '=) 'assign]
      [(eq? (car lis) 'return) 'return]
      [(eq? (car lis) 'if) 'if]
      [(eq? (car lis) 'while) 'while]
      [else (error 'badop "Invalid Statement")])))

(define M_boolean
  (lambda (expression)
    (cond
      [(boolean? expression) expression]
      [(boolean? expression) expression]
      [(eq? (bool_operator expression) '&&) (and (M_boolean (l_bool expression)) (M_boolean(r_bool expression)))]
      [(eq? (bool_operator expression) '||) (or (M_boolean (l_bool expression)) (M_boolean (r_bool expression)))]
      [(eq? (bool_operator expression) '!) (not (M_boolean (l_bool expression)))])))

(define l_bool cadr)
(define r_bool caddr)
(define bool_operator car)
