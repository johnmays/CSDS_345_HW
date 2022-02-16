#lang racket

(define M_assign
  (lambda (statement state)
    (remove_var (var statement) state)
    (add_var (var statement) (val statement) state)))
     
(define var cadr)
(define val caddr)