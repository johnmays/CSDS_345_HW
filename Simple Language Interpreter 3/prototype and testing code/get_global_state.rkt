#lang racket
(define get_global_state
  (lambda (state)
    (cond
      [(not (null? (cddr state))) (get_global_state (cdr state))]
      [else state])))