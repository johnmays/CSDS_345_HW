#lang racket

(define M_if
  (lambda (statement state)
    (M_state (condition statement) state)
    (if (eq? (M_boolean (condition statement) state) #t)
        (M_state (statement-1 statement))
        (if (null? (statement-2 statement))
            (state)
            (M_state (statement-2 statement))))))
                  
(define condition cadr)
(define statement-1 caddr)
(define statement-2 cdddr)