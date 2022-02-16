#lang racket

(define M_if
  (lambda (statement state)
    (M_state (condition statement) state)
    (if (eq? (M_boolean (condition statement) state) #t)
        (M_state (statement-1 statement))
        (if (null? (else-statement statement))
            (state)
            (M_state (statement-2 statement) state)))))
                  
(define condition cadr)
(define statement-1 caddr)
(define else-statement cdddr)
(define statement-2 cadddr)