#lang racket
; ==================================================================================================
;                                           ABSTRACTIONS
; ==================================================================================================

(define pre_op car)
(define l_operand cadr)
(define r_operand caddr)

(define state_vars car)
(define state_vals cadr)

(define condition cadr)
(define statement-1 caddr)
(define statement-2 cadddr)
(define else cdddr)

(define loopbody caddr)
; ==================================================================================================
;                                          STATEMENT EVAL
; ==================================================================================================

; (M_while (while (cond) (statement-list)))

(define M_while
  (lambda (statement state)
    (if [M_bool (condition statement) state]
        [M_while (statement (M_state ((loopbody statement) state)))]
        [state])))