#lang racket
;possible M_state
(define M_state
  (lambda (stmt-list state)
    (cond
      [(null? stmt-list) state];(find_var 'return state)]
      [(eq? (pre_op (car stmt-list)) 'var) (M_state (cdr stmt-list)(M_declaration (car stmt-list) state))]
      [(eq? (pre_op (car stmt-list)) '=) (M_state (cdr stmt-list)(M_assign (car stmt-list) state))]
      [(eq? (pre_op (car stmt-list)) 'if) (M_state (cdr stmt-list)(M_if (car stmt-list) state))]
      [(eq? (pre_op (car stmt-list)) 'while) (M_state (cdr stmt-list)(M_while (car stmt-list) state))]
      [else (error 'badop "Invalid statement")])))