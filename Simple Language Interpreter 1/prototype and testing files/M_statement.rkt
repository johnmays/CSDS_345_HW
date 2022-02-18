#lang racket

; General state function which evaluates the change in the state given a particular statement
(define M_statement
  (lambda (stmt state)
    (cond
      [(eq? (pre_op stmt) 'var) (M_declaration stmt state)]
      [(eq? (pre_op stmt) '=) (M_assign stmt state)]
      [(eq? (pre_op stmt) 'return) 'return]
      [(eq? (pre_op stmt) 'if) (M_if stmt state)]
      [(eq? (pre_op stmt) 'while) (M_while stmt state)]
      [else (error 'badop "Invalid statement")])))

; Evaluates the state after a sequence of statements
(define M_statementlist
  (lambda (stmt state)
    (if (null? (next_stmt stmt))
        (M_statement (curr_stmt stmt) state)
        (M_statementlist (next_stmt stmt) (M_statement (curr_stmt stmt) state)))))
