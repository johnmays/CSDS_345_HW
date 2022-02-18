#lang racket
(require "Homework2_temp.rkt")

(define initialized?
  (lambda (var state)
    (if (not (declared? var (car state)))
      #f
      (initialized_helper var (car state) (cadr state)))))

(define initialized_helper
  (lambda (var variables values)
    (cond
      [(null? variables) #f]
      [(and (eq? var (car variables)) (not (void? (car values)))) #t]
      [(and (eq? var (car variables)) (void? (car values))) #f]
      [else initialized_helper var (cdr variables) (cdr values)])))
    

(define M_return
  (lambda (state)
    (if (and (declared? 'return (car state)) (initialized? 'return state))
        (cond
           [(eq? (find_var 'return state) #t) 'true]
           [(eq? (find_var 'return state) #f) 'false]
           [else (find_var 'return state)])
        #f)))

; (define newstate (M_statement '(var return) '(()())))
(define newstate '((return a b c) (#t 2 3 4)))