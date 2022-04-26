#lang racket

(define deepcopy
  (lambda (lis)
    (cond
      [(null? lis) '()]
      [(box? (car lis))
       (begin
         (define x (box (unbox (car lis))))
         (cons x (deepcopy (cdr lis))))]
      [else (cons (car lis) (deepcopy (cdr lis)))])))


(define lis (list '(a b) (list (box 2) (box 4))))
(define lis2 (deepcopy lis))
(set-box! (caadr lis) 23)
    
    