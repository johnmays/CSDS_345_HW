#lang racket

(define state_vars car)
(define state_vals cadr)
(define empty_state '(()()))

; Testing methods stuff
(define a_methods '(methoda1 methoda2 methoda3))
(define b_methods '(methodb1 methodb2 methodb3))

; Suppose class B extends class A...
; The closure for B should contain (methodb1 methodb2 methodb3 methoda1 ...) as its overall methods
(define merge_methods
  (λ (am bm)
    (append bm am)))

; Testing instance field stuff
(define a_fields '((ai1 ai2 ai3) (1 2 3)))
(define b_names '(bi1 ai2 bi3))
(define b_vals '(4 5 6))

; Again, suppose class B extends class A...
; From the advice given in class, the instance fields for b will be given by (b1 a2 b3 a1 a2 a3) - note the duplicate a2
; But the values will be reversed, so the values are given by (3 2 1 6 5 4)
; a1 = 1, a2 = 2, a3 = 3, and so on...
(define merge_instance_values
  (λ (af bn bv)
    (list (append bn (car af)) (reverse (append bv (cadr af))))))

; Querying b.a1 should yield the value of 5
; The state will still look like ((var names) (var vals)), except the vals are reversed. This is called whenever we
; need to look through the instance variables, because the requested variable couldn't be found elsewhere
(define find_instance_var
  (λ (name state)
    (list-ref (state_vals state) (get_idx name (state_vars state)))))

(define get_idx
  (λ (name var_names)
    (cond
      [(null? var_names) (error 'varerror "Variable not declared: ~a" name)]
      [(eq? name (car var_names)) (- (length var_names) 1)]
      [else (get_idx name (cdr var_names))])))