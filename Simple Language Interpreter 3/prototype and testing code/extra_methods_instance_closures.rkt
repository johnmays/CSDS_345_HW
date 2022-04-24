#lang racket
(require "interpreter.rkt")

; Instance abstractions
(define instance_value caddr)
(define value_keyword caaddr)
(define instance_class cadr)

; Creates instance binding along with instance closure
(define add_instance
  (lambda (stmt state)
    (if (declared? (instance_class stmt) state)
        (make_instance_closure (instance_class stmt))
        (error 'instancerror "No such class has been declared."))))

;Creates a binding for instances.
(define M_instancedef
  (lambda (stmt state next)
    (add_instance stmt state)))
; COMMENT: I used to call next on add_instance, but I am testing not doing that any more.

  