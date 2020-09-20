#lang racket
(provide (all-defined-out) (all-from-out "tools.rkt" racket/pretty))
(require "tools.rkt" racket/pretty)
(print-as-expression #f)
(pretty-print-abbreviate-read-macros #f)
(define-syntax example
  (syntax-rules ()
    ((_ e) (begin (newline)
                  (pretty-print 'e)
                  (displayln "==>")
                  (pretty-print e)))))
(define-syntax examples
  (syntax-rules ()
    ((_ e ...) (begin (example e) ...))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples
(define-relation (appendo ab c abc)
  (conde
    ((== '() ab) (== c abc))
    ((fresh (a b bc)
       (== `(,a . ,b) ab)
       (== `(,a . ,bc) abc)
       (appendo b c bc)))))



(define-relation (reverseo ys sy)
  (conde
    ((== '() ys) (== '() sy))
    ((fresh (first rest prefix)
       (== `(,first . ,rest) ys)
       ;; With a typical search strategy, there is no refutationally complete
       ;; ordering of the following two goals.  This ordering works well when
       ;; running in the forward direction, but not in the backward direction.
       (reverseo rest prefix)
       (appendo prefix `(,first) sy)))))


;; A miniscule relational interpreter.
(define-relation (evalo expr env value)
  (conde
    ((== `(quote ,value) expr))

    ((fresh (index)
       (== `(var ,index) expr)
       (lookupo index env value)))

    ((fresh (a d va vd)
       (== `(cons ,a ,d) expr)
       (== `(,va . ,vd) value)
       (evalo a env va)
       (evalo d env vd)))))

;; Variables are represented namelessly using relative De Bruijn indices.
;; These indices are encoded as peano numerals: (), (s), (s s), etc.
(define-relation (lookupo index env value)
  (fresh (arg e*)
    (== `(,arg . ,e*) env)
    (conde
      ((== '() index) (== arg value))
      ((fresh (i* a d)
         (== `(s . ,i*) index)
         (== `(,a . ,d) e*)
         (lookupo i* e* value))))))

