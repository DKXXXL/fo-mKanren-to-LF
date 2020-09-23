#lang racket
(provide
  (all-from-out "common.rkt")
  (all-from-out "microk-fo-det.rkt")
  ==

  define-relation
  fresh
  conde
  query
  run
  run*

  run/trace
  run*/trace

  run/directed
  run*/directed

  stream-take
  stream-take/directed
  conj*
  disj*
  )
(require "common.rkt" "microk-fo-det.rkt")
(include "mk-syntax.rkt")

;;; Move run/trace to here because
;;;  mk-syntax.rkt is public common code

;;; (define-syntax run/trace
;;;   (syntax-rules ()
;;;     ((_ n body ...) (map (lambda (state)
;;;                            (list (reify/initial-var state)
;;;                                  (reverse (state-trace state))))
;;;                          (stream-take n (query body ...))))))

(define-syntax run/trace
  (syntax-rules ()
    ((_ n body ...) 
        (match-let* 
            ([streamq (query body ...)]
             [(pause _ prop-goal) streamq])
          (map (lambda (state)
                           (match-let* 
                              ([tr (reverse (state-trace state))])
                             (list (reify/initial-var state)
                                   tr
                                   (proof-term-construct tr state prop-goal)
                                 )))
                         (stream-take n streamq))))                       
  ))
(define-syntax run*/trace
  (syntax-rules () ((_ body ...) (run/trace #f body ...))))


;;;  use trace to do directed search
(define-syntax query/directed
  (syntax-rules ()
    ((_ direction (x ...) g0 gs ...)
     (let ((goal (fresh (x ...) (== (list x ...) initial-var) g0 gs ...)))
       (pause (empty-state/fuel direction) goal)))))


(define (stream-take/directed n s)
  (if (eqv? 0 n) '()
    (let ((s (mature/directed s)))
      (if (pair? s)
        (cons (car s) (stream-take/directed (and n (- n 1)) (cdr s)))
        '()))))

(define-syntax run/directed
  (syntax-rules ()
    ((_ direction n body ...) (map reify/initial-var (stream-take/directed n (query/directed direction body ...))))))


(define-syntax run*/directed
  (syntax-rules () 
    ((_ direction body ...) (run/directed direction #f body ...))))

