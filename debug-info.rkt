#lang errortrace racket
(provide 
  (all-defined-out))

(require racket/contract)
(require errortrace)

;;; set the following to 'ON then we will have debug info
(define debug-output-info 'ON)


(define (debug-info-initialization)
  (define debug-info-threshold 
    (if (equal? debug-output-info 'ON) -100 1))
  (define (get-debug-info-threshold)
    debug-info-threshold)

  (define (set-debug-info-threshold! l)
    (set! debug-info-threshold l))
  
  (values get-debug-info-threshold set-debug-info-threshold!)
)

(define-values 
  (get-debug-info-threshold set-debug-info-threshold!)
  (debug-info-initialization))


(define-syntax debug-dump-w/level
  (syntax-rules ()
    ((_ l x ...) 
      (if (>= l (get-debug-info-threshold)) 
        (printf x ...)
        'Threshold-Too-High))
          ))
(define-syntax debug-dump-off
  (syntax-rules ()
    ((_ ...) 
      (void))))

(define-syntax debug-dump
  (syntax-rules ()
    ((_ x ...) 
      (debug-dump-w/level 0 x ...))))

(define-syntax raise-and-warn
  (syntax-rules ()
    ((_ x ...) 
      (begin (debug-dump-w/level 100 x ...) (/ 1 0)))))

