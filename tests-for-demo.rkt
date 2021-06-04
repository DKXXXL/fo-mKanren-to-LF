#lang errortrace racket

(require "tests-fo-LF.rkt")

(require rackunit)

;;; https://docs.racket-lang.org/text-table/index.html
(require text-table)

(provide
  (all-defined-out)
  (all-from-out "tests-fo-LF.rkt")
  (all-from-out text-table)
)

(define-syntax list-reflective
  (syntax-rules ()
    ((_ ) (list))
    ((_ l x ...) 
      (cons (cons 'l (λ () l))
        (list-reflective x ...)
      ))))

;;; each test suite
(define test-cases-graph-reachable
  (list-reflective
    (run 1 () (unreachable 'c 'a))
    (run 1 () (reachable 'c 'a))
    (run 1 (z) (unreachable 'c z) (node z))
  ))


;;; make test-suite into one general
(define all-demos
  (append 
    test-cases-graph-reachable
  ))

(define (run-demos ds)
  (define result 
    (for/fold 
          ([acc '()])
          ([each-demo ds])
      (match-let* 
        ([(cons content thunk) each-demo])
          (match-let*-values
            ([((cons result _) _ realtime _) (time-apply thunk '())])
            (cons (list content result realtime) acc))
  ))
)
result
)


(module+ test
  (require rackunit/text-ui)
  (set-debug-info-threshold! 1)
  ;;; (run-tests all-tests)
  (print-table (run-demos all-demos)
      #:border-style 'latex 
  )
  ;;; (profile-thunk (thunk (run-tests all-tests)))
)

