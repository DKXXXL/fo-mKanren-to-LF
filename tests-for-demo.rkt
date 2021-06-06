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

;;; 5.1 basic test -- (forall (x) (disj (== x 1) (=/= x 1)))

;;; 
(define test-cases-graph-reachable
  (list-reflective
    (run 1 () (unreachable 'c 'a))
    (run 1 () (reachable 'c 'a))
    (run 1 (z) (unreachable 'c z))
    (run 1 (z) (unreachable 'd z))
    (run 1 (z) (unreachable z 'a))
    (run 1 (z) (unreachable z 'b))
    (run 1 (z) (unreachable z 'c))
    
  ))

(define test-cases-evalo
  (list-reflective
    ;;; eigen cannot do this!
    (run 1 ()
     (cimpl 
      (evalo '6 5)
      (evalo omega 5)))
    
    (run 1 (x z) (for-all (y) (evalo `(app ,x (quote ,y)) z)))
    
    (run 1 (x) (for-all (y) (evalo `(app ,x (quote ,y)) y)))
    
    (run 1 (q) (cimpl (evalo q q)
                  (fresh (t) (evalo q t) (evalo t q))))
    
    ;;; type constraint, disequality
    ;;;   we want more forall example that eigen cannot do
    ;;;  

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
(cons (list 'Query 'Result 'Time-in-ms) result)
)


(module+ test
  (require rackunit/text-ui)
  (set-debug-info-threshold! 1)
  ;;; (run-tests all-tests)
  (printf "Graph Reachability Demos\n")
  (print-table (run-demos test-cases-graph-reachable)
      #:border-style 'latex )
  (printf "Evalo Demos\n")
  (print-table (run-demos test-cases-evalo)
      #:border-style 'latex )
)

