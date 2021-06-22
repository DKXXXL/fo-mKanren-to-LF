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
(define basic-test-cases
  (list-reflective
    (run 1 (a) (conj* (stringo a) (for-all (z) (not-stringo a))))
    (run 1 () (for-all (v) (disj* (== v 1) (=/= v 1) (== v 2))))
    (run 1 (a b) (for-all (z) (disj* (== z a) (=/= z b))))
    (run 1 (a) (for-all (z) (== z a)))
    (run 1 () (for-all (z) (fresh (x) (== z x))))
    (run 1 (q) (for-all (x) (=/= q (cons 1 x))))

    (run 1 (q) (fresh (a b) (== q (cons a b)) (for-all (x) (=/= (cons x x) (cons a b))) ))

  ))

;;; 5.2 Basic Implication Test
(define basic-implication
  (list-reflective
    (run 1 ()  (for-all (a b) (cimpl (conj* (== b a) (symbolo a)) (=/= b 1))) )
    (run 1 ()  (for-all (x z) (cimpl (conj (== x z)(False z)) 
                                   (False x))))
    (random-goal (A)
      (run 1 ()  (cimpl 
                    (fresh (x) (disj A (=/= x x)))
                    A)))
    (random-goal (A B C D E X Z)
      (run 1 ()  (cimpl 
                      (conj* 
                        (A . cimpl . B)
                        (B . cimpl . C)
                        (C . cimpl . D)
                        (Z . cimpl . D)
                        (D . cimpl . E) 
                        (X . cimpl . E))
                      (A . cimpl . E)) ))
    (random-goal (A)
      (run 1 ()  (cimpl 
                      (conj* 
                        (for-all (x) ((False x) . cimpl . A))
                        (False 1))
                      A)))
    (random-goal (A)
      (run 1 ()  (cimpl 
                      (conj* 
                        (for-all (x) ((False x) . cimpl . A))
                        (fresh (k) (False k)))
                      A)))

    
  ))


;;; 5.5 other tests
(define customized-relate-cases
  (list-reflective
    (run 1 (x) (for-all (b) (has-false (list b b x)))) 
    (run 1 (a) 
      (for-all (x) (sort-boolo (list #f #f x) (list a #f x))))
    (run 1 () (for-all (a) 
      (cimpl (membero #f (list a)) 
             (== a #f))
    ))
    (run 3 (o) (for-all (x) (sort-boolo-base-case (list x #f #f #f) (list #f #f #f x) o)))
    (run 1 () (for-bound (x) [boolo x] (sort-boolo (list #f x #f) (list #f #f x))))
  (run 1 () (for-all (x1 x2) 
    (fresh (r1 r2)
      (sort-two-boolo (list x1 x2) (list r1 r2))
      (disj* (conj* (=/= x1 #f) (=/= x2 #f))
             (== r2 #f)))))
  (run 1 (q) (filter p q (list)))
  (run 1 (z) (neg (zeros z)))
  ))



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
  (printf "Basic Demos\n")
  (print-table (run-demos basic-test-cases)
    #:border-style 'latex )

  (printf "Basic Implication Demos")
  (print-table (run-demos basic-implication)
    #:border-style 'latex )
  
  (printf "Evalo Demos\n")
  (print-table (run-demos test-cases-evalo)
    #:border-style 'latex )

  (printf "Graph Reachability Demos\n")
  (print-table (run-demos test-cases-graph-reachable)
      #:border-style 'latex )

  (printf "Other Customized Relation Demos\n")
  (print-table (run-demos customized-relate-cases)
      #:border-style 'latex )
)

