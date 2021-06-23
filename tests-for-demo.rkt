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

(define-syntax curry-λ
  (syntax-rules ()
    ((_ () body) 
        body)
    ((_ (x) body) 
        (λ (x) body))
    ((_ (x y ...) body) 
        (λ (x) (curry-λ (y ...) body)))))


(struct grk    (t1)
  #:transparent               
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a" (grk-t1 val)))]
     ;;; L stands for Lisp Elements
)


(define query-var
  (let* ([c 0]
        [greeks (map grk '("\\gamma" "\\alpha" "\\beta"))]
        [l (length greeks)]
        [query-by-index (λ (t) (list-ref greeks (modulo c l)))])
    (λ ()
      (set! c (+ c 1))
      (query-by-index c))))

(define (into-goal goal-or-procedure)
  (if (procedure? goal-or-procedure)
    (into-goal (goal-or-procedure (query-var)))
    goal-or-procedure
    ))

(define-syntax list-reflective
  (syntax-rules ()
    ((_ ) (list))
    ((_ l x ...) 
      (cons l
        (list-reflective x ...)
      ))))

(define-syntax demo-run
  (syntax-rules ()
    ((_ n body ...) (cons (into-goal (curry-λ body ...)) (thunk (run n body ...))))))


;;; 5.1 basic test -- (forall (x) (disj (== x 1) (=/= x 1)))
(define basic-test-cases
  (list-reflective
    (demo-run 1 (a) (for-all (z) (== z a)))
    (demo-run 1 ()  (for-all (z) (fresh (x) (== z x))))
    (demo-run 1 ()  (for-all (z) (fresh (x y) (== (cons z y) x))))


    (demo-run 1 () (for-all (v) (disj* (== v 1) (=/= v 1) (== v 2))))
    (demo-run 1 () (fresh (a b) (for-all (v)  (disj* (== v a) (=/= v b)))))
    ;;; (exists (a b) (for-all (v) (conj (== v a) (=/= v b)) (=/= v)))

    (demo-run 1 (q) (for-all (x) (=/= q (cons 1 x))))

    (demo-run 1 (a) (conj* (stringo a) (for-all (z) (not-stringo a))))
    (demo-run 1 () (for-all (v) (disj* (== v 1) (=/= v 1) (== v 2))))
    (demo-run 1 (a b) (for-all (z) (disj* (== z a) (=/= z b))))
    
    


    (demo-run 1 (q) (fresh (a b) (== q (cons a b)) 
               (for-all (x) (=/= (cons x x) (cons a b))) ))

  ))

;;; 5.2 Basic Implication Test
(define basic-implication
  (list-reflective
    (demo-run 1 ()  (for-all (a b) (cimpl (conj* (== b a) (symbolo a)) (=/= b 1))) )
    (demo-run 1 ()  (for-all (x z) (cimpl (conj (== x z)(False z)) 
                                   (False x))))
    (random-goal (A)
      (demo-run 1 ()  (cimpl 
                    (fresh (x) (disj A (=/= x x)))
                    A)))
    (random-goal (A B C D E X Z)
      (demo-run 1 ()  (cimpl 
                      (conj* 
                        (A . cimpl . B)
                        (B . cimpl . C)
                        (C . cimpl . D)
                        (Z . cimpl . D)
                        (D . cimpl . E) 
                        (X . cimpl . E))
                      (A . cimpl . E)) ))
    (random-goal (A)
      (demo-run 1 ()  (cimpl 
                      (conj* 
                        (for-all (x) ((False x) . cimpl . A))
                        (False 1))
                      A)))
    (random-goal (A)
      (demo-run 1 ()  (cimpl 
                      (conj* 
                        (for-all (x) ((False x) . cimpl . A))
                        (fresh (k) (False k)))
                      A)))

    
  ))


;;; 5.5 other tests
(define customized-relate-cases
  (list-reflective
    (demo-run 1 (x) (for-all (b) (has-false (list b b x)))) 
    (demo-run 1 (a) 
      (for-all (x) (sort-boolo (list #f #f x) (list a #f x))))
    (demo-run 1 () (for-all (a) 
      (cimpl (membero #f (list a)) 
             (== a #f))
    ))
    (demo-run 3 (o) (for-all (x) (sort-boolo-base-case (list x #f #f #f) (list #f #f #f x) o)))
    (demo-run 1 () (for-bound (x) [boolo x] (sort-boolo (list #f x #f) (list #f #f x))))
  (demo-run 1 () (for-all (x1 x2) 
    (fresh (r1 r2)
      (sort-two-boolo (list x1 x2) (list r1 r2))
      (disj* (conj* (=/= x1 #f) (=/= x2 #f))
             (== r2 #f)))))
  (demo-run 1 (q) (filter p q (list)))
  (demo-run 1 (z) (neg (zeros z)))
  ))



;;; 
(define test-cases-graph-reachable
  (list-reflective
    (demo-run 1 () (unreachable 'c 'a))
    (demo-run 1 () (reachable 'c 'a))
    (demo-run 1 (z) (unreachable 'c z))
    (demo-run 1 (z) (unreachable 'd z))
    (demo-run 1 (z) (unreachable z 'a))
    (demo-run 1 (z) (unreachable z 'b))
    (demo-run 1 (z) (unreachable z 'c))
    
  ))

(define test-cases-evalo
  (list-reflective
    ;;; eigen cannot do this!
    (demo-run 1 ()
     (cimpl 
      (evalo '6 5)
      (evalo omega 5)))
    
    (demo-run 1 (x z) (for-all (y) (evalo `(app ,x (quote ,y)) z)))
    
    (demo-run 1 (x) (for-all (y) (evalo `(app ,x (quote ,y)) y)))
    
    (demo-run 1 (q) (cimpl (evalo q q)
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
        ([(cons content thunk) each-demo]
         [latex-content (format "$~a$" content)])
          (match-let*-values
            ([((cons result _) _ realtime _) (time-apply thunk '())]
             [(latex-result) (format "$~a$" result)]
             [(latex-result-excape-underscore) (string-replace latex-result "_" "\\_")]
             )
            (cons (list latex-content latex-result-excape-underscore realtime) acc))
  )))
(cons (list 'Query 'Result "Time (ms)") (reverse result))
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

