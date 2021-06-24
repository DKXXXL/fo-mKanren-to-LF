#lang errortrace racket

(require "tests-fo-LF.rkt")
(require "microk-fo-def.rkt")

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
  (let* (
         [greeks (map grk '("\\alpha" "\\beta" "\\gamma" "\\delta" "\\epsilon"))]
        [l (length greeks)]
        [query-by-index (λ (t) (list-ref greeks (modulo t l)))])
    (λ (i)
      (query-by-index i))))

(struct ppair    (a b)
  #:transparent               
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a,~a)" (ppair-a val) (ppair-b val)))]
     ;;; L stands for Lisp Elements
)


(define/contract (hijack-ppair goal)
  (Goal? . -> . Goal?)
  (define (each-case rec-parent rec g)
    (match g
      [(relate _ _) g] 
      [(cons a b) (ppair (rec a) (rec b))]
      [o/w (rec-parent g)]
    )
  )
  (define result-f 
    (compose-maps (list each-case goal-term-base-map pair-base-map state-base-endo-functor hash-key-value-map identity-endo-functor))
  )
  (result-f goal)
)


(define (into-goal goal-or-procedure i)
  (if (procedure? goal-or-procedure)
    (into-goal (goal-or-procedure (query-var i)) (+ i 1))
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
    ((_ n body ...) (cons (hijack-ppair (into-goal (curry-λ body ...) 0)) (thunk (run n body ...))))))


(define-syntax demo-unhalt
  (syntax-rules ()
    ((_ n body ...) 
    (cons (hijack-ppair (into-goal (curry-λ body ...) 0)) 
          (thunk 'TOO-MUCH-TIME )))))


;;; 5.1 basic test -- (forall (x) (disj (== x 1) (=/= x 1)))
(define constructive-negation-tests-1
  (list-reflective
      (demo-run 1 (q) (for-all (x) (== x q)))
      (demo-run 1 (q) (for-all (x) (fresh (y) (== x y))))
      (demo-run 1 (q) (for-all (x) (fresh (y) (== x y) (== y q))))
      (demo-run 1 (q) (for-all (x) (== q (cons 1 x))))
      (demo-run 1 (q) (for-all (x) (fresh (y) (== y (cons 1 x)))))
      (demo-run 1 (q) (for-all (x) (fresh (y) (== x (cons 1 y)))))
      (demo-run 1 (q) (for-all (x) (=/= x q)))
      (demo-run 1 (q) (for-all (x) (fresh (y) (=/= x y))))
      (demo-run 1 (q) (for-all (x) (fresh (y) (=/= x y) (== y q))))
      (demo-run 1 (q) (for-all (x) (=/= q (cons 1 x))))
      (demo-run 1 (q) (conj* (fresh (x) (== q (cons 1 x))) (for-all (x) (=/= q (cons 1 x)))))
      (demo-run 1 (q) (for-all (x) (=/= (cons x x) (cons 0 1))))
      (demo-run 1 (q) (for-all (x) (=/= (cons x x) (cons 1 1))))
      (demo-run 1 (q) (for-all (x) (=/= (cons x x) (cons q 1))))
      (demo-run 1 (q) (fresh (a b) (== q (cons a b)) (for-all (x) (=/= (cons x x) (cons a b))) ))
;;; Above From Constructive Negation Test
    ;;; unhalting
      
  )

)


;;; 
(define test-cases-constructive-negation-others
  (list-reflective
    (demo-run 1 () (unreachable 'c 'a))
    (demo-run 1 () (reachable 'c 'a))
    (demo-run 1 (z) (unreachable 'c z))
    (demo-run 1 (z) (unreachable 'd z))
    (demo-run 1 (z) (unreachable z 'a))
    (demo-run 1 (z) (unreachable z 'b))
    (demo-run 1 (z) (unreachable z 'c))

    (demo-run 1 () (winning 'c))
    (demo-run 1 () (winning 'd))
    (demo-unhalt 1 () (winning 'a))
    (demo-unhalt 1 () (winning 'b))

    (demo-unhalt 1 (q) (filter-singleton q (list 1)))
    
  ))


(define basic-test-cases
  (list-reflective


      (demo-run 1 ()  (for-all (z) (fresh (x y) (== (cons z y) x))))
      (demo-run 1 () (for-all (v) (disj* (== v 1) (=/= v 1) (== v 2))))
      (demo-run 1 () (fresh (a b) (for-all (v)  (disj* (== v a) (=/= v b)))))
      (demo-run 1 () (fresh (a b) (for-all (v) (conj (== v a) (=/= v b)) (=/= v v))))
      (demo-run 1 (a) (conj* (stringo a) (for-all (z) (not-stringo a))))
      (demo-run 1 () (for-all (v) (disj* (== v 1) (=/= v 1) (== v 2))))
      (demo-run 1 (a b) (for-all (z) (disj* (== z a) (=/= z b))))
    
    (demo-run 1 (R) (for-all (x y) (disj (disj (=/= y (cons 'a 'b)) (=/= x y) ) (== y R ))))
  

  ))

;;; This goal can only be satisfied from outside
;;; Opaque-Goal = False
(define Opaque-Goal
  (let* ([c 0])
    (λ ()
    (let* ([k (string->symbol (format "Loop~a" c))]
           [_ (set! c (+ c 1))])
    (letrec ([g (λ () (relate (λ () (fresh () (g)) ) `(,k))) ])
      (g)
    )
  )))
)

(define (ciff X Y) (conj (cimpl X Y) (cimpl Y X)))

(define-syntax random-goal
  (syntax-rules ()
    ((_ (x ...) g0 gs ...)
     (let ((x (Opaque-Goal)) ...)  (conj* g0 gs ...)))))

;;; 5.2 Basic Implication Test
(define basic-implication
  (list-reflective
    (demo-run 1 (a b)  (cimpl (== a 1) (== a b)))
    (demo-run 1 ()  (for-all (a b) (cimpl (conj* (== b a) (symbolo a)) (=/= b 1))) )
    (demo-run 1 ()  (for-all (a) (cimpl (== a 1) (symbolo a))))
    (demo-run 1 ()  (for-all (x z) (cimpl (conj (== x z)(False z)) 
                                   (False x))))   
    (demo-run 1 (R) (for-all (x y) (cimpl (conj (== y (cons 'a 'b)) (== x y) ) (== y R ))))
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
                        (fresh (k) (False k)))
                      A)))
    (demo-run 1 () (cimpl (neg (winning 'a)) (winning 'b)))
    (demo-run 1 () (cimpl (cimpl (winning 'd) (Bottom)) (Bottom) ))
    (demo-unhalt 1 () (cimpl (winning 'c) (Bottom)))
    
  ))


;;; 5.5 other tests
(define customized-relate-cases
  (list-reflective
    ;;; (demo-run 1 (x) (for-all (b) (has-false (list b b x)))) 

    (demo-run 1 () (for-all (x) (sort-boolo (list #f x #f) (list #f #f x))))   
    (demo-run 1 () (cimpl (for-all (x) (sort-boolo (list x #f) (list x #f))) (Bottom)))
    ;;; (demo-run 1 (x) (cimpl (sort-boolo (list x #f) (list x #f)) (Bottom)))

    ;;; (demo-run 1 () (for-all (x) (sort-boolo (list #f x #f #f) (list #f #f #f x))))   
    ;;; (demo-run 1 () (cimpl (for-all (x) (sort-boolo (list x #f #f) (list x #f #f))) (Bottom)))

    ;;; (demo-run 1 () (for-all (a) 
    ;;;   (cimpl (membero #f (list a)) 
    ;;;          (== a #f))
    ;;; ))
    ;;; (demo-run 1 (o) (for-all (x) (sort-boolo-base-case (list x #f #f #f) (list #f #f #f x) o)))
  ;;; (demo-run 1 () (for-all (x1 x2) 
  ;;;   (fresh (r1 r2)
  ;;;     (sort-two-boolo (list x1 x2) (list r1 r2))
  ;;;     (disj* (conj* (=/= x1 #f) (=/= x2 #f))
  ;;;            (== r2 #f)))))
  ;;; (demo-run 1 (q) (filter p q (list)))
  ;;; (demo-run 1 (z) (neg (zeros z)))
  ))

(define idf (caaar (run 1 (z) (evalo `(lambda (var ())) z))))

(define test-cases-evalo
  (list-reflective
    ;;; eigen cannot do this!
    
    (demo-run 1 (x z) (for-all (y) (evalo `(app ,x (quote ,y)) z)))
    
    (demo-run 1 (x) (for-all (y) (evalo `(app ,x (quote ,y)) y)))
    

    (demo-run 4 (x) (cimpl (evalo omega idf)
                           (evalo `(app ,omega ,omega) x)))

    (demo-unhalt 1 (z) 
      (cimpl (evalo `(cons ,omega '6) (cons idf 6)) 
             (evalo omega z)))

    ;;; (demo-run 1 (q) (cimpl (evalo q q)
    ;;;               (fresh (t) (evalo q t) (evalo t q))))
    
    ;;; type constraint, disequality
    ;;;   we want more forall example that eigen cannot do
    ;;;  

  ))



;;; make test-suite into one general



(define/contract (escape-latex s)
  (string? . -> . string?)
  (define specials `("#" "_"))
  
  (for/fold 
    ([acc s])
    ([each specials])
    (string-replace acc each (string-append "\\" each))
  )

)

(define (run-demos ds)
  (define result 
    (for/fold 
          ([acc '()])
          ([each-demo ds])
      (match-let* 
        ([(cons content thunk) each-demo]
        ;;;  [_ (printf "~a\n" content)]
         [latex-content (escape-latex (format "$~a$" content))])
          (match-let*-values
            ([((cons result _) _ realtime _) (time-apply thunk '())]
             [(realtime) (if (equal? result 'TOO-MUCH-TIME) 'N/A realtime)]
             [(latex-result) (format "$~a$" result)]
             [(latex-result-escape) (escape-latex latex-result)]
             )
            (cons (list latex-content latex-result-escape realtime) acc))
  )))
(cons (list 'Query 'Result "Time (ms)") (reverse result))
)


(module+ test
  (require rackunit/text-ui)
  (set-debug-info-threshold! 1)
  ;;; (run-tests all-tests)
  (printf "Constructive Negation Related\n")
  (printf "Constructive Negation Examples\n")
  (print-table (run-demos constructive-negation-tests-1)
    #:border-style 'latex )

  (printf "Constructive Negation Complicated Examples\n")
  (print-table (run-demos test-cases-constructive-negation-others)
      #:border-style 'latex )

  (printf "Basic Demos\n")
  (print-table (run-demos basic-test-cases)
    #:border-style 'latex )

  (printf "Basic Implication Demos\n")
  (print-table (run-demos basic-implication)
    #:border-style 'latex )
  
  (printf "Evalo Demos\n")
  (print-table (run-demos test-cases-evalo)
    #:border-style 'latex )



  (printf "Other Customized Relation Demos\n")
  (print-table (run-demos customized-relate-cases)
      #:border-style 'latex )
)

