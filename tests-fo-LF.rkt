#lang racket

(require "mk-fo.rkt")
(require errortrace)
;;; (require "examples-for-test.rkt")

(provide
  (all-defined-out)
)

(display "Running first-order-microKanren-LF tests:")
(newline)


(define all-tests-table (make-hash))
;;; global mutable-context for hashing
;;; hash : maps symbol to (closure of) test-cases

(define blue-colour "\033[94m")
(define blue-colour-end "\033[0m")
(define-syntax test
  (syntax-rules ()
    ((_ name e-actual e-expected)
     (time (begin
             (printf "Testing ~a ~s: \n  ~s ~a \n  \n ==> " 
                      blue-colour name 'e-actual blue-colour-end)
             (let* ((actual e-actual) 
                   (expected e-expected)
                   (checker-func 
                      (match expected 
                        ['succeed (lambda (x) (not (null? x)))]
                        ['fail null?]
                        [o/w (lambda (x) (equal? x expected))]
                      ))
                   )
               (if (checker-func actual)
                 (printf "\n ~s " 'success)
                 (printf "FAILURE\nEXPECTED: ~s\nACTUAL: ~s\n"
                         expected actual))
                         
             ))))))

(define-syntax test-reg!
  (syntax-rules ()
    ((_ name e-actual e-expected)
     (define name
          (let* ([x (lambda () (test 'name e-actual e-expected))]
                [reg! (hash-set! all-tests-table 'name x)])
            'name)))
    ((_ e-actual e-expected)
          (let* ([name (gensym '?)]
                 [x (lambda () (test name e-actual e-expected))]
                 [reg! (hash-set! all-tests-table name x)])
            reg!))
 ))

(define-syntax test-reg!=>
  (syntax-rules ()
    ((_ name e-actual e-expected) (test-reg! name e-actual e-expected))
    ((_ e-actual e-expected) (test-reg! e-actual e-expected))
    ))

(define run-1-succeed (run 1 () (== 1 1)))
(define run-1-fail (run 1 () (== 1 2)))

;;; type constraint sanity check

((run 1 ()  (fresh (x) (symbolo x)))
  . test-reg!=> . 'succeed  
)

((run 1 ()  (fresh (x) (stringo x)))
  . test-reg!=> . 'succeed  
)

((run 1 ()  (fresh (x) (symbolo x) (stringo x)))
  . test-reg!=> . 'fail  
)

((run 1 ()  (fresh (x y) (== x y) (symbolo x) (numbero y)))
  . test-reg!=> . 'fail  
)

((run 1 ()  (fresh (x y) (== x (cons 1 1)) (symbolo x)))
  . test-reg!=> . 'fail  
)

((run 1 ()  (fresh (x) (disj* (symbolo x) (stringo x))))
  . test-reg!=> . 'succeed  
)


;;; Sanity Check

(test-reg! Identity
  (run 1 () (for-all (y) (fresh (x) (== y x))))
  run-1-succeed
)


(test-reg! NEQPair
  (run 1 () (fresh (y) (for-all (x) (=/= y (cons x 3)))))
  run-1-succeed
)

(test-reg! NEQAll
  (run 1 () (fresh (y) (for-all (x) (=/= y x))))
  run-1-fail
)

(test-reg! NEQPair-All
  (run 1 () (fresh (y) (for-all (x) (=/= (cons y 3) (cons x 3)))))
  run-1-fail
)


(test-reg! Trivial-contradiction-1
  (run 1 () (for-all (y) (fresh (x) (== y x) (=/= y x))))
  run-1-fail
)

(test-reg! Trivial-contradiction-2
  (run 1 () (for-all (y) (for-all (x) (== y x) (=/= y x))))
  run-1-fail
)

(test-reg! Trivial-Disjunction-1
  (run 1 () (for-all (y) (for-all (x) (disj* (== y x) (=/= y x)))))
  run-1-succeed
)


(test-reg! Trivial-Disjunction-2
  (run 1 () (fresh (y) (for-all (x) (disj* (== y x) (=/= y x)))))
  run-1-succeed
)


;;; complicated check

(define-relation (appendo xs ys xsys)
  (conde ((== xs '()) (== ys xsys))
         ((fresh (x zs zsys)
            (== `(,x . ,zs)   xs)
            (== `(,x . ,zsys) xsys)
            (appendo zs ys zsys)))))



(define-relation (boolo a)
  (disj* (== a #t) (== a #f)))

(define-relation (not-pairo a)
  (for-all (x y) (=/= a (cons y x))))


(define-relation (not-symbolo a)
  (complement (symbolo a)))

(test-reg! finite-domain-exhaustion
  (run 1 (a b c) (=/= a b) (=/= b c) (=/= a c) (boolo a) (boolo b) (boolo c))
  run-1-fail
)

;; a is every pair
(test-reg! AllThePair
  (run 1 (a) (for-all (x y) (== a `(,x . ,y))))
  run-1-fail
)

(test-reg! AllSymbol
  (run 1 () (for-all (x) (symbolo x)))
  run-1-fail
)


(test-reg! Trivial-Disjunction-Symbol
  (run 1 () (for-all (y) (disj* (symbolo y) (not-symbolo y) )))
  run-1-succeed
)

;;; BUGFIX: the following currently unhalt 
;;;   if set to run*
;;; BUGFIX: change the following into two runs
;;;   each check one of (not-pairo) and (identity pair)
((run 1 (a) 
  (conj* 
    (for-all (x y) (disj* (=/= x y) ;; this =/= adds no information, but shouldn’t break
                          (=/= a `(,x . ,y))
                          (conj* (== a `(,x . ,y)) (== x y))))
    (disj* (not-pairo a) (fresh (z) (== a (cons z z))))))

;;; ((not-pairo a) (_.0 . _0) ...)
. test-reg!=> . 'succeed
)

((run 1 (a) 
  (conj* 
    (for-all (x) (=/= a `(,x . ,x)))
    (disj* (not-pairo a) (fresh (m n) (=/= m n) (== a (cons m n))))
    ))

;;; ((not-pairo a) [(_.0 . _.1) where (=/= _.0 _.1)] …)
. test-reg!=> . 'succeed
)


;;; this unhalt even set to 1
(Complicated-1
  (run 1 (a) 
  (conj* 
    (for-all (x y) 
      (disj* (symbolo x) ;; this symbolo adds no information
            (=/= a `(,x . ,y))
            (conj* (== a `(,x . ,y)) (not-symbolo x))))
    (disj* (not-pairo a) 
           (fresh (m n) (not-symbolo m) (== a (cons m n)) ))))
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed 
)

;;; this unhalt even set to 1
;; x is not a pair whose car is a symbol
;;; ((run 1 (a) 
;;;   (conj*  
;;;     (for-all (x y) 
;;;       (disj* (symbolo x) ;; this symbolo adds no information
;;;               (=/= a `(,x . ,y))
;;;               (conj* (== a `(,x . ,y)) (not-symbolo x)))))
;;;     (disj* (not-pairo a) (not-symbolo a)))

;;; ;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
;;; . test-reg!=> . 'succeed
;;; )

;;; the above currently unhalt if set to run*

((run* (a) 
  (for-all (x y) (disj* 
                        (=/= a x) 
                        (conj* (== a x) (== x y)))))
;;; ()
. test-reg!=> . 'fail
)




((run 1 (a b)
  (conj*
    (for-all (x)
      (=/= (cons a b) (cons x 3)))
    (=/= b 3)    
  ))

;;; ((=/= b 3) …)
. test-reg!=> . 'succeed
)

((run 6 (a b)
  (conj*
    (for-all (x)
      (disj* (conj* (== a x)            ;; complement of (=/= a x)
                        (disj* (=/= a x)  ;; this branch will fail
                                  (=/= b 3)))
            (=/= b 3))))
    (=/= b 3))

;;; ((=/= b 3) …)
. test-reg!=> . 'succeed
)


; Universally quantified: x, y, z
; Outside of the for-all: a, b, c
; Inside of the for-all: r, s, t
((run 1 () (for-all (x) (== x x))) . test-reg!=> . 'succeed)
((run 1 (a) (for-all (x) (== x a))) . test-reg!=> . 'fail)
((run 1 (a) (for-all (x) (fresh (s) (== a s)))) . test-reg!=> . 'succeed)
((run 1 (a) (for-all (x) (fresh (s) (== x s)))) . test-reg!=> . 'succeed)
((run 1 (a) (for-all (x) (fresh (s t) (== s `(,x . ,t))))) . test-reg!=> . 'succeed)




((run 1 (a b) (for-all (x) 
  (disj (=/= x a) (=/= x b)))) . test-reg!=> . 'succeed)
; closed world: removing any of the disjuncts should fail
((run 1 () (for-all (x) 
  (disj* (symbolo x) (numbero x) (stringo x)
         (== x #t) (== x #f) 
         (fresh (r s) (== x (cons r s)))))) . test-reg!=> . 'succeed)
; cons + car/cdr: all these should 'succeed
((run 1 () 
(for-all (x) 
  (fresh (r) 
    (disj* (fresh (s t) (=/= x (cons s t))) ; x not a pair
          (fresh (s t) (== x (cons s t))))))) . test-reg!=> . 'succeed) ; x is a pair
; different ways of encoding a “pairo” like constraint
((run 1 () (for-all (x)
   (disj* (not-pairo x) (fresh (s t) (== x (cons s t))))))
   . test-reg!=> . 'succeed
   )
; Using relations
((run 1 () (for-all (x) (fresh (r s)
    (disj* (=/= (cons x r) s)
           (appendo (list x) r s))))) 
  . test-reg!=> . 'succeed )
;; not supported yet:
;(run 1 () (for-all (x) (fresh (r s)
;    (implies (appendo (list x) r s)
;             (== (cons x r) s))))

;; a fancy/possibly-slow way of saying (=/= a b)
((run 1 (a b)
  (for-all (x) (disj* (=/= a x) (=/= b x))))
. test-reg!=> . 'succeed  
)


((run 1 (c a b) (for-all (x) (=/= c (cons a (cons b x)))))
. test-reg!=> . 'succeed)
((run 1 (c a b) (for-all (y) (=/= c (cons a (cons b y)))) )
. test-reg!=> . 'succeed)
((run 1 () (for-all (x) (=/= x (cons x x))))
. test-reg!=> . 'succeed)
((run 1 (a) (for-all (y) (disj* (numbero a) (stringo a))))
. test-reg!=> . 'succeed)
((run 1 () (for-all (z) (fresh ( r ) (=/= r z) (numbero r))))
. test-reg!=> . 'succeed)
;;; ((run 1 () (for-all-bound (z) [numbero z] (=/= z (cons 1 2))))
;;; . test-reg!=> . 'succeed)
;;; ((run 1 () (for-all-bound (z) [stringo z] (=/= z (cons 1 2))))
;;; . test-reg!=> . 'succeed)
;;; ((run 1 () (for-all-bound (z) [symbolo z] (=/= z (cons 1 2))))
;;; . test-reg!=> . 'succeed)
;;; ((run 1 () (for-all-bound (z) [(for-all-bound (x) (== x z))] (Bottom)) )
;;; . test-reg!=> . 'succeed)
;;; ((run 1 () (for-all-bound (z) [(for-all-bound (x) (=/= x z))] (Bottom)) )
;;; . test-reg!=> . 'succeed)

(define (run-all-tests)
  (hash-for-each all-tests-table 
    (lambda (key value) (value))))


(define-syntax run-the-test
  (syntax-rules ()
    ((_ name)
     ((hash-ref all-tests-table 'name)) )
 ))

;;; (run-all-tests)
