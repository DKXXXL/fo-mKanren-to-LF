#lang racket

(require "mk-fo.rkt")
(require racket/format)
(require errortrace)
;;; (require "examples-for-test.rkt")

(require rackunit)

(provide
  (all-defined-out)
  (all-from-out "mk-fo.rkt")
)

;;; (display "Enabling code coverage, might hurt performance \n")
(instrumenting-enabled #t)
;;; (profiling-enabled (make-parameter #t))
;;; (profiling-record-enabled (make-parameter #t))
;;; (execute-counts-enabled (make-parameter #t))
;;; (coverage-counts-enabled (make-parameter #t))
;;; (printf "Profiling is ~a \n" (profiling-enabled))
;;; (get-execute-counts)


(define-values (total-tested-number 
                passed-tested-number
                inc-total-tested-number
                inc-passed-tested-number) 
  (let* (
    [total-tested-number-literal 0]
    [passed-tested-number-literal 0]
    [get-total (lambda () total-tested-number-literal)]
    [get-passed (lambda () passed-tested-number-literal)]
    [inc-total-tested-number 
      (lambda () 
        (set! total-tested-number-literal (+ total-tested-number-literal 1)))]
    [inc-passed-tested-number 
      (lambda () 
        (set! passed-tested-number-literal (+ passed-tested-number-literal 1)))])
  (values get-total get-passed inc-total-tested-number inc-passed-tested-number)      
  )
)

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

            ;;;  (inc-total-tested-number)
             (let* (
                   (actual e-actual) 
                   (str-name (~a name))
                   (expected e-expected)
                   (checker
                      (match expected 
                        ['succeed  (test-false str-name (null? actual))]
                        ['fail     (test-true str-name (null? actual))]
                        [o/w       (test-equal? str-name actual expected)]
                      ))
                   )
              ;;;  (if (checker-func actual)
              ;;;    (begin 
              ;;;       (inc-passed-tested-number) 
              ;;;       (printf "\n ~s " 'success))
              ;;;    (printf "FAILURE\nEXPECTED: ~s\nACTUAL: ~s\n"
              ;;;            expected actual))
              checker
                         
             ))))))

(define-syntax test-reg!
  (syntax-rules ( JUST-DECL )
    ((_ name e-actual e-expected)
     (define name
          (let* ([x (lambda () (test 'name e-actual e-expected))]
                 [reg! (hash-set! all-tests-table 'name x)])
            'name)))
    ((_ JUST-DECL name e-actual e-expected)
     (define name
          (let* ([x (lambda () (test 'name e-actual e-expected))])
            x)))
    ((_ e-actual e-expected)
          (let* ([name 'e-actual]
                 [x (lambda () (test name e-actual e-expected))]
                 [reg! (hash-set! all-tests-table name x)])
            reg!))
  
 ))

(define-syntax test-reg!=>
  (syntax-rules ()
    ((_ name e-actual e-expected) (test-reg! name e-actual e-expected))
    ((_ e-actual e-expected) (test-reg! e-actual e-expected))
    ))

(define-syntax test-reg!=>X
  (syntax-rules ()
    ((_ name e-actual e-expected) (printf "\n Skipping as currently failed ~a ~a => ~a " 'name 'e-actual 'e-expected) )
    ((_ e-actual e-expected) (printf "\n Skipping as currently failed ~a => ~a " 'e-actual 'e-expected) )
    ))

(define-syntax test-reg!=>ND ;; won't be runned during testing, just declared
  (syntax-rules ()
    ((_ name e-actual e-expected) (test-reg! JUST-DECL name e-actual e-expected))
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

((run 1 ()  (fresh (x) (not-stringo x)))
  . test-reg!=> . 'succeed  
)


(Easy-failing
  (run 1 ()  (fresh (x) (symbolo x) (not-symbolo x)))
  . test-reg!=> . 'fail  
)

(Easy-failing-2
  (run 1 ()  (fresh (x) (stringo x) (not-stringo x)))
  . test-reg!=> . 'fail  
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

(Input-pair-incorrect
  (run 1 (xs ys) (for-all (k) (== xs 4)))
  . test-reg!=> . 'succeed
)

;;; complicated check

(define-relation (appendo xs ys xsys)
  (conde ((== xs '()) (== ys xsys))
         ((fresh (x zs zsys)
            (== `(,x . ,zs)   xs)
            (== `(,x . ,zsys) xsys)
            (appendo zs ys zsys)))))



(define (boolo a)
  (disj* (== a #t) (== a #f)))

(define-relation (not-pairo a)
  (for-all (x y) (=/= a (cons y x))))


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

(test-reg! Trivial-Disjunction-Number
  (run 1 () (for-all (y) (disj* (numbero y) (not-numbero y) )))
  run-1-succeed
)


;;; BUGFIX: the following currently unhalt 
;;;   if set to run 1
;;; BUGFIX: change the following into two runs
;;;   each check one of (not-pairo) and (identity pair)
(Complicated-3
  (run 1 (a) 
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


(Complicated-1
  (run 1 (a) 
  (conj* 
    (for-all (x y) 
      (disj* (symbolo x) ;; this symbolo adds no information
            (=/= a `(,x . ,y))
            (conj* (== a `(,x . ,y)) (not-symbolo x))))
    (disj* (not-pairo a) 
           (fresh (m n) (not-symbolo m) (== a (cons m n)) ))
           ))
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed 
)

;;; this unhalt even set to 1
;; x is not a pair whose car is a symbol
(Complicated-2
  (run 1 (a) 
  (conj*  
    (for-all (x y) 
      (disj* (symbolo x) ;; this symbolo adds no information
              (=/= a `(,x . ,y))
              (conj* (== a `(,x . ,y)) (not-symbolo x)))))
    (disj* (not-pairo a) (not-symbolo a)))

;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed
)

(Complicated-4
  (run 1 (a) 
    (for-all (x y) 
      (disj* 
            (symbolo x) ;; this symbolo adds no information
            (=/= a `(,x . ,y))
            (conj* 
                   (== a `(,x . ,y)) 
                   (not-symbolo x)
                   )
            )) )
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed 
)

(Complicated-4-1
  (run 1 (a) 
    (for-all (x y) 
      (disj* 
            ;;; (symbolo x) ;; this symbolo adds no information
            (=/= a `(,x . ,y))
            (conj* 
                   (== a `(,x . ,y)) 
                   (not-symbolo x)
                   )
            )) )
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed 
)


(Complicated-4-1-1
  (run 1 (a) 
    (for-all (x y) 
      (disj* 
            ;;; (symbolo x) ;; this symbolo adds no information
            (=/= a `(,x . ,y))
            (conj* 
                   (== a `(,x . ,y)) 
                  ;;;  (not-symbolo x)
                   )
            )) )
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed 
)

(Complicated-4-1-2
  (run 1 (a) 
    (for-all (x y) 
      (disj* 
            ;;; (symbolo x) ;; this symbolo adds no information
            (=/= a `(,x . ,y))
            ;;;  (== a `(,x . ,y)) 
            (not-symbolo x))) )
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed 
)



(Complicated-4-2
  (run 1 (a) 
    (for-all (x y) 
      (disj* 
            (symbolo x) ;; this symbolo adds no information
            ;;; (=/= a `(,x . ,y))
            (conj* 
                   (== a `(,x . ,y)) 
                   (not-symbolo x)
                   )
            )) )
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'fail
)

(Complicated-4-3
  (run 1 (a) 
    (for-all (x y) 
      (disj* 
            (symbolo x) ;; this symbolo adds no information
            (=/= a `(,x . ,y))
            ;;; (conj* 
            ;;;        (== a `(,x . ,y)) 
            ;;;        (not-symbolo x)
            ;;;        )
            )) )
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed 
)

(Complicated-5
  (run 1 (a) 
    (disj* (not-pairo a) 
           (fresh (m n) (not-symbolo m) (== a (cons m n)) )) )
;;; ((not-pairo a) [(_.0 . _.1) where (not-symbolo _.0)] …)
. test-reg!=> . 'succeed 
)

;;; the above currently unhalt if set to run 1

(WeirdOne-2
  (run 1 (a) 
  (for-all (x y) (disj* 
                        (=/= a x) 
                        (conj* (== a x) (== x y)))))
;;; it is equivalent to
;;; for-all (x y) (conj* (disj* (=/= a x) (== a x)) 
                        ;;;  (disj* (=/= a x) (== x y)))
;;; which is again
;;;     for-all (x y) (disj* (=/= a x) (== x y))
. test-reg!=> . 'fail
)



(WeirdOne-3
  (run 1 (a) 
  (for-all (x y) (disj* (=/= a x) (== x y))))
;;; it is equivalent to
;;; for-all (x y) (conj* (disj* (=/= a x) (== a x)) 
                        ;;;  (disj* (=/= a x) (== x y)))
;;; which is again
;;;     for-all (x y) (disj* (=/= a x) (== x y))
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
(Trivial-Wrong-1
  (run 1 (a) (for-all (x) (== x a))) . test-reg!=> . 'fail)
((run 1 (a) (for-all (x) (fresh (s) (== a s)))) . test-reg!=> . 'succeed)
((run 1 (a) (for-all (x) (fresh (s) (== x s)))) . test-reg!=> . 'succeed)
((run 1 (a) (for-all (x) (fresh (s t) (== s `(,x . ,t))))) . test-reg!=> . 'succeed)




((run 1 (a b) (for-all (x) 
  (disj (=/= x a) (=/= x b)))) . test-reg!=> . 'succeed)
; closed world: removing any of the disjuncts should fail
(Closed-world-1
  (run 1 () (for-all (x) 
  (disj* 
         (== x #t) 
         (fresh (r s) (== x (cons r s)))))) . test-reg!=> . 'fail)

(Closed-world-2
  (run 1 () (for-all (x) 
  (disj* (symbolo x) (numbero x) (stringo x)
         (== x #t) (== x #f) (== x '())
         (fresh (r s) (== x (cons r s)))))) . test-reg!=> . 'succeed)

; cons + car/cdr: all these should 'succeed
((run 1 () 
(for-all (x) 
  (fresh (r) 
    (disj* (fresh (s t) (=/= x (cons s t))) ; this always holds
          (fresh (s t) (== x (cons s t))))))) . test-reg!=> . 'succeed) ; x is the pair

; cons + car/cdr: all these should 'succeed
((run 1 () 
(for-all (x) 
  (fresh (r) 
    (disj* (for-all (s t) (=/= x (cons s t))) ; x not any pair  
          (fresh (s t) (== x (cons s t))))))) . test-reg!=> . 'succeed) ; x is a pair

; different ways of encoding a “pairo” like constraint
((run 1 () (for-all (x)
   (disj* (not-pairo x) 
          (fresh (s t) (== x (cons s t))))))
   . test-reg!=> . 'succeed
   )
; Using relations
((run 1 () (for-all (x) (fresh (r s)
    (disj* (=/= (cons x r) s)
           (appendo (list x) r s))))) 
    ;;; [s == (x . r)] ==> appendo (list x) r s
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


(NestedCons-1
  (run 1 (c a b) (for-all (x) (=/= c (cons a (cons b x)))))
. test-reg!=> . 'succeed)

;;; The following current has bug
(NestedCons-2
  (run 1 (c a b) (for-all (y) (=/= c (cons a (cons b y)))) )
. test-reg!=> . 'succeed)
((run 1 () (for-all (x) (=/= x (cons x x))))
. test-reg!=> . 'succeed)
((run 1 (a) (for-all (y) (disj* (numbero a) (stringo a))))
. test-reg!=> . 'succeed)
((run 1 () (for-all (z) (fresh ( r ) (=/= r z) (numbero r))))
. test-reg!=> . 'succeed)
(For-bound-Trivial-1
  (run 1 () (for-bound (z) [numbero z] (=/= z (cons 1 2))))
. test-reg!=> . 'succeed)
((run 1 () (for-bound (z) [stringo z] (=/= z (cons 1 2))))
. test-reg!=> . 'succeed)
((run 1 () (for-bound (z) [symbolo z] (=/= z (cons 1 2))))
. test-reg!=> . 'succeed)

;;; TODO: Higher-ranked for-all
;;; ((run 1 () (for-bound (z) [(for-bound (x) (== x z))] (Bottom)) )
;;; . test-reg!=> . 'succeed)
;;; ((run 1 () (for-bound (z) [(for-bound (x) (=/= x z))] (Bottom)) )
;;; . test-reg!=> . 'succeed)
(For-bound-Identity-1
  (run 1 () (for-bound (z) [numbero z] (numbero z) ))
. test-reg!=> . 'succeed)

(For-bound-Identity-2
  (run 1 () (for-bound (z) [numbero z] (symbolo z) ))
. test-reg!=> . 'fail)


(For-bound-Vacuous-1
  (run 1 () (for-bound (z) [z . =/= . z] (Bottom) ))
. test-reg!=> . 'succeed)

;;; baby sorting

;;;  truthness : truth value always first
(define-relation (sort-two-boolo xs ys)
  (fresh (x1 x2 y1 y2)
    (== xs (list x1 x2))
    (== ys (list y1 y2))
    (conde ((=/= x1 #f) (=/= x2 #f)
            (=/= y1 #f) (=/= y2 #f))
           ((=/= x1 #f) (== x2 #f)
            (=/= y1 #f) (== y2 #f))
           ((== x1 #f) (=/= x2 #f)
            (=/= y1 #f) (== y2 #f))
           ((== x1 #f) (== x2 #f)
            (== y1 #f) (== y2 #f)))))
(Babysort
  (run 1 () (for-all (x1 x2) 
    (fresh (r1 r2)
      (sort-two-boolo (list x1 x2) (list r1 r2))
      (disj* (conj* (=/= x1 #f) (=/= x2 #f))
             (== r2 #f)))))
. test-reg!=> . 'succeed
)

(Babysort-fail
  (run 1 () (for-all (x1 x2) 
    (fresh (r1 r2)
      (sort-two-boolo (list x1 x2) (list r1 r2))
      (disj* (conj* (=/= x1 #f) (=/= x2 #f))
             (=/= r2 #f)))))
. test-reg!=> . 'fail
)

(define-relation (splito xs x1s x2s)
  (conde ((== xs '())
          (== x1s '())
          (== x2s '()))
         ((fresh (x)
           (== xs (list x))
           (== x1s (list x))
           (== x2s '())))
         ((fresh (xs^ x y x1s^ x2s^)
           (== xs (cons x (cons y xs^)))
           (== x1s (cons x x1s^))
           (== x2s (cons y x2s^))
           (splito xs^ x1s^ x2s^)))))
(define-relation (merge-boolo xs ys xsys)
  (conde ((== xs '()) (== ys xsys))
         ((== ys '()) (== xs xsys))
         ((fresh (x y xs^ ys^ xsys^)
            (== xs (cons x xs^))
            (== ys (cons y ys^))
            (conde ((== x #f)
                    (== xsys (cons x xsys^))
                    (merge-boolo xs^ ys xsys^))
                   ((=/= x #f)
                    (== xsys (cons y xsys^))
                    (merge-boolo xs ys^ xsys^)))))))
(define-relation (sort-boolo xs ys)
  (conde ((== xs '()) (== ys '()))
         ((fresh (x)
           (== xs (list x))
           (== ys (list x))))
         ((fresh (x1s x2s y1s y2s)
              (splito xs x1s x2s)
              (sort-boolo x1s y1s)
              (sort-boolo x2s y2s)
              (merge-boolo y1s y2s ys)))))


(define-relation (membero elem lst)
  (fresh (first rest)
    (== lst (cons first rest))
      (conde
        ((== first elem))
        ((membero elem rest)))))

(Teenage-sort-1
  (run 1 () (for-bound (x) [boolo x] (sort-boolo (list x #f) (list #f x))))

. test-reg!=> . 'succeed
)

(Teenage-sort-2
  (run 1 () (for-bound (x) [boolo x] (sort-boolo (list #f x) (list #f x))))
. test-reg!=> . 'succeed
)

(Teenage-sort-3
  (run 1 () (for-bound (x) [boolo x] (sort-boolo (list x #f #f) (list #f #f x))))
. test-reg!=> . 'succeed
)

(Teenage-sort-4
  (run 1 () (for-bound (x) [boolo x] (sort-boolo (list #f x #f) (list #f #f x))))
. test-reg!=> . 'succeed
)

(Teenage-sort-5
  (run 1 () (for-bound (x) [boolo x] (sort-boolo (list #f #f x) (list #f #f x))))
. test-reg!=> . 'succeed
)

(Teenage-sort-6
  (run 1 (a) (for-bound (x) [boolo x] (sort-boolo (list #f #f x) (list a #f x))))
. test-reg!=> . 'succeed
)


(define (sort-boolo-base-case xs ys o)
  (conde ((== xs o) (== ys o))
         ((fresh (x)
           (== xs (list x))
           (== ys (list x))))
         ((fresh (x1s x2s y1s y2s)
              (splito xs x1s x2s)
              (sort-boolo x1s y1s)
              (sort-boolo x2s y2s)
              (merge-boolo y1s y2s ys)))))

(sort-bool-synthesize-base
  (run 1 (o) (for-all (x) (sort-boolo-base-case (list x #f #f #f) (list #f #f #f x) o)))
. test-reg!=>ND . 'succeed 
)

(sort-boolo-implies-membero-1
  (run 1  (y lst) 
      (cimpl (sort-boolo lst (cons #f y))
             (membero #f lst))
    )
. test-reg!=> . 'succeed 
)


;;; 
;;; Following test-cases are for cimpl
;;; 

((run 1 (x)  (cimpl (== x 1) (=/= x 2)))
  . test-reg!=> . 'succeed  
)

((run 1 ()  (for-all (x) (cimpl (== x 1) (=/= x 2))))
  . test-reg!=> . 'succeed  
)

((run 1 (x a)  (cimpl (== x a) (=/= x 2)))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (for-all (x) (cimpl (== x a) (=/= x 2))) )
  . test-reg!=> . 'succeed  
)

((run 1 (x a)  (cimpl (== x a) (=/= x a)))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (for-all (x) (cimpl (== x a) (=/= x a))) )
  . test-reg!=> . 'fail  
)


((run 1 (a)  (cimpl (stringo a) (symbolo a)))
  . test-reg!=> . 'succeed  
)

((run 1 ()  (for-all (a) (cimpl (stringo a) (symbolo a))) )
  . test-reg!=> . 'fail  
)

((run 1 (a)  (cimpl (== a 1) (symbolo a)))
  . test-reg!=> . 'succeed  
)

((run 1 ()  (for-all (a) (cimpl (== a 1) (symbolo a))))
  . test-reg!=> . 'fail  
)


((run 1 ()  (for-all (a) (cimpl (== a 1) (numbero a))))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (cimpl (=/= a 1) (symbolo a)))
  . test-reg!=> . 'succeed  
)

(Cimpl-dec1
  (run 1 ()  (for-all (a) (cimpl (=/= a 1) (symbolo a))) )
  . test-reg!=> . 'fail  
)


((run 1 (a)  (conj (== a 1) (cimpl (=/= a 1) (symbolo a))))
  . test-reg!=> . 'succeed  
)


((run 1 (a)  (conj (numbero a) (cimpl (stringo a) (symbolo a))) )
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (conj (== a 1) (cimpl (== a 1) (symbolo a))))
  . test-reg!=> . 'fail  
)

(define-relation (False x)
  (False x))


(Syn-solve-1
  (run 1 (a)  (cimpl (False a) (False a)))
  . test-reg!=> . 'succeed  
)

(define-relation (Falsew/1 x)
  (conj (== x 1) (Falsew/1 x)))


((run 1 (a)  (cimpl (Falsew/1 a) (Falsew/1 a)))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (cimpl (Falsew/1 a) (== a 1)))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (cimpl (Falsew/1 a) (== a 2)))
  . test-reg!=> . 'succeed  
)


(define-relation (False1 x)
  (False2 x))

(define-relation (False2 x)
  (False1 x))

(define-relation (False3 x)
  (False x))


((run 1 (a)  (conj (cimpl (False1 a) (False2 2)) (== a 2)))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (conj (cimpl (False2 a) (False1 2)) (== a 2)))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (conj (cimpl (False3 a) (False 2)) (== a 2)))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (conj (cimpl (False a) (False3 2)) (== a 2)))
  . test-reg!=> . 'succeed  
)

((run 1 (a)  (cimpl (conj (a . == . 1)  
                          ((a . == . 1) . → . (symbolo a))) 
                    (Bottom)) )
  . test-reg!=> . 'succeed  
)

(define → cimpl)

(Syn-solve-cimpl
  (run 1 (a)  (cimpl ((== a 1) . → . (False a)) 
                    (False a)) )
  . test-reg!=> . 'succeed  
)

(Syn-solve-lor
  (run 1 (a)  (cimpl ((disj (== a 1) (Bottom)) . → . (False a)) 
                    (False a)) )
  . test-reg!=> . 'succeed  
)


(Syn-solve-land
  (run 1 (a)  (cimpl ((conj (== a 1) (Top)) . → . (False a)) 
                    (False a)) )
  . test-reg!=> . 'succeed  
)

;;; This goal can only be satisfied from outside
;;; Opaque-Goal = False
(define (Opaque-Goal)
  (let* ([k (gensym)])
    (letrec ([g (λ () (relate (λ () (fresh () (g))) `(,k))) ])
      (g)
    )
  )
)

(define (ciff X Y) (conj (cimpl X Y) (cimpl Y X)))

(define-syntax random-goal
  (syntax-rules ()
    ((_ (x ...) g0 gs ...)
     (let ((x (Opaque-Goal)) ...)  (conj* g0 gs ...)))))

;;; Some tautology
(Syn-solve-taut-1
  (random-goal (A B C)
    (run 1 ()  (ciff 
                    (conj (A . → . C) (B . → . C)) 
                    ((disj A B) . → . C)) ))
  . test-reg!=> . 'succeed  
)

(Syn-solve-taut-2
  (random-goal (A B C)
    (run 1 ()  (cimpl  ;;; TODO: ciff here will makes unhalt
                        ;;; is that intuitionstically provable?
                    (disj (A . → . C) (B . → . C)) 
                    ((conj A B) . → . C)) ))
  . test-reg!=> . 'succeed  
)

(Syn-solve-taut-curry
  (random-goal (A B C)
    (run 1 ()  (ciff 
                    (A . → . (B . → . C)) 
                    ((conj A B) . → . C)) ))
  . test-reg!=> . 'succeed  
)

;;; A `unfold to` A
;;; A `unfold to` C \/ A

(Syn-solve-taut-comp
  (random-goal (A B C D E X Z)
    (run 1 ()  (cimpl 
                    (conj* 
                      (A . → . B)
                      (B . → . C)
                      (C . → . D)
                      (Z . → . D)
                      (D . → . E) 
                      (X . → . E))
                    (A . → . E)) ))
  . test-reg!=> . 'succeed  
)

((random-goal (A B C)
    (run 1 (a)  (cimpl
                    (conj 
                      ((disj A B) . → . C)
                      A) 
                    C) ))
  . test-reg!=> . 'succeed  
)


(Syn-solve-universal
  (random-goal (A)
    (run 1 ()  (cimpl 
                    (conj* 
                      (for-all (x) ((False x) . → . A))
                      (False 1))
                    A)))
  . test-reg!=> . 'succeed  
)


(Syn-solve-universal-2
  (random-goal (A)
    (run 1 (y)  (cimpl 
                    (conj* 
                      (for-all (x) ((False x) . → . A))
                      (False y))
                    A)))
  . test-reg!=> . 'succeed  
)

(Syn-solve-universal-3
  (random-goal (A)
    (run 1 ()  (for-all (x) 
                  (cimpl 
                    (conj* 
                      (False x)
                      (for-all (y) ((False y) . → . A)))
                    A))))
  . test-reg!=> . 'succeed  
)

;;; Unhalting!
(Syn-solve-universal-4
  (random-goal (A)
    (run 1 ()  (cimpl
                    (for-all (x) ((False x) . → . A))  
                    (for-all (x) ((False x) . → . A))
                    )))
  . test-reg!=> . 'succeed  
)

(Syn-solve-universal-5
  (random-goal (A)
    (run 1 ()  (cimpl
                    (for-all (x) A)  
                    (for-all (x) A)
                    )))
  . test-reg!=> . 'succeed  
)

(Syn-solve-universal-6
  (random-goal (A)
    (run 1 ()  (cimpl
                    A  
                    (for-all (x) A)
                    )))
  . test-reg!=> . 'succeed  
)

(Syn-solve-existential
  (random-goal (A)
    (run 1 ()  (cimpl 
                    (conj* 
                      (for-all (x) ((False x) . → . A))
                      (fresh (k) (False k)))
                    A)))
  . test-reg!=> . 'succeed  
)



(Syn-solve-existential-1
  (random-goal (A)
    (run 1 ()  (cimpl 
                    (fresh (x) A)
                    A)))
  . test-reg!=> . 'succeed  
)

(Syn-solve-existential-1-2
  (random-goal (A)
    (run 1 ()  (cimpl 
                    (fresh (x) A)
                    (fresh (y) A))))
  . test-reg!=> . 'succeed  
)


(Syn-solve-existential-2
  (random-goal (A)
    (run 1 ()  (cimpl 
                  (for-all (x) ((False x) . → . A))
                      (cimpl (fresh (k) (False k))
                                A))))
  . test-reg!=> . 'succeed  
)

(Syn-solve-existential-3
  (random-goal (A)
    (run 1 ()  (cimpl 
                  (fresh (k) (False k))
                      (cimpl (for-all (x) ((False x) . → . A))
                                A))))
  . test-reg!=> . 'succeed  
)


(Syn-solve-existential-4
  (random-goal (A)
    (run 1 ()  (cimpl 
                  (fresh (x) (disj A (=/= x x)))
                  A)))
  . test-reg!=> . 'succeed  
)

;;; At this point it is cartesian closed bi-category
;;; we should also try to prove pierce-law (((A -> B) -> B) -> B) which should fail

;;; Next for quantifiers

;;; 
;;; 
;;; 


;;; (define (report-current)
;;;   (printf "\n Passed/Total number of test-cases: ~a/~a" 
;;;     (passed-tested-number) 
;;;     (total-tested-number)))

;;; (define (report-coverage)
;;;   (annotate-covered-file (string->path "tests-fo-LF.rkt"))
;;; )

(define all-tests
  (test-suite 
    "all"
    (hash-for-each all-tests-table 
     (lambda (key value) (value)))
  )
)

;;; (define (run-all-tests)
;;;   (hash-for-each all-tests-table 
;;;     (lambda (key value) (value)))
;;;   ;;; (report-current)
;;; )


(define-syntax run-the-test
  (syntax-rules ()
    ((_ name)
     (let ([k (hash-ref all-tests-table 'name #f)]
           [q name])
      ((or k q))
     ) )
 ))



;;; 


(module+ test
  (require rackunit/text-ui)
  (require errortrace)
  (instrumenting-enabled #t)
  (run-tests all-tests))