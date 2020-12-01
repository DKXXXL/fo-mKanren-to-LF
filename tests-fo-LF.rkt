#lang racket

(require "mk-fo.rkt")

(display "Running first-order-microKanren-LF tests:")
(newline)


(define blue-colour "\033[94m")
(define blue-colour-end "\033[0m")
(define-syntax test
  (syntax-rules ()
    ((_ name e-actual e-expected)
     (time (begin
             (printf "Testing ~a ~s: \n  ~s ~a \n  \n ==> " 
                      blue-colour name 'e-actual blue-colour-end)
             (let ((actual e-actual) (expected e-expected))
               (if (equal? actual expected)
                 (printf "~s\n" 'success)
                 (printf "FAILURE\nEXPECTED: ~s\nACTUAL: ~s\n"
                         expected actual))))))))

(define run-1-succeed (run 1 () (== 1 1)))
(define run-1-fail (run 1 () (== 1 2)))

;;; Sanity Check

(test 'Identity
  (run 1 () (for-all (y) (fresh (x) (== y x))))
  run-1-succeed
)


(test 'NEQPair
  (run 1 () (fresh (y) (for-all (x) (=/= y (cons x 3)))))
  run-1-succeed
)

(test 'NEQAll
  (run 1 () (fresh (y) (for-all (x) (=/= y x))))
  run-1-fail
)

(test 'NEQPair-All
  (run 1 () (fresh (y) (for-all (x) (=/= (cons y 3) (cons x 3)))))
  run-1-fail
)


(test 'Trivial-contradiction-1
  (run 1 () (for-all (y) (fresh (x) (== y x) (=/= y x))))
  run-1-fail
)

(test 'Trivial-contradiction-2
  (run 1 () (for-all (y) (for-all (x) (== y x) (=/= y x))))
  run-1-fail
)

(test 'Trivial-Disjunction-1
  (run 1 () (for-all (y) (for-all (x) (disj* (== y x) (=/= y x)))))
  run-1-succeed
)


(test 'Trivial-Disjunction-2
  (run 1 () (fresh (y) (for-all (x) (disj* (== y x) (=/= y x)))))
  run-1-succeed
)



