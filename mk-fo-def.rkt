#lang racket
(provide 
  (struct-out Goal)
  (struct-out disj)
  (struct-out conj)
  (struct-out cimpl)
  (struct-out impl)
  (struct-out relate)
  (struct-out ==)
  (struct-out =/=)
  (struct-out ex)
  (struct-out forall)
  (struct-out Top)
  (struct-out Bottom)


  ;;; type constraint, without dual ?
  (struct-out symbolo)
  (struct-out numbero)
  (struct-out stringo)
  (struct-out not-symbolo)
  (struct-out not-numbero)
  (struct-out not-stringo)

  
  (struct-out stream-struct)
  (struct-out mplus)
  (struct-out bind)
  (struct-out pause)
  (struct-out mapped-stream)
  (struct-out to-dnf)
  (struct-out syn-solve)
  for-all
  for-bound
  for-bounds

  any?
  assumption-base?
  empty-assumption-base
  empty-assumption-base?

  Stream?

)


(struct Goal () 
  #:transparent)

(struct relate Goal (thunk description)      ;;;#:prefab
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "{user-relation ~a}" (relate-description val)))]
)
(struct == Goal    (t1 t2)
  #:transparent               
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a =ᴸ ~a" (==-t1 val) (==-t2 val)))]
     ;;; L stands for Lisp Elements
)
(struct ex Goal    (varname g) 
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∃~a. ~a" (ex-varname val) (ex-g val)))]
  #:guard (lambda (varname g type-name)
                    (cond
                      [(Goal? g) 
                       (values varname g)]
                      [else (error type-name
                                   "Should be Goal: ~e"
                                   g)]))
)
;;; meta-data ex, actually will be ignored at this stage
;;;   indicating the scope of varname, 
;;;   but only as a hint

;;; we need implement the first version of complement,
;;;   so the complement version of each operation need to be defined
(struct =/= Goal (t1 t2)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ≠ᴸ ~a" (=/=-t1 val) (=/=-t2 val)))]
)

(struct forall Goal (varname domain g)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∀~a {~a}. ~a" (forall-varname val) (forall-domain val)  (forall-g val)))]
  #:guard (lambda (varname domain g type-name)
                    (cond
                      [(Goal? g) 
                       (values varname domain g)]
                      [else (error type-name
                                   "Should be Goal: ~e"
                                   g)]))
)

(struct symbolo Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "symbol ~a" (symbolo-t val)))]
)

(struct not-symbolo Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-symbol ~a" (not-symbolo-t val)))]
)


(struct numbero Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "number ~a" (numbero-t val)))]
)

(struct not-numbero Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-number ~a" (not-numbero-t val)))]
)


(struct stringo Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "string ~a" (stringo-t val)))]
)

(struct not-stringo Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-string ~a" (not-stringo-t val)))]
)

;;; typeinfo is a set of type-symbol
;;; indicating t is union of these type
;;;   this goal is usually not interfaced to the user

(struct type-constraint Goal (t typeinfo)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "type-constraint ~a ~a" (type-constraint-t val) (type-constraint-typeinfo val)))]
  #:guard (lambda (t typeinfo type-name)
                    (cond
                      [(set? typeinfo) 
                       (values t typeinfo)]
                      [else (error type-name
                                   "bad typeinfo: ~e"
                                   typeinfo)]))
)


;;; haven't decided introduce or not
;;;   details in domain-exhausitive check
;;; (struct pairo (t)
;;;   #:methods gen:custom-write
;;;   [(define (write-proc val output-port output-mode)
;;;      (fprintf output-port "not-string ~a" (not-stringo-t val)))]
;;; )


(struct Top Goal ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "T" ))]
)


(struct Bottom Goal ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "⊥" ))]
)


;; first-order microKanren
;;; goals
(struct disj Goal   (g1 g2) 
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a ∨ ~a)" (disj-g1 val) (disj-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)

(struct conj  Goal (g1 g2)  
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a ∧ ~a)" (conj-g1 val) (conj-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)

;;; a short hand for g1 -> g2 /\ g2 -> g1
;;; TODO: using https://stackoverflow.com/questions/52137060/how-to-avoid-loading-cycle-in-racket
;;;     to cycle require the "decidable-goal?" from
;;;     because we require g1, g2 are both decidable-goal
(struct equiv Goal (g1 g2)  
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a <=> ~a)" (equiv-g1 val) (equiv-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)

;;; ;;; the following goal
;;; ;;;   it "hmap" maps each goal to a proof-term (usually a parameter)
;;; ;;;   and its semantic is the conjunction of all these goals
;;; ;;; 
;;; (struct parameter-list Goal (hmap)
;;;   #:transparent
;;;   #:guard (lambda (hmap type-name)
;;;                     (cond
;;;                       [(hash? hmap) 
;;;                        (values g1 g2)]
;;;                       [else (error type-name
;;;                                    "Should be a hashmap")]))
;;; )

;;; ;;; the following goal is exactly the semantic of a state
;;; (struct wrapped-state parameter-list () 
;;;   #:transparent)

;;; just a abbreviation of ~g1 \/ g2
(struct impl Goal (g1 g2)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a => ~a)" (impl-g1 val) (impl-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)
;;; constructive implication, basically will skip the 
;;;   handling of antec but directly proceed to conseq
(struct cimpl  Goal (g1 g2)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a => ~a)" (cimpl-g1 val) (cimpl-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)

;;; Syntactic assumption all the time
(struct cimpl-syn  cimpl ()  
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a ⟶ ~a)" (cimpl-g1 val) (cimpl-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)




;;; streams
(struct stream-struct () #:prefab)
(struct bind  stream-struct (asumpt bind-s bind-g)   
  #:transparent
  #:guard (lambda (asumpt bind-s bind-g type-name)
                    (cond
                      [(and (assumption-base? asumpt) 
                            (Stream? bind-s) 
                            (Goal? bind-g))
                       (values asumpt bind-s bind-g)]
                      [else (error type-name)]))
)
(struct mplus stream-struct (mplus-s1 mplus-s2) 
  #:transparent
  #:guard (lambda (mplus-s1 mplus-s2 type-name)
                    (cond
                      [(and (Stream? mplus-s1) 
                            (Stream? mplus-s2))
                       (values mplus-s1 mplus-s2)]
                      [else (error type-name
                              "Should both be Stream: ~e"
                              (list mplus-s1 mplus-s2) )]))
)

(define-syntax mplus*
  (syntax-rules ()
    ((_ x) x)
    ((_ x y ...) 
      (mplus x (mplus* y ...)))))

;;; (pause st g) will fill the generated proof term into st
;;; it has the same specification as (start st g)
(struct pause stream-struct (asumpt pause-state pause-goal) #:prefab)
(struct mapped-stream stream-struct (f stream) #:prefab)
;;; f :: state -> stream of states
;;; mapped-stream f (cons a s) = mplus (f a) (mapped-stream f s)
(struct to-dnf stream-struct (state mark) #:prefab)
;;; semantically there is or in the "state"
;;;   this will lift the "or"s into stream
;;;   at the current stage, mark is used for pointing to
;;;     the disj component

(struct syn-solve stream-struct (asumpt org-asumpt st g) #:prefab)


;;; this will force the v in st to be a stream of ground term
;;; basically used for proof-term-generation for
;;;    existential quantifier
;;;  say we have state (v =/= 1) /\ (numbero v)
;;; this will enumerate v to be each value
(struct force-v-ground stream-struct (v st) #:prefab)

(define (any? _) #t)
(define (assumption-base? k) (list? k))
(define (empty-assumption-base? k) (equal? k '()))
(define empty-assumption-base '())

;;; detect stream or not
(define (Stream? s)
  (or (stream-struct? s)
    (match s
      [#f #t]
      [(cons k r) (Stream? r)]
      [o/w #f]
    )))


(define-syntax for-all
  (syntax-rules ()
    ((_ (x) g0 gs ...)
      (let ( [x (var/fresh 'x)] ) 
        (forall x (Top) (conj* g0 gs ...))))

    ((_ (x y ...) g0 gs ...)
      (let ( [x (var/fresh 'x)] ) 
        (forall x (Top) (for-all (y ...) g0 gs ...))))
  ))

(define-syntax for-bounds
  (syntax-rules ()
    ((_ (x ...) () g0 gs ...)
      (for-all (x ...) g0 gs ...))

    ((_ (x) (cond0 conds ...) g0 gs ...)
      (let ( [x (var/fresh 'x)] ) 
        (forall x (conj* cond0 conds ...) (conj* g0 gs ...)) ) )
  
    ((_ (k x ...) (cond0 conds ...) g0 gs ...)
      (let ( [k (var/fresh 'k)] ) 
        (forall k (Top) (for-bound (x ...) (cond0 conds ...) g0 gs ... )) )
    )))

(define-syntax for-bound
  (syntax-rules ()
    ((_ (x) conds g0 gs ...)
      (let ( [x (var/fresh 'x)] ) 
        (forall x conds (conj* g0 gs ...)) ) )
  
    ((_ (k x ...) conds g0 gs ...)
      (let ( [k (var/fresh 'k)] ) 
        (forall k (Top) (for-bound (x ...) conds g0 gs ... )) )
    )))

