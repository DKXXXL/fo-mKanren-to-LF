#lang errortrace racket
(provide
  (all-from-out "common.rkt")
  (struct-out disj)
  (struct-out conj)
  (struct-out cimpl)
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
  


  (struct-out mplus)
  (struct-out bind)
  (struct-out pause)
  for-all
  for-bound
  for-bounds
  step
  mature
  mature?
  ;;; walk*/goal

  vars-member?
  vars-missing?
  goal-vars
  

  syntactical-simplify
  complement
  ;;; replace-1-to-0

  ==

  define-relation
  fresh
  conde
  query
  run
  run/state
  run*

  conj*
  disj*
  )

(require "common.rkt")
(require "proof-term.rkt")
(require errortrace)


;;; The following are for functionality of error-trace

(instrumenting-enabled #t)
;;; (profiling-enabled #t)
;;; (profiling-record-enabled #t)
;;; (execute-counts-enabled #t)
;;; (coverage-counts-enabled #t)


;;; the parent type of all goals
;;;  and "Goal?" is helpful 
(struct Goal () 
  #:transparent)

(struct relate Goal (thunk description)
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

;;; stands for existential quantifier
;;;   indicating the scope of varname, 
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


(struct =/= Goal (t1 t2)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ≠ᴸ ~a" (=/=-t1 val) (=/=-t2 val)))]
)

;;; universal quantifier,
;;;   domain decides the domain the varname quantifies on
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
;;; Note: this goal is not part of exposed interface 
;;;   only inner mechanism use it
;;;   Users will use (not-)symbolo, (not-)numbero, .. so on
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


;; first-order microKanren goals


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

;;; constructive implication, 
;;; its proof term is exactly the lambda
;;;  what's special about this is that
;;;   the system will try to extract the decidable component of antec
;;;     to either falsify or integrated into state
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

;;; constructive implication as well
;;;   what's different is that it will not deal with the antec
;;;     and directly consider every antec as part of assumption
;;;     (no semantic solving on assumption at all)
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

;;; used for contract
;;; TODO: change to better things
(define (any? _) #t)


;; TODO (greg): consider using sets
;;; The following are a incomplete interfaces for assumption-base
;;;   in case in the future we want to modify the implementation
;;;   of assumption base 
(define (assumption-base? k) (list? k))
(define (empty-assumption-base? k) (equal? k '()))
(define empty-assumption-base '())


;;; return (cons (cons index assumption) remaining-assumptiob-base)
;;;   return '() when assumption-base is empty
(define/contract (iter-assumption-base k)
  (assumption-base? . -> . any?)
  k
)

;;; TODO: try to make assumption base smaller
(define/contract (cons-assmpt index prop init-assmpt)
  (any? any? assumption-base? . -> . assumption-base?)
  (cons (cons index prop) init-assmpt)  
)


;;; return a list of goals from assumption
(define/contract (all-assumption-goals assmpt)
  (assumption-base? . -> . list?)
  (map cdr assmpt)
)

;;; return a list of terms from assumption
(define/contract (all-assumption-terms assmpt)
  (assumption-base? . -> . list?)
  (map car assmpt)
)

;;; The above are interfaces for assumption-base


;;; Denote Goal-map type as
;;;      (goal -> goal) -> (goal -> goal) -> goal -> goal
;;; extensible function on pattern matching
;;;  pretentious "map" just means it maps goal to goal
;;;   named as functor but actually just a homomorphism --
;;;     respects all the Goal? structure that is working on Goal?
;;;   This is inspired by TVM's IRFunctor, 
;;;     which I believe is also inspired by something else
;;; goal-base-map : (goal -> goal) -> (goal -> goal) -> goal -> goal
;;;  rec-parent will call the one on the past overloading functor

;;;   extended-f will use the whole composed functor
;;;  this functor will do nothing but recurse on the tree
(define (goal-base-map rec-parent rec-root g)
  ;;; (define rec extended-f)
  (let* ([rec rec-root])
    (match g
      [(disj   a b)   (disj  (rec a) (rec b))]
      [(conj   a b)   (conj  (rec a) (rec b))]
      [(cimpl  a b)   (cimpl (rec a) (rec b))]
      [(ex     v g)   (ex     v         (rec g))]
      [(forall v b g) (forall v (rec b) (rec g))]
      [_              (rec-parent g)])))  ;; otherwise do nothing

;;; Denote Goal-map type as
;;;      (goal -> goal) -> (goal -> goal) -> goal -> goal
;;;   named as functor but actually just a homomorphism --
;;;     respects all the Goal? structure that is not only working on Goal?

(define (goal-term-base-map rec-parent rec g)
  ;;; (define rec extended-f)
  (match g
    [(== x y)        (== (rec x) (rec y))]
    [(=/= x y)       (=/= (rec x) (rec y))]
    [(symbolo x)     (symbolo (rec x))]
    [(not-symbolo x) (not-symbolo (rec x))]
    [(numbero x)     (numbero (rec x))]
    [(not-numbero x) (not-numbero (rec x))]
    [(stringo x)     (stringo (rec x))]
    [(not-stringo x) (not-stringo (rec x))]
    [(type-constraint x types) (type-constraint (rec x) types)]
    [(disj a b)     (disj (rec a) (rec b))]
    [(conj a b)     (conj (rec a) (rec b))]
    [(ex v g)       (ex v (rec g))]
    [(forall v b g) (forall v (rec v) (rec g))]
    [_ (rec-parent g)] ;; otherwise do nothing
  )
)


;;; homomorphism on state
(define (state-base-endo-functor rec-parent rec g)
  (match g
    [(state a scope d t)
      (state (rec a) scope (rec d) (rec t))]
    [_ (rec-parent g)]
  )
)

(define (hash-key-value-map rec-parent rec g)
  (match g 
    [(? hash?)
      (make-hash (rec (hash->list g)))]
    [_ (rec-parent g)]))

(define (identity-endo-functor rec-parent rec g) g)

(define (goal-identity g) g)


;;; this one basically can help me solve the expression problem
;;; this is the procedure that will compose a bunch of functor into
;;;     one homomorphism
;;; For example:  I can extend state as I want now  
;;; [(goal -> goal) -> (goal -> goal) -> goal -> goal] -> (goal -> goal) 
(define (compose-maps maps)
  (define (compose-maps-with-extf maps rec-root)
    (match maps
      [(cons fst then)
        (let* ([rec-parent (compose-maps-with-extf then rec-root)])
          (lambda (g) (fst rec-parent rec-root g))
        )]
      ['() (lambda (x) x)]
    )
  )
  (define (resultf g)
    ((compose-maps-with-extf maps resultf) g) )
  resultf
)
;;; Example Usage: 
;;; not-symbolo will be translated into (numbero v stringo v pairo v boolo)
;;; (define remove-neg-by-decidability
;;;   (define (match-single rec-parent rec-root g)
;;;     (match g
;;;       [(not-symbolo x) (disj (pairo x) (boolo x) (numbero x) (stringo x))]
;;;       [(not-numbero x) (disj (pairo x) (boolo x) (symbolo x) (stringo x))]
;;;       [(not-stringo x) (disj (pairo x) (boolo x) (numbero x) (symbolo x))]
;;;       [_ (rec-parent g)]
;;;     )
;;;   )
;;;   (compose-maps (list match-single goal-base-map))
;;; )
;;; (define remove-neg-by-decidability-and-remove-cimple
;;;   (define (match-single rec-parent rec-root g)
;;;     (match g
;;;       [(not-symbolo x) (disj (pairo x) (boolo x) (numbero x) (stringo x))]
;;;       [(not-numbero x) (disj (pairo x) (boolo x) (symbolo x) (stringo x))]
;;;       [(not-stringo x) (disj (pairo x) (boolo x) (numbero x) (symbolo x))]
;;;       [_ (rec-parent g)]
;;;     )
;;;   )
;;;   (define (remove-cimpl rec-parent rec-root g)
;;;     (match g
;;;       [(cimpl x) (disj (pairo x) (boolo x) (numbero x) (stringo x))]
;;;       [(stop ..) (ex)]
;;;       [_ (rec-parent g)]
;;;     )
;;;   )
;;;   (compose-maps (list remove-cimpl match-single goal-base-map))
;;; )

;;; cimpl -> ... /\ remove-neg-by-decidability



;;; homomorphism on pair, will respect pair construct
;;;  will also respect tproj
;;;   Recall tproj is used for intermediate representation
;;;   -- during relative complements we need pair-less point-ful representation
(define (pair-base-map rec-parent extended-f g)
  (define rec extended-f)
  (match g
    ['() '()]
    [(cons a b) (cons (rec a) (rec b))]
    [(tproj tm cxr) (tproj_ (rec tm) cxr)] ;; respect tproj
    [_ (rec-parent g)]
  )
)



;;; ;;; homomorphism from pair, except that each "composed node" will translate to "or"
;;; ;;;   it's just mapping pairs into arithmetic
;;; ;;; for example, we have cons and unit in the language of lisp
;;; ;;; now you can basically look at it as another AST
;;; ;;;   now if we map cons to or, '() to Boolean value, then it is a kind of 
;;; ;;;     folding after evaluation
;;; (define (pair-base-functor op-mapping)
;;;   (define (pair-base-functor- rec-parent extended-f g)
;;;     (define rec extended-f)
;;;     (match g
;;;       ['() (op-mapping '())]
;;;       [(cons a b) ((op-mapping cons) (rec a) (rec b))]
;;;       [_ (op-mapping 'default )] ;;; otherwise use op-mapping's default
;;;     )
;;;   )
;;;   pair-base-functor-
;;; )


;;; The following two function can detect if there is 
;;;   var existence anywhere
;;;   in a given pair-goal
;;;     
(define/contract (vars-member? vars pair-goal)
  (set? any? . -> . boolean?)
  (define all-fvs (goal-vars pair-goal))
  (not (set-empty? (set-intersect vars all-fvs)))
)


(define/contract (vars-missing? vars pair-goal)
  (set? any? . -> . boolean?)
  (define all-fvs (goal-vars pair-goal))
  (set-subtract! all-fvs vars)
  (not (set-empty? all-fvs))
)


;;; Example Usage : replace 1 with 0 in an arbitrary list
;;; (define (replace-1-to-0 k)
;;;   (define (case1 rec-parent extended-f g)
;;;     (if (equal? g 1) 0 (rec-parent g)))
  
;;;   ((compose-maps (list case1 pair-base-map  identity-endo-functor)) k)
;;; )


;;; currently implemented with side-effect,
;;;   it is another kind of fold but I am bad at recursion scheme
;;;   basically return all free-variables appearing inside g
(define (goal-vars g)
  (define fvs (mutable-set))
  (define (counter rec-parent rec-root g)
    (match g
      [(var _ _) (begin (set-add! fvs g) g)]
      [_ (rec-parent g)]
    )
  )

  (define g-visitor 
    (compose-maps (list counter goal-term-base-map pair-base-map state-base-endo-functor identity-endo-functor))
  )

  (g-visitor g)
  fvs
)


;;; The following are defunctionalized stream structure

;;; stream-struct is the parent of all streams
(struct stream-struct () #:prefab)

(struct bind  stream-struct (assmpt s g)   
  #:transparent
  #:guard (lambda (assmpt s g type-name)
                    (cond
                      [(and (assumption-base? assmpt) 
                            (Stream? s) 
                            (Goal? g))
                       (values assmpt s g)]
                      [else (error type-name)]))
)

(struct mplus stream-struct (s1 s2) 
  #:transparent
  #:guard (lambda (s1 s2 type-name)
                    (cond
                      [(and (Stream? s1) 
                            (Stream? s2))
                       (values s1 s2)]
                      [else (error type-name
                              "Should both be Stream: ~e"
                              (list s1 s2) )]))
)

(define-syntax mplus*
  (syntax-rules ()
    ((_ x) x)
    ((_ x y ...) 
      (mplus x (mplus* y ...)))))

;;; (pause st g) will fill the generated proof term into st
;;; it has the same specification as (start st g)
;;; (pause st g) has same specification as (start st g)

(struct pause stream-struct (assmpt state goal) #:prefab)


;;; f :: state -> stream of states
;;; mapped-stream f (cons a s) = mplus (f a) (mapped-stream f s)
;;;   in a lazy fashion
(struct mapped-stream stream-struct (f stream) #:prefab)


;;; semantically there is or in the "state"
;;;   this will lift the "or"s into stream
;;;   at the current stage, mark is used for pointing to
;;;     the disj component
;;; finally a stream of state where only conjunction is inside each state
;;;  a /\ (b \/ c) /\ (d \/ e) 
;;;  1 -> a /\ c /\ e; 2 -> a /\ b /\ e ...
(struct to-dnf stream-struct (state address) #:prefab)


;;; a stream of syntactical solving
(struct syn-solve stream-struct (assmpt init-assmpt st g) #:prefab)


;;; this will force the v in st to be a stream of ground term
;;; basically used for proof-term-generation for
;;;    existential quantifier
;;;  say we have state (v =/= 1) /\ (numbero v)
;;; this will enumerate v to be each ground value except for $v = 1$ and number
(struct force-v-ground stream-struct (v st) #:prefab)


;;; detect stream or not
;;;   because we have #f as part of stream structure so
;;;   we cannot easily use stream-struct?
(define (Stream? s)
  (or (stream-struct? s)
    (match s
      [#f #t]
      [(cons k r) (Stream? r)]
      [o/w #f]
    )))


;;; A lot of boiler-plate code
;;;   (syntactical) unification on two goals, 
;;;   the open/free variables will try to be matched
;;;   the inner-declared variable will debrujin indexed
;;;     for alpha-equivalence
(define/contract (unify/goal ag bg st)
  (Goal? Goal? ?state? . -> . Stream?)
  (define solution 
    ; this could be a state, a goal, and etc.
    ;;; we will at the end transform it into a stream of state
    (match (cons ag bg)
      [(cons (relate _ b) (relate _ d))
        (and (equal? (car b) (car d)) (== b d))]
      [(cons (== a b) (== c d))
        (disj (conj* (== a c) (== b d)) (conj* (== a d) (== b c)))] 
      [(cons (=/= a b) (=/= c d))
        (disj (conj* (== a c) (== b d)) (conj* (== a d) (== b c)))]
      ;;; composed goals
      [(cons (ex a b) (ex c d))
        (let* ([k (gensym)]
              [LHS (b . subst . [k // a ])] ;;; (a [k/x])
              [RHS (d . subst . [k // c ])])
          (unify/goal LHS RHS st) ; a stream to return
        )]
      [(cons (forall a b c) (forall d e f))
        (let* ([k (gensym)]
              [LHS (c . subst . [k // a])]
              [LHS-D (b . subst . [k // a])]
              [RHS (f . subst . [k // d])]
              [RHS-D (e . subst . [k // d])])
          (mapped-stream 
            (lambda (st) (unify/goal LHS RHS st))
            (unify/goal LHS-D RHS-D st)) ; a stream to return
        )]
      [(cons (conj a b) (conj c d))
        (mapped-stream 
          (lambda (st) (unify/goal b d st))
          (unify/goal a c st)) ; a stream to return
        ]
      [(cons (disj a b) (disj c d))
        (mapped-stream 
          (lambda (st) (unify/goal b d st))
          (unify/goal a c st)) ; a stream to return
        ]
      [(cons (cimpl a b) (cimpl c d))
        (mapped-stream 
          (lambda (st) (unify/goal b d st))
          (unify/goal a c st)) ; a stream to return
        ]
      [(cons (symbolo a) (symbolo b))
        (== a b)]
      [(cons (not-symbolo a) (not-symbolo b))
        (== a b)]
      [(cons (numbero a) (numbero b))
        (== a b)]
      [(cons (not-numbero a) (not-numbero b))
        (== a b)]
      [(cons (stringo a) (stringo b))
        (== a b)]
      [(cons (not-stringo a) (not-stringo b))
        (== a b)]
      [(cons (type-constraint a T1) (type-constraint b T2))
        (and (equal? T1 T2) (== a b))]
      [_ #f]
  ))
  (match solution
    [(? ?state?) (wrap-state-stream solution)]
    [(? Goal?) (pause '() st solution)] 
    ;; TODO: Really without assumption? 
    [(? Stream?) solution]
  )
)

;;; used for (to-dnf stream):
;;;   since a state has semantic of disjunction
;;;     we transform it into DNF and we should be able to index each disjunct component

(define (get-state-DNF-range st)
  (define conjs (state-diseq st))
  (map length conjs)
)

 
(define (get-state-DNF-initial-index st)
  (define conjs (state-diseq st))
  (map (lambda (x) 0) conjs)
)

;;; return #f if there is no next
;;; precondition: length l == length range
(define (dnf-address++ l range)
  (match (cons l range)
    [(cons '() '()) #f]
    [(cons (cons a s) (cons r t))
      (if (< (+ 1 a) r)
        (cons (+ 1 a) s)
        (let* ([up-level (dnf-address++ s t)])
          (and up-level
            (cons 0 up-level))))]
  )
)

(define (get-state-DNF-next-address st address)
  (define range (get-state-DNF-range st))
  (dnf-address++ address range))

(define (get-state-DNF-by-address st address)
  (define conjs (state-diseq st))
  (define indexed-conjs (map (lambda (disjs pos) (list (list-ref disjs pos))) conjs address))
  (state-diseq-set st indexed-conjs)
)


;;; the goal is complementable 
;;;     iff goal is without any relate/no customized relations anywhere
(define/contract (complementable-goal? g)
  (Goal? . -> . boolean?)
  (define res #t)
  ;;; side-effect for folding
  ;;;   still using visitor pattern/homomorphism
  (define (each-case rec-parent rec g)
    (match g
      [(relate _ _) (begin (set! res #f) g)]
      [(cimpl a b) (rec b)] ; only requires b complementable
      [(forall _ b g) (rec (cimpl b g))] ; equivalent semantic
      [_ (rec-parent g)]
    )
  )
  (define f (compose-maps (list each-case goal-base-map identity-endo-functor)))
  (f g)
  res
)

;;; the goal is decidable 
;;;     iff goal is without any relate/any constructive implication
;;;     TODO: make it more relaxed
(define/contract (decidable-goal? g)
  (Goal? . -> . boolean?)
  (define res #t)
  ;;; side-effect for folding
  ;;;   still using visitor pattern/homomorphism
  (define (each-case rec-parent rec g)
    (match g
      [(relate _ _) (begin (set! res #f) g)]
      ;; TODO (greg): if `a` is decidable, the entire implication may still be decidable
      [(cimpl a b) (begin (set! res #f) g)] ; don't even allow implication to be inside g
      [(forall _ b g) (rec (cimpl b g))] ; equivalent semantic
      [_ (rec-parent g)]
    )
  )
  (define f (compose-maps (list each-case goal-base-map identity-endo-functor)))
  (f g)
  res
)

;;; Goal? -> Goal? x Goal? 
;;; specification: 
;;;   g <=> (let (a,b) = (split-dec+nondec g) in (conj a b))
;;;   where a must be decidable component
;;; {dec} + {non-dec}
(define/contract (split-dec+nondec g)
  (Goal? . -> . pair?)
  (define rec split-dec+nondec)

  (match g
    [(conj a b)
      (match-let* 
          ([(cons a-dec a-ndec) (rec a)]
           [(cons b-dec b-ndec) (rec b)])
        (cons (conj a-dec b-dec) (conj a-ndec b-ndec)))]

    [(disj a b)
      (if (andmap decidable-goal? (list a b))
          (cons (disj a b) (Top))
          (cons (Top) (disj a b)))]

    [(cimpl a b) 
        (if (decidable-goal? a)
          (match-let* ([(cons b-dec b-ndec) (rec b)]) 
                      (cons (cimpl a b-dec) (cimpl a b-ndec)))
          (cons (Top) g))]
    
    [(forall v D g)
        ;;; remember that D is always decidable (by definition)
        (match-let* 
          ([(cons g-dec g-ndec) (rec g)])
        (cons (forall v D g-dec) (forall v D g-ndec)))]

    ;;; others are considered as primitive case
    [_ 
      (if (decidable-goal? g)
        (cons g (Top))
        (cons (Top) g))
    ]
  )
)


;;; Use syntactical-simplification
;;;   right after decidable component extraction
(define/contract (simplify-dec+nondec g)
  (Goal? . -> . pair?)
  (if (decidable-goal? g)
      `(,g . ,(Top))
      (match-let* ([(cons a b) (split-dec+nondec g)])
        `(,(syntactical-simplify a) . ,(syntactical-simplify b)))
  )   
)


;;; the special stream only used for forall
;;;   all the possibe results of first-attempt-s
;;;   will be complemented and intersect with the domain of the bind-g
;;;   bind-g will have to be a forall goal
(struct bind-forall  stream-struct (assmpt scope state domain-var g)          #:prefab)

;;; if a stream is WHNF(?)  
(define/contract (mature? s)
  (Stream? . -> . boolean?)
    (or (not s) (pair? s)))


(define (not-state? x) (not (state? x)))

;;; return a whnf of stream
(define/contract (mature s)
    (Stream? . -> . Stream?)
    ;;; (assert-or-warn (not-state? s) "It is not supposed to be a state here")
    ;;; (debug-dump "\n maturing: ~a" s)
    (if (mature? s) s (mature (step s))))
  

;;; given a stream of states, 
;;;   return another stream of states 
;;;   make sure there is no disjunction in meaning of each state and 
;;;     all the disjunction are lifted to mplus
;;;  semantic of to-dnf
(define/contract (TO-DNF stream)
  (Stream? . -> . Stream?)
  ;;; (debug-dump "TO-DNF computing \n")
  (mapped-stream (lambda (st) (to-dnf st (get-state-DNF-initial-index st))) stream))


;;; return an equivalent stream of state
;;;   where each state has no assymetrical inequality inside 
;;;     i.e. we won't have ((cons a b) =/= y)
;;;         instead we will have (a =/= y.1) \/ (b =/= y.2) together with y = (y.1, y.2)
;;;           note: y.1, y.2 are both fresh variables (instead of tproj) 
;;;       of course together with the stream y is not even a pair
(define/contract (TO-NON-Asymmetric assmpt stream)
  (assumption-base? Stream? . -> . Stream?)
  ;;; (debug-dump "TO-NON-Asymmetric computing \n")
  (mapped-stream (λ (st) (remove-assymetry-in-diseq assmpt st)) stream)
)

;;; term-finite-type : term x state -> stream
;;;  this will assert t is either #t, #f, or '()
;;;   NOTE: this procedure won't handle proof-term correctly
;;;     as we know pause will always fill in one proof-term
(define/contract (term-finite-type assmpt t st)
  (assumption-base? any? ?state? . -> . Stream?)
  (pause assmpt st (disj* (== t '()) (== t #t) (== t #f)))
)

;;; run a goal with a given state
;;;   note that when st == #f, the returned stream will always be #f
;;; Specificaion: 
;;;   the partial proof term of st will be applied with the proof-term of g
;;;   and if assmpt == '(), then we will only invoke semantic computation
(define/contract (start assmpt st g)
  (assumption-base? ?state? Goal? . -> . Stream?)

  ;;; the following is a heuristic 
  ;;;     on which case syntactical solving will happen
  (define heuristic-to-syn-solve
    (and (or (relate? g) (Bottom? g)) 
         (not (empty-assumption-base? assmpt))))
  
  (if heuristic-to-syn-solve
    (mplus 
      (syn-solve assmpt assmpt st g)
      (sem-solving assmpt st g))
    (sem-solving assmpt st g)  
  )
  
)



;;; run a goal with a given state
;;;     except we will only do syntactical solving on the given goal
;;;   using given "assmpt"
;;; 
;;;  1. when assmpt is empty, we will unfold one level of relation init-assmpt
;;;       and then do "pause/start" (cimpl init-assmpt' g)
;;;       so that a new decidable component of init-assmpt' can be extracted/analyzed/falsified
;;;  2. if any assmpt is actually used, we will shift the current proving target 'g'
;;;       and thus invoke a new "pause/start" (so that new possible sem-solving can be proceeded)
(define/contract (syn-solving assmpt init-assmpt st g)
  (assumption-base? assumption-base? ?state? Goal? . -> . Stream?)
  (debug-dump "\n syn-solving assmpt: ~a" assmpt)
  (debug-dump "\n syn-solving goal: ~a" g)
  ;;; first we look at top-level assumption to see if unification can succeed
  ;;; then we need to deconstruct the (top)-assumption base
  ;;;   to syntactical pattern match on all the sub-assumption
  ;;; TODO: here destruction on assmption 
  ;;;       doesn't integrate the sub-assmpt into the state... some information is loss
  ;;;       so currently paying the price of duplicate computation, 
  ;;;         we will keep calling sem-solving on cimpl which is the 
  ;;;    for example we have assumption list (a b (c \/ k) d e) to goal g
  ;;;      when we are dealing with the case c \/ k, we will at the end invoke  (c a b (d1 /\ d2 /\ ... (dj \/ dk) ..) e) on g
  ;;;           (k a b d e) on g, will duplicate the computation for the case (a b) on g
  ;;; TODO (greg): maybe we can delay this deconstruction to avoid duplicating computation
  (define/contract (traversal-on-assmpt term-name top-assmpt remain-assmpt)
    (any? Goal? assumption-base? . -> . Stream?)
    (define top-name-assmpt (cons term-name top-assmpt))
    (match top-assmpt
      [(conj a b) 
        (let* (
          [a-name (LFpair-pi-1 term-name)]
          [b-name (LFpair-pi-2 term-name)]
          [new-rem (cons-assmpt a-name a
                     (cons-assmpt b-name b remain-assmpt))]
          )
        (syn-solve new-rem init-assmpt st g)
        )]
      [(disj a b)
        ;;; TODO: remove duplicate computation. 
        ;;;   (syn-solve on g with init-assmpt)
        ;;;   w/-disj will calculate some parts of the above stream again
        ;;;     as we already half way through init-assmpt
        (fresh-param (lhs rhs split lhs-assmpt rhs-assmpt)
          (let* (
              [split-goal (conj (cimpl a g) (cimpl b g))]
              [st-pf-filled st]
              [reduced-assmpt (filter (lambda (x) (not (equal? top-name-assmpt x))) init-assmpt)]
              [w/-disj  (pause reduced-assmpt st-pf-filled split-goal)]
              [w/o-disj (syn-solve remain-assmpt init-assmpt st g)]    
              )
            (mplus w/-disj w/o-disj)))]
      [(cimpl a b)
          (fresh-param (applied argument)
            (let* (
                [st-pf-filled  st]
                [reduced-assmpt (filter (lambda (x) (not (equal? top-name-assmpt x))) init-assmpt)]
                [new-assmpt (cons-assmpt applied b reduced-assmpt)]
                [k (debug-dump "\n syn-solving: cimpl: new assmpt: ~a" new-assmpt)]
                [w/-cimpl
                  (mapped-stream
                    (λ (st) (pause init-assmpt st a))
                    (pause new-assmpt st-pf-filled g))]
                [w/o-cimpl
                  (syn-solve remain-assmpt init-assmpt st-pf-filled g)])
              (mplus w/-cimpl w/o-cimpl)
            ))]
      [(ex v t)
      ;;; the key idea is that
      ;;; ((forall v (R . cimpl . g)) and (ex v R)) . cimpl . g
          (fresh-param (axiom-deconstructor subgoal)
            (let* (
                [subgoal-ty (for-all (x) ( (t . subst . [x // v]) . cimpl . g ))]
                [axiom-decons-ty
                  (subgoal-ty . cimpl . 
                   ((ex v t) . cimpl . g))]
                [st-pf-filled st]
            ;;; remove that existential assumption as well
            ;;; TODO: apparently there are some duplicate computation, 
            ;;;   with these unremoved assumption before top assmpt
            ;;;     (because the new subgoal-ty barely changed)
                [reduced-assmpt (filter (λ (a) (not (equal? top-name-assmpt a))) init-assmpt)]
                [k (debug-dump "\n syn-solving: reduced assmpt: ~a" reduced-assmpt)]
                )
              (mplus 
                (syn-solve remain-assmpt init-assmpt st g)
                (pause reduced-assmpt st-pf-filled subgoal-ty))))]
      [(forall v domain t)
            (fresh-param (applied-term dp2)
            (let* (
                [VT (fresh-var VT)]
                [forall-internal (cimpl domain t)]
                [applied-type (forall-internal . subst . [VT // v])]
                [st-pf-filled st]
                ;;; Note: even though we seem to only allow for-all to be instantiated
                ;;;     with only one variable
                ;;;       the second instantiation will happen when our
                ;;;     proving goal is shifted from g
                [new-assmpt (cons-assmpt applied-term applied-type remain-assmpt)]
                    )
               
                (syn-solve new-assmpt init-assmpt st-pf-filled g)) )]
      ;;; atomic prop! just ignore them
      [o/w (syn-solve remain-assmpt init-assmpt st g)]
    )
  )

;;; original assumption: (P x)

;;; st: (== b c)
;; (== a b) -> G (== a c)

;; normalized (== a b) is (== a c)


;; (conj (== x 1) (== x y) (impl (== x 2) (== y 2)))
;;; (conj (== x 1) (== x y) (disj (=/= x 2) (conj (== x 2) (== y 2))))

;; (impl (== x 2) (== x 2))
;; results in one state with no constraints

;; (impl (== x 2) (== x 2)) ===> (disj (=/= x 2) (conj (== x 2) (== x 2)))
;; results in two states:
;;   x == 2
;;   x =/= 2

;; if we see (== a b) while solving G, then we can consider that (== a b) satisfied without adding this constraint to the state
;;; \neg (== a b)
;;; (== a b) /\ G

;;; incrementally-growing-set-of-assumptions

;;; where F is user-defined, and G is ==, this is a possible way to simplify without using G as a hash key:
;;; (impl (impl F G) goal)

;;; (disj (neg (impl F G))
;;;       (conj (impl F G) goal))

;;; (disj (neg (disj (neg F)
;;;                  (conj F G)))
;;;       (conj (disj (neg F) (conj F G)) goal))

;;; (disj (conj (neg G) F)
;;;       (conj (impl F G) goal))

;;; (impl F (conj dec-G undec-G))
;;; key: ((... \/ R \/ x==g) (impl F undec-G))


;;; (impl (disj* (P x) (Q y) (== a b)) goal)
;;;   ==>
;;; (conj (impl (disj (P x) (Q y)) goal) (impl (== a b) goal))


;;; (impl A (conj (P x) B))
;;;   ==>
;;; (conj (impl A (P x)) (impl A B))
;;;  key: (P x) points to (impl A (P x))
;;;  split using transformation for decidable B

;;; incrementally-growing set of assumptions:
;;; simple-assumptions: (set A B C (P x))
;;; complex-assumptions: (make-immutable-hash  ;; the purpose of this is to defer dealing with complex assumptions until they become relevant (useful for solving body)
;;;                        (G . (impl F G))  ;; i.e., if our goal is G then we can replace it with solving F
;;;                        (D . (disj D E))  ;; i.e., if our goal is D, then we can replace entire solving process with E added directly, and this D removed
;;;                        (E . (disj D E))
;;; 
;;; A is atomic     ;; base case
;;; A is user-defined, and unfolds:
;;;   => (conj B C) ;; just add B and C

;;;   => (impl A (impl B C))  ;; key: C
;;;   => (disj A B)           ;; key: (union (keys A) (keys B))


;;;   => (disj (impl A (disj B C)) D)  ;; key: (union (keys B) (keys C) (keys D))

;;;   => (disj D E)  ;; key D E
;;;   => (impl F G)  ;; key G
;;;   => (forall x domain body)  ;; key body
;;;   => (exists x body)         ;; key body

;;; stream-of-syntactically-solvable-relation-calls:
;;;   (P x), (A x), (B x), ... (stream-append/interleaved (unfold-accumulate-syntactic (A x)) (unfold-accumulate-syntactic (B x))))

;;; (A x) /\ (B x)


;;; original goal: g

;;; (solve st sossrc g)
;;; g is atomic: further constraint st using atomic constraint OR keep original st if atomic constraint exists in sossrc
;;; g is relation-call: can return original state if relation-call exists in sossrc OR unfold and solve relation-call
;;; g is conj
;;; g is disj


  (if (empty-assumption-base? assmpt)
    (and (ormap has-relate (all-assumption-goals init-assmpt)) 
         (unfold-assumption-solve init-assmpt st g)) 
    ;; TODO: change to re-invokable stream
    ;;; currently we expand the assumption to extract more information
    (match-let* 
        ([(cons (cons term-name ag) remain-assmpt) 
            (iter-assumption-base assmpt)]
         [if-top-level-match (unify/goal ag g st)] ;;; type: Stream?
         [k (debug-dump "\n current assmpt: ~a, matching ~a" ag if-top-level-match)]
         [if-top-level-match-filled if-top-level-match];;; fill the current proof term
        )
      (if if-top-level-match
          (mplus if-top-level-match-filled
                (traversal-on-assmpt term-name ag remain-assmpt))
          (traversal-on-assmpt term-name ag remain-assmpt))
    )
  )
)

;;; Also no proof-term generation for this part
;;;   unfold one-level of relation inside g
(define/contract (unfold-one-level-relate g)
  (Goal? . -> . Goal?)  
  (define (each-case rec-parent rec g)
    (match g
      [(relate thunk _) (thunk)] 
      [o/w (rec-parent g)]
    )
  )
  (define result-f 
    (compose-maps (list each-case goal-base-map pair-base-map identity-endo-functor))
  )
  (result-f g)
)

;;; detect if there is any customized relation in g
(define/contract (has-relate g)
  (Goal? . -> . boolean?)  
  (define result #f)
  (define (each-case rec-parent rec g)
    (if result
        g
        (match g
          [(relate thunk _) (begin (set! result #t) g)] 
          [o/w (rec-parent g)]))
  )
  (define result-f 
    (compose-maps (list each-case goal-base-map pair-base-map identity-endo-functor))
  )
  (result-f g)
  result
)



;;; assmpt x state x Goal -> Stream
;;;  it will first collapse/conj all the assumptions into one assumption
;;;   and then use unfold-one-level-relate on the one assumption
;;;   
;;;  this is different from others in that it is stepping assumption
;;;  precondition: assmpt != empty, (has-relate assmpt)
(define/contract (unfold-assumption-solve assmpt st goal)
  (assumption-base? ?state? Goal? . -> . Stream?)
  ;;; (define/contract (push-axiom st ty)
  ;;;   (?state? Goal? . -> . pair?)
  ;;;   (push-lflet st (LFaxiom ty) : ty))
  
  (define conj-assumpt-ty (foldl conj (Top) (all-assumption-goals assmpt)))
  (define conj-assumpt-term (foldl LFpair (LFaxiom (Top)) (all-assumption-terms assmpt)))
  
  (define unfold-conj-assumpt-ty (unfold-one-level-relate conj-assumpt-ty))
  (define s-unfold-conj-assmpt-ty (syntactical-simplify unfold-conj-assumpt-ty))

  (define unfolded-goal (cimpl s-unfold-conj-assmpt-ty goal)) 
  ;;; use cimpl here to allow newly unfolded assumption processed by sem-solving
  ;;; (match-let*
  ;;;    ([(cons st all-assmpt-term) (push-lflet st conj-assumpt-term : conj-assumpt-ty)]
  ;;;     [(cons st axiom-unfold)    (push-axiom st (cimpl conj-assumpt-ty unfold-conj-assumpt-ty))]
  ;;;     [(cons st axiom-simplify)  (push-axiom st (cimpl unfold-conj-assumpt-ty s-unfold-conj-assmpt-ty))]
  ;;;     [(cons st s-unfold-conj-term) 
  ;;;           (push-lflet st 
  ;;;             (LFapply axiom-simplify (LFapply axiom-unfold all-assmpt-term)) : s-unfold-conj-assmpt-ty)]
  ;;;     [final-st st]
  ;;;     )
    ;;; every might-be-useful assumption is already in the unfolded goal
  (pause empty-assumption-base st unfolded-goal)
  
)


;;; run a goal with a given state
;;; note that when st == #f, the returned stream will always be #f
;;; Specificaion: 
;;;   the partial proof term of st will be applied with the proof-term of g
(define/contract (sem-solving assmpt st g)
  (assumption-base? ?state? Goal? . -> . Stream?)
  ;;; the following used when primitive goal is to fill in the
  (and st ;;; always circuit the st
    (match g
    ((disj g1 g2)
     (step (mplus (pause assmpt st g1)
                  (pause assmpt st g2))))
    ((conj g1 g2)
    ;;; will add g1 into assumption when solving g2
    ;;;   different from cimpl that state will be impacted after solving g1
     (fresh-param (left-v)
       (let* ([st-pf-filled  st]
              ;;; Note: Also a stupid heurstic
              ;;; Warning!!!: later we will use cons-assmpt to sieve
              ;;;   the valid assumption into assumption base
              ;;;   instead of this incomplete relate check
              ;;;       Trivial assumption doesn't need to be added into assmpt
              ;;; TODO: to make things more informed 
              ;;; [new-assmpt (if (relate? g1) (cons-assmpt left-v g1 assmpt) assmpt)]
              [new-assmpt assmpt]
            )
       (step (bind new-assmpt (pause assmpt st-pf-filled g1) g2)))))
    ;;; the real syntactical solving for cimpl
    ((cimpl-syn g1 g2)
      (fresh-param (name-g1)
        (let* ([st-to-fill st])
          (pause (cons-assmpt name-g1 g1 assmpt) st-to-fill g2))
      ))
    ((cimpl g1 g2) 
      ;;; semantic solving of implication is 
      ;;;  g1 = g1-dec /\ g1-ndec
      ;;;     g1 -> g2 = g1-dec -> (g1-ndec -> g2)
      ;;;     = ~g1-dec \/ 
      ;;; [g1-dec /\ (g1-ndec -> bot)] \/ 
      ;;; [g1-dec /\ (g1-ndec -> g2)]
     (fresh-param (name-g1 adnd adnd-conj ~g1-dec-term ~g1-ndec-term
                   ~g1-dec->g1-dec->bot-term bot2
                   g1-dec-conj-~g1-ndec-term g1-dec-conj-g1-ndec-g2-term
                   g1-dec-term g2-dec-term g1-ndec-term g1-ndec-g2-term
                   bot->g2-term bot1)
      ;;; TODO: rewrite the following into ANF-style (the push-let form)
      (match-let* 
            ([(cons g1-dec g1-ndec) (simplify-dec+nondec g1)]
             [Axiom-DEC+NDEC-ty (cimpl g1 (conj g1-dec g1-ndec))]
             [Axiom-Bottom-g2-ty (cimpl (Bottom) g2)]
             [~g1-dec-ty (complement g1-dec)]
             [~g1-dec->g1-dec->bot (cimpl ~g1-dec-ty (cimpl g1-dec (Bottom)))]
             [~g1ndec (cimpl-syn g1-ndec (Bottom))]
             [g1ndec-g2 (cimpl-syn g1-ndec g2)]
             [st-to-fill st]
             [st-~g1-dec st-to-fill]
             [st-~g1ndec st]
             [st-g1ndec-g2 st-to-fill]
            )
        (mplus*
          (pause assmpt st-~g1-dec ~g1-dec-ty)
          ;;; A -> bot /\ A
          (pause assmpt st-~g1ndec (conj g1-dec (cimpl-syn g1-ndec (Bottom)))) 
          ;;; and syntactical falsifying 
          (pause assmpt st-g1ndec-g2 (conj g1-dec (cimpl-syn g1-ndec g2)))))
          ;;; and syntactical solving
    ))
    ((relate thunk descript)
      (pause assmpt st (thunk)))
    ((== t1 t2) (unify t1 t2 st))
    ((=/= t1 t2) (neg-unify t1 t2 st))
    ((symbolo t1)  (wrap-state-stream (check-as-inf-type symbol? t1 st)))
    ;; TODO (greg): factor out predicates
    ((not-symbolo t1) 
      (mplus 
        (term-finite-type assmpt t1 st)
        (wrap-state-stream (check-as-inf-type-disj (set-remove all-inf-type-label symbol?) t1 st)))) 
    ((numbero t1) (wrap-state-stream (check-as-inf-type number? t1 st)))
    ((not-numbero t1)  
      (mplus 
        (term-finite-type assmpt t1 st)
        (wrap-state-stream (check-as-inf-type-disj (set-remove all-inf-type-label number?) t1 st)))) 
    ((stringo t1) (wrap-state-stream (check-as-inf-type string? t1 st)))
    ((not-stringo t1)  
      (mplus 
        (term-finite-type assmpt t1 st)
        (wrap-state-stream (check-as-inf-type-disj (set-remove all-inf-type-label string?) t1 st))))

    ((type-constraint t types)
      (wrap-state-stream (check-as-inf-type-disj types t st)))
    ((ex v gn) 
      ;;; TODO: make scope a ordered set (or just a list)
      (let* (
          ;;; we first need to make scope information on state correct
          ;;; TODO: lift the scope information out of the state
          [add-to-scope (lambda (scope) (set-add scope v))]
          [remove-from-scope-stream 
            (lambda (st) 
              (wrap-state-stream (state-scope-update st (lambda (scope) (set-remove scope v)) )))]
          [scoped-st (state-scope-update st (lambda (scope) (set-add scope v)))]
          ;;; then we compose new proof-term hole
          [body-to-fill-scoped-st scoped-st]
          [solving-gn (pause assmpt body-to-fill-scoped-st gn)]

          ;;; we pop added scope information
          ;;;  and then make sure v become ground term (by using force-v-ground)
          ;;;  so that proof-term filling can succeed
          [remove-scoped-stream (mapped-stream remove-from-scope-stream solving-gn)]
          ;;; TODO: turn on the constructive existential
          ;;; [extract-ground-v-stream (mapped-stream (lambda (st) (force-v-ground v st)) remove-scoped-stream)]
          ;;; [instantiate-v-from-state
          ;;;   (lambda (st)
          ;;;     (wrap-state-stream
          ;;;       (st . <-pfg . (walk* v (state-sub st)))))]
          ;;; [term-filled-stream (mapped-stream instantiate-v-from-state extract-ground-v-stream)]
          [term-filled-stream remove-scoped-stream]
          )
         term-filled-stream))
    ;;; forall is tricky, 
    ;;;   we first use simplification to
    ;;;   we first need to consider forall as just another fresh
    ;;;   and "bind" the complement of result to the nexttime forall as domain
    ;;;   
    ;;; 
    ((forall var domain goal) 
      ;;; Note: we won't support complicated (like recursive 
      ;;;   relationship) in domain as the user
      ;;;     can always use cimpl for complicated antecident/domain
      ;;;   The good thing about this is that otherwise, the following
      ;;;     "checking-domain-emptieness" will need to be 
      ;;;     rewritten into stream computation, would be horrible
      ;;;    and also we won't have decidable domain-exhaustiveness check
      
      ;;;  the first step is actually trying prove bottom from domain or otherwise
      ;;; TODO: add syntactical solving (i.e. put domain_ into the assumption but never solve it)
      ;;;         as now we know domain is always decidable so we just need to solve it (to add into state)
      (let* [(domain_ (simplify-domain-wrt assmpt st domain var))  
             (k (begin (debug-dump "\n ~a : domain_ : ~a " var domain_)))] 

        (match domain_

          ;;; in the bottom case, inside proof term
          ;;;   we try to prove domain -> Bottom, and then prove Bottom -> goal
          ;;;   then by composition we are done
          [(Bottom) (let* 
                      ([k (debug-dump "\n one solution: ~a" st)]
                       [from-bottom-ty (cimpl (Bottom) goal)]
                       [pf-term-to-fill-st st]
                       [st-terminating st]
                       [w/scope (state-scope st-terminating)]
                       [res (clear-about st-terminating (list->set (state-scope st-terminating)) var)]
                      ;;;  [q (mature res)]
                      ;;;  [k (debug-dump "\n after clear about: ~a \n  with scope ~a removing ~a" q w/scope var)]
                       )
                      res 
                      ) ]
          [_ 
            (let* ([ignore-one-hole-st st])
              (bind-forall  assmpt
                            (set-add (state-scope st) var)
                            ;;; NOTE: the following "(ex var ..)" ex var is non-trivial and not removable.
                            ;;;     which is explicitly handling the scoped var
                            (TO-DNF (TO-NON-Asymmetric assmpt (pause assmpt ignore-one-hole-st (ex var (conj domain_ goal)))) )
                            var 
                            (forall var domain_ goal)))]
        )
      )
    )
    ((Top) (wrap-state-stream st))
    ((Bottom) (wrap-state-stream #f))
    ))
)
  

(define/contract (step s)
  (Stream? . -> . Stream?)
  ;;; (debug-dump "\n       step: I am going through ~a" s)
  (match s
    ((mplus s1 s2)
     (let ((s1 (if (mature? s1) s1 (step s1))))
       (cond ((not s1) s2)
             ((pair? s1)
              (cons (car s1)
                    (mplus s2 (cdr s1))))
             (else (mplus s2 s1)))))
    ((bind assmpt s g)
     (let ((s (if (mature? s) s (step s))))
       (cond ((not s) #f)
             ((pair? s)
              (step (mplus (pause assmpt (car s) g)
                           (bind assmpt (cdr s) g))))
             (else (bind assmpt s g)))))
    ((syn-solve asm org-asm st g)
     (syn-solving asm org-asm st g))
    ((to-dnf st mark)
      ;;; mark is the index
      (if (equal? (state-diseq st) '())
          (cons st #f)
          (and mark
            (let ([ret (get-state-DNF-by-address st mark)]
                [next-mark (get-state-DNF-next-address st mark)])
              (cons ret (to-dnf st next-mark))))
      ))

    ((mapped-stream f stream)
      ;;; TODO: recheck this part .. it might be not correct searching strategy
      (let ((s (if (mature? stream) stream (step stream))))
        (cond ((not s) #f)
              ((pair? s)
                (let* ([s- (f (car s))]
                       [sk (if (?state? s-) (wrap-state-stream s-) s-)]
                       [check (or (Stream? sk) (raise-and-warn "~a is not [?state? -> Stream? U ?state?] \n" f))])
                  (step (mplus sk
                               (mapped-stream f (cdr s))))) )
              (else (mapped-stream f s)))))
    ;;; bind-forall is a bit complicated
    ;;;   it will first need to collect all possible solution of
    ;;;   s, and complement it, and intersect with 
    ((bind-forall assmpt current-vars s v (forall v domain goal))
     (let ((s (if (mature? s) s (step s))))
       (cond 
        ;;; unsatisfiable, then the whole is unsatisfiable
        ((not s) #f)
        ;;; possible to satisfy! we complement this current requirement/condition
        ;;;  to initiate the search for the remaining domain
        ;;;  and the same time, other possible 

        ;;;   to initiate the search for remaining domain is hard: 
        ;;;   1. we extract goal from the state
        ;;;   2. we take its complement
        ;;;   3. we clear the v information from st
        ;;;   4. the cleared state and its complement help us on the next search 
        ((pair? s)
            (match-let* 
                  ([st (car s)]
                   [current-vars (list->set current-vars)]
                   [w/o-v (set-remove current-vars v)]
                  ;;;  TODO: figure out trace!
                   [mentioned-var (set-add current-vars v)]

                   ;; (x = (cons x y) ) (cons a x) = (cons a y) -> x = y
                  ;;;  (x = (cons a y)) => (a = x.car, y = x.cdr  )
                   [field-projected-st (field-proj-form st)]
                   [domain-enforced-st (domain-enforcement-st field-projected-st)]
                   [unmention-substed-st (unmentioned-substed-form mentioned-var domain-enforced-st)]
                   
                   
                   [relative-complemented-goal (relative-complement unmention-substed-st current-vars v)]
                  ;;;  remove more than one variable is good, make state as small as possible
                   [shrinked-st (shrink-away unmention-substed-st current-vars v)]
                   [k (begin  (debug-dump "\n domain ~a" domain)
                              (debug-dump "\n initial st: ~a" st)
                              (debug-dump "\n field-projected-st: ~a" field-projected-st)
                              (debug-dump "\n domain-enforced-st: ~a" domain-enforced-st)
                              (debug-dump "\n unmention-substed-st: ~a" unmention-substed-st)
                              (debug-dump "\n shrinked-st on ~a: ~a" v shrinked-st) 
                              (debug-dump "\n relative-complemented-goal: ~a" (syntactical-simplify relative-complemented-goal))
                              ;;; (debug-dump "\n complemented goal: ")(debug-dump st-scoped-w/ov)
                              ;;; (debug-dump "\n next state ") (debug-dump next-st) 
                              ;;; (debug-dump "\n search with domain on var ")
                              ;;; (debug-dump v) (debug-dump " in ") (debug-dump cgoal) 
                              (debug-dump "\n"))
                              ]
                    [valid-shrinked-state (valid-type-constraints-check shrinked-st)] ;; clear up the incorrect state information
                    [current-domain (state->goal st)]
                    ;;; there will be some unnecessary information caused by above computation, better removed. 
                    )
              ;;; forall x (== x 3) (== x 3)
              ;;;   forall x (conj (== x 3) (=/= x 3)) (== x 3)
              ;;;  forall x () (symbolo x) /\ (not-symbolo x)
              (step (mplus (pause assmpt valid-shrinked-state (forall v (conj relative-complemented-goal domain) goal))
                           (bind-forall assmpt current-vars (cdr s) v (forall v domain goal)))))) ;;; other possible requirements search

        (else (bind-forall assmpt current-vars s v (forall v domain goal))))

             ))
    ((pause assmpt st g) (start assmpt st g))
    (_            s)))


;;; trivially negate the goal, relies on the fact that
;;;  we have a dualized goals
;;; doesn't support user-customized goal, and universal-quantification
(define/contract (complement g)
  (Goal? . -> . Goal?)
  (let ([c complement])
    (match g
      [(disj g1 g2) (conj (c g1) (c g2))]
      [(conj g1 g2) (disj (c g1) (c g2))]
      [(cimpl a b) ;;; \neg a \lor b 
        (conj a (complement b))]
      [(relate _ _) 
        (raise-and-warn "User-Relation not supported.")]
      [(== t1 t2) (=/= t1 t2)]
      [(=/= t1 t2) (== t1 t2)]
      [(ex a gn) (forall a (Top) (c gn))]
      [(forall v bound gn) ;; forall v. bound => g
        (ex v (conj bound (complement gn))) ]
      [(numbero t) (not-numbero t)]
      [(not-numbero t) (numbero t)]
      [(stringo t) (not-stringo t)]
      [(not-stringo t) (stringo t)]
      [(symbolo t) (not-symbolo t)]
      [(not-symbolo t) (symbolo t)]
      [(type-constraint t types) 
        (disj (type-constraint t (set-subtract all-inf-type-label types)) (is-of-finite-type t))]
      [(Top) (Bottom)]
      [(Bottom) (Top)]
    )
  )
)





;;; simplify goal w.r.t. a domain variable, constant parameters acceptable
;;;   if satisfiable, then act as identity
;;;     note that this is only used by forall-bound (for-all domain) goal
;;;   otherwise return False
;;; simplify-domain-wrt : state x goal x var -> goal
;;; basically use vanilla miniKanren to check unsatisfiability
(define/contract (simplify-domain-wrt assmpt st goal var)
  (assumption-base? ?state? decidable-goal? any? . -> . Goal?)
  ;;; just run miniKanren!
  (define (first-non-empty-mature stream)
    (match (mature stream)
      [#f #f]
      [(cons #f next) (first-non-empty-mature next)]
      [v v]))
  ;;; Note: following we only allowed semantic solving,
  ;;;     as we don't allow cimpl/quantifier/customized relation in domain bound
  (if (first-non-empty-mature (pause empty-assumption-base st goal)) (syntactical-simplify goal) (Bottom))
  
  )

;;; some trivial rewrite to make goal easier/reable
;;;     equivalence is ensured
(define/contract (syntactical-simplify goal)
  (Goal? . -> . Goal?)
  (define (basic-tactic rec-parent rec goal)
    (define prev-result (rec-parent goal))
    (define singlerewrite 
      (match prev-result
        [(conj (Top) x) x]
        [(conj x (Top)) x]
        [(disj (Bottom) x) x]
        [(disj x (Bottom)) x]
        [(conj x x) x]
        [(disj x x) x]
        [_ 'rewrite-failed]
      )
    )
    (if (equal? singlerewrite 'rewrite-failed) prev-result (rec singlerewrite))
  )
  ((compose-maps (list basic-tactic goal-base-map  identity-endo-functor)) goal)
)


(define type-label-to-type-goal
  (hash
    symbol? symbolo
    pair? (lambda (term) (fresh (y z) (== term (cons y z))))
    number? numbero
    string? stringo
  )
)

;;; literally replace each x with mapping[x] in state/anything
;;;   actually also works for goal
;;;   there are some very mysterious behaviour here
;;;     as literal-replace* will respect substitution list inside state
(define/contract (literal-replace* mapping st)
  (hash? any? . -> . any?)
  (define (hash-table-add added htable)
    (define key (car added))
    (define value (cdr added))
    (define org (hash-ref htable key #f))
    (if org 
      (hash-set htable key (set-intersect org value))
      (hash-set htable key value))
  )

  (define subst-mapping (hash->list mapping))

  (define (literal-replace-from-after rec-parent rec obj)
    (match obj
      [x 
        #:when (hash-ref mapping x #f) 
        (walk* (hash-ref mapping x #f) subst-mapping) ]
      ;;; other extended construct -- like state
      ;;;  very untyped...
      ;;;  (a = a) (type-constrant a (number?))
      [(state a scope d e) 
        (let* ([new-sub-possible-with-cycle (rec a)] 
               [new-sub (filter (lambda (x) (not (equal? (car x) (cdr x)))) new-sub-possible-with-cycle)]
                ;;; TODO: we will only remove (a = a) and 
                ;;;   forget about possible cycle cases like (a = b, b = a)
               [old-hash-list (hash->list mapping)]
               [new-hash-list 
                (map (lambda (x) (cons (car x) (walk* (cdr x) new-sub))) old-hash-list)]
               [new-mapping (make-hash new-hash-list)]
               [rec (lambda (any) (literal-replace* new-mapping any)) ])
          (state new-sub scope (rec d) (rec e)))]
      ;;; or type constraint information,
      ;;;  we only need to deal with type information


      [(? hash?) 
        ;;; type-constraint!
        (let* ([type-infos (hash->list obj)]
               [new-type-infos (rec type-infos)])
          (foldl hash-table-add (hash) new-type-infos) ) ]
      [_ (rec-parent obj)]))

  (define internal-f (compose-maps (list literal-replace-from-after pair-base-map goal-term-base-map identity-endo-functor)))
  ;;; return the following
  (internal-f st)
)

(define-syntax subst
  (syntax-rules ( // )   
    ((_ X [to // from] ...) ; following the traditional subst syntax
      (let ([smap (make-hash `((,from . ,to) ... ))])
        (literal-replace* smap X)
      ))
  ))

;;; replace one var with another
;;;  var x var x state -> state
;;;   but will barely touch the type constraint 
;;;    s.t. after's type will be intersected with from's type constraint
;;;           if both after and from are variables
;;;    it will respect pair, goal, state-sub
;;;   i.e. when state is involved, 
;;;       the "after" will be replaced by (walk* after sub)
(define (literal-replace from after st)
  (literal-replace* (hash from after) st))



;;; [(term, term)] x state -> state
;;;  unifies each equation one by one
(define (unifies-equations list-u-v-s st)
  (foldl (lambda (eq st) (car (unify (car eq) (cdr eq) st))) st list-u-v-s)
)

;;; [(term, term)] -> [(term, term)]
;;; given a series of equation, make it into a standard subst form (cyclic-free)
(define (consistent-subst-equation list-u-v-s)
  (for/fold
    ([acc-subst '()])
    ([each-eq list-u-v-s])
    (match-let* ([(cons u v) each-eq])
      (unify/sub u v acc-subst))
  )
)

;;; return a set of vars, indicating that those vars, "s" are in the
;;;  form of "s =/= (cons ...)", and thus we need to break down s themselves
;;;   only used for TO-Non-Assymetry
(define/contract (record-vars-on-asymmetry-in-diseq st0)
  (state? . -> . any?)
  (define each-asymmetry-record! (mutable-set))
  (define (each-asymmetry rec-parent rec g)
    (match g
      ;;; thiss pattern matching i a bit dangerous
      ;;; TODO: make equation/inequality into a struct so that pattern-matching can be easier
      [(cons (var _ _) (cons _ _)) 
          (let* ([v (car g)])
              (set-add! each-asymmetry-record! v)
              g
                 )]
      [(cons (cons _ _) (var _ _)) 
          (let* ([v (cdr g)])
              (set-add! each-asymmetry-record! v)
              g)]
      [_ (rec-parent g)]

    )
  )

  (define each-asymmetry-recorder
    (compose-maps (list each-asymmetry pair-base-map identity-endo-functor))
  )
  (each-asymmetry-recorder (state-diseq st0))
  (set->list each-asymmetry-record!)
)

;;; var -> goal
;;;   a bunch of goal asserts v is of finite type
(define (is-of-finite-type v)
  (disj* (== v #t) (== v #f) (== v '()))
)


;;; given the st, we will break down a bunch of v's domain by the domain axiom
;;;  return an equivalent stream of states s.t. v is pair in one state and not pair in the others
;;; TODO: currently ignore proof-term
(define/contract (pair-or-not-pair-by-axiom assmpt vs st)
  (assumption-base? any? ?state? . -> . Stream?)
  (define (decides-pair-goal v) 
    (disj* 
       (type-constraint v (set pair?)) 
       (type-constraint v (set-remove all-inf-type-label pair?))
       (is-of-finite-type v)
    ))
  (define axioms-on-each 
    (map decides-pair-goal vs))
  
  (define conj-axioms
    (foldl conj (Top) axioms-on-each))
  
  (pause assmpt st (conj conj-axioms (== 1 1)))
)

;;; return an equivalent stream of state, given a state
;;;  but in each state, there is no assymetric disequality
;;;     i.e. (var s) =/= (cons ...)
;;;   This is usually where unhalting happening 
(define (remove-assymetry-in-diseq assmpt st)
  (define asymmetric-vars (record-vars-on-asymmetry-in-diseq st))
  ;;; (debug-dump "\n assymetric-st:  ~a \n asymmetric-vars: ~a" st asymmetric-vars)
  (if (equal? (length asymmetric-vars) 0)
    (wrap-state-stream st)
    (mapped-stream (lambda (st) (remove-assymetry-in-diseq assmpt st)) (pair-or-not-pair-by-axiom assmpt asymmetric-vars st))))


;;;  Recall the definition of tproj:
;;; tproj :: var x List of ['car, 'cdr] 
;;; cxr as a path/stack of field projection/query
;;; (struct tproj (v cxr) #:prefab)
;;; (struct tcar (term) #:prefab)
;;; (struct tcdr (term) #:prefab)



(define-syntax fresh-var
  (syntax-rules ()
    ((_ x)
     (let ((x (var/fresh 'x))) x))))

(define-syntax fresh-var/name
  (syntax-rules ()
    ((_ name)
     (let ((x (var/fresh name))) x))))

;;; given a tproj, we construct a tproj-ectable term for it
;;;  return the equation for removing the tproj
;;; tproj -> pair as var, cons/tree of vars
;;;  example: a tproj-able term for (x.car.cdr == ..) 
;;;     will become (x == ((a b) c)) (a == ...) 
(define (equation-for-remove-tproj x)
  ;;; (define field-projection-list (tproj-cxr x))
  (define x-name (format "~a" x))
  (define (construct-sketch path)
    (match path
      [(cons 'car rest)  (cons (construct-sketch rest) (fresh-var fpu))]
      [(cons 'cdr rest)  (cons (fresh-var fpu) (construct-sketch rest))]
      ['() (fresh-var fpu)]
    )
  )
  ;;; TODO: figure out why this algorithm is working! -_-
  (cons (tproj-v x) (construct-sketch (reverse (tproj-cxr x))))
)

;;; given a bunch of tproj
;;; return a pair of 
;;;   1. a subst mapping from var to its cons-structure
;;;   2. a hashmapping from each xs into var
(define/contract (proj-free-equations-for-tproj xs)
  ((listof tproj?) . -> . (cons/c (listof pair?) hash?))

  ;;; var-management info, no duplicate vars for same projection
  (define tp-to-var (hash))
  (define (get-var-from-tp tp)
  ;;; note this tp might be var as well
  ;;;     a tp with zero path is just a var
    (if (tproj? tp)
        (let* ([oldvar  (hash-ref tp-to-var tp #f)]
           [varname (string->unreadable-symbol (format "v~a" tp))]
           [maybe-newvar  (if oldvar oldvar (fresh-var/name varname))])
          (if oldvar '() (set! tp-to-var (hash-set tp-to-var tp maybe-newvar)))
          maybe-newvar)
        tp))

  ;;; construct equivalent equations for projection form 
  (define/contract (construct-body-eqs x)
    (tproj? . -> . (listof pair?))
    (match x 
      [(tproj xv (cons _ rem))
          (let* ([rest-body-equations (construct-body-eqs (tproj_ xv rem))]
                 [xv-rem     (get-var-from-tp (tproj_ xv rem))]
                 [xv-rem.1   (get-var-from-tp (tproj_ xv (cons 'car rem)))]
                 [xv-rem.2   (get-var-from-tp (tproj_ xv (cons 'cdr rem)))]
                 [xv-rem-eq  (cons xv-rem (cons xv-rem.1 xv-rem.2))])
            (cons xv-rem-eq rest-body-equations))]
      [(? var?) '()]
    )
  )

  ;;; collect all the equations w.r.t. xs
  (define all-equations 
    (for/fold
      ([acc     '()])
      ([each-tp  xs])
      (append (construct-body-eqs each-tp) acc)))

  ;;; equivalent as all-equations, but cycle-free (subst list)
  (define resulting-subst 
    (for/fold
      ([acc-sub     '()])
      ([each-eq all-equations])
      (match-let* ([(cons lhs rhs) each-eq])
        (unify/sub lhs rhs acc-sub))))

  ;;; collect all the projected var
  (define all-tproj-vs
    (for/fold
      ([acc-tproj-v (set)])
      ([each-tproj  xs])
      (match-let* ([(tproj v _) each-tproj])
        (set-add acc-tproj-v v))))
  
  ;;; now we have a big mapping maps each var to its cons-structure
  (define var-cons-form-mapping
    (for/fold
      ([mappings     '()])
      ([each-v      all-tproj-vs])
      (let* ([new-map (cons each-v (walk* each-v resulting-subst))])
        (cons new-map mappings))))

  (debug-dump "  proj-free-equations-for-tproj : resulting-subst : ~a \n" resulting-subst)
  (debug-dump "  proj-free-equations-for-tproj : var-cons-form-mapping : ~a \n" var-cons-form-mapping)
  (cons var-cons-form-mapping tp-to-var)

  
)

;;; taking car on both sides of eq
(define (tcar-eq eq) 
  (define res `(,(tcar (car eq)) . ,(tcar (cdr eq))))
  (match res 
    [(cons (? term?) _) res]
    [(cons _ (? term?)) (cons (cdr res) (car res))] 
    [_ res])
)


;;; taking cdr on both sides of eq
(define (tcdr-eq eq) 
  (define res `(,(tcdr (car eq)) . ,(tcdr (cdr eq))))
  (match res 
    [(cons (? term?) _) res]
    [(cons _ (? term?)) (cons (cdr res) (car res))] 
    [_ res])
)

;;; for Lisp universe, the only
;;;   non simple thing is pair
(define (not-simple-form x) (pair? x))
(define (is-simple-form x) (not (not-simple-form x)))


;;; given a set of equation 
;;;  return an equivalent set of equation 
;;;  s.t. each equation won't have pair inside, and at each side of
;;;     one equation there is only one var
(define/contract (field-proj-form st)
  (state? . -> . state?)
  (define eqs (state-sub st))

  (state-sub-set st (eliminate-conses eqs))
)

;;; given a set of equations 
;;;  return an equivalent set of equations, with no pair inside 
;;;  also no duplicate form, i.e. a and a._1 won't appear together
;;;     but only tproj inside
(define (eliminate-conses eqs)
  ;;; (debug-dump "\n eliminate-conses's input: ~a" eqs)
  ;;; (define (each-eli-eq single-eq)
  ;;;   ;;; won't stop if either side has cons
  ;;;   (match single-eq
  ;;;     [(cons LHS RHS)
  ;;;       #:when (and (is-simple-form LHS) (is-simple-form RHS)) 
  ;;;       (list single-eq)]
  ;;;     [(cons (cons _ _) _) (eliminate-conses (list (tcar-eq single-eq) (tcdr-eq single-eq)))]
  ;;;     [(cons _ (cons _ _)) (eliminate-conses (list (tcar-eq single-eq) (tcdr-eq single-eq)))]
  ;;;     [o/w (raise-and-warn "\n Unexpected equation form ~a" single-eq)]
  ;;;   )
  ;;; )

  ;;; (foldl append '() 
  ;;;     (map each-eli-eq eqs))
  
  ;;; a while loop, very procedure way of doing things
  ;;; basically will rewrite a bunch of equation into field-proj form
  ;;;   and also the ancestor won't appear, i.e. if a._1 is some term appearing, a won't appearing at all
  ;;;    the canonical-repr is the one helping with it
  (define (while-non-empty-eqs eqs res canonical-repr)
    ;;; (debug-dump "eliminate-conses: while-non-empty-eqs ~a\n          with partial result ~a \n" eqs res)
    (if (equal? '() eqs)
      res
      (match-let* 
        ([(cons eq rest) eqs]
         [(cons LHS RHS) eq]
         [eq-canon 
            (cons (hash-ref canonical-repr LHS LHS) 
                  (hash-ref canonical-repr RHS RHS))])
          (if (not (equal? eq-canon eq))
            (while-non-empty-eqs (cons eq-canon rest) res canonical-repr)      
            (if (and (is-simple-form LHS) (is-simple-form RHS))
              (while-non-empty-eqs rest (cons eq res) canonical-repr)
              ;;; one side is non-simple
              (match-let*
                ([new-eq1 (tcar-eq eq)]
                 [new-eq2 (tcdr-eq eq)]
                 [crpr canonical-repr]
                 [crpr1 (if (is-simple-form LHS) 
                            (hash-set crpr LHS (cons (tcar LHS) (tcdr LHS)))
                            crpr)]
                 [crpr2 (if (is-simple-form RHS) 
                            (hash-set crpr1 RHS (cons (tcar RHS) (tcdr RHS)))
                            crpr1)])
                (while-non-empty-eqs (cons new-eq1 (cons new-eq2 rest)) res crpr2)))))))
    (filter 
      (λ(t) (not (equal? (car t) (cdr t))))
      (while-non-empty-eqs eqs '() (hash)))
)


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



;;; given a state in unmentioned-exposed-form
;;;   return a state, where unmentioned-var are replaced as much as possible
;;;     "as much as" is because there are cases that unmentioned-var
;;;     has no relationship with other vars, so cannot be eliminated
;;; precondition: must in field-proj form
;;; TODO: maybe many more bugs are here
(define/contract (unmentioned-substed-form mentioned-vars st)
  (set? state? . -> . state?)
  
  (define (tproj-or-var? x) (or (var? x) (tproj? x)))
  ;;; following function will swap lhs and rhs of equation
  ;;;   if lhs is not unmentioned but rhs is
  ;;; postcondition: 
  ;;; 1. the lhs must be a var
  ;;; 2. if lhs is mentioned, then rhs must be mentioned
  ;;; 3. unsafe as substitution list as we are doing lhs/rhs swapping
  ;;;     might causing cycle in subst list, but those have unmentioned will soon removed
  ;;; 4. if there is unmentioned var, it must appear on the left hand side
  (define (swap-if-rhs-unmentioned eq)
    (define lhs (car eq))
    (define rhs (cdr eq))
    (define lhs-has-mentioned-var
      (vars-member? mentioned-vars lhs))

    (define rhs-has-unmentioned-var
      (vars-missing? mentioned-vars rhs))

    (if (and lhs-has-mentioned-var rhs-has-unmentioned-var)
      (cons rhs lhs) ;; doing swap
      eq))

  (define old-eqs (state-sub st))
  (define (remove-unnecessary-equation eqs)
    (filter 
      (λ(t)
        (and (pair? t)
          (not (equal? (car t) (cdr t)))))
      eqs)
  )
  (debug-dump "\n unmentioned-substed-form's input st: ~a \n unmentioned-substed-form's vars : ~a \n" st mentioned-vars)
  ;;; precondition: st has empty sub
  (define (unmention-remove-everywhere eqs0 st)
    ;;; (define eqs (state-sub st))
    (define eqs (remove-unnecessary-equation eqs0))
    (if (equal? eqs '())
      st
      (match (swap-if-rhs-unmentioned (car eqs))
        [(cons lhs rhs)
          #:when (vars-missing? mentioned-vars lhs) 
          ; when there is unmentioned var, thus equation needs removed
          ;;;  this should handle [(a == b, b == c), remove b] -> (a == c)
          (match-let* 
            ([new-rhs (walk* rhs (cdr eqs))]
             [(cons new-st remain-eqs) (literal-replace lhs new-rhs (cons st (cdr eqs)))]
             [k (debug-dump "\n        unmentioned-substed-form removing: ~a, into ~a" lhs new-rhs)]
            )
            (unmention-remove-everywhere remain-eqs new-st))]
        [(cons v rhs)
          ;;; BUG: rhs is not rewritten
          (state-sub-update 
            (unmention-remove-everywhere (cdr eqs) st)
            (lambda (eqs-) (cons (cons v rhs) eqs-)))]
      )
    ))
  ;;; (define new-eqs (filter (lambda (x) (set-member? mentioned-vars (car x))) old-eqs))
  
  (define result-st (unmention-remove-everywhere old-eqs (state-sub-set st '())))
  ;;; TODO: change to unify-equations
  (define (swap-to-lhs-var eq)
    (define lhs (car eq))
    (define rhs (cdr eq))

    (if (not (tproj-or-var? lhs))
      (cons rhs lhs) ;; doing swap
      eq))
  (state-sub-update result-st (lambda (eqs) (map swap-to-lhs-var eqs)))
)

;;; given a state in unmentioned-subst-form and field-projected-form
;;;   return a state, where 
;;;     every constraint "about any variables not inside mentioned-vars"
;;;         will be considered automatically satisfied
;;;   operationally, we just literally remove those constraints
;;; precondition: 
;;;  1. st is in unmentioned-substed-form, domain-enforced-form, field-proj-form
(define/contract (unmentioned-totally-removed mentioned-vars st)
  (set? state? . -> . state?)
  (let* ([domain-enforced-st st]
         [diseqs (state-diseq domain-enforced-st)]
         [new-diseq (filter (lambda (p) (not (vars-missing? mentioned-vars p))) diseqs)] 
         ;; diseqs must be list of singleton list of thing
         [type-rcd-lst (hash->list (state-typercd domain-enforced-st))]
         [new-typercd-lst (filter (lambda (v) (not (vars-missing? mentioned-vars v))) type-rcd-lst)]
         [new-typercd (make-hash new-typercd-lst)])
    (state-diseq-set 
      (state-typercd-set domain-enforced-st new-typercd)
      new-diseq))
)


;;; DomainEnforcement -- 
;;;   basically currently make sure if term (tproj x car) appear
;;;     then x is of type pair ((has-type x pair) will appear)
(define (domain-enforcement-st st) ;; (tproj x car.cdr.car) (typeconstant x car) pair
  (define all-tprojs (collect-tprojs st))
  ;;; (debug-dump "\n    inside domain-enforcement-st all-tprojs: ~a" all-tprojs)
  (define sub (state-sub st))
  ;;; (tproj v path) x state -> state
  ;;; given a (possibly complicated) tproj, make st enforce on its domain
  ;;;   example, if term = x.car.cdr, then (pair? x), (pair x.car) will both be added
  (define/contract (force-as-pair term st)
    (tproj? state? . -> . state?)

    ;;; return all the term that are typed pair inside a tproj term
    (define (all-domain-terms x)
      (define v (tproj-v x))
      (define path (tproj-cxr x))
      (match path
        [(list r) 
          #:when (member r '(car cdr))
          (set v)]
        [(cons r rpath)
          #:when (member r '(car cdr))
          (set-add (all-domain-terms (tproj v rpath)) (tproj v rpath))
        ]
        [o/w (raise-and-warn "Unexpected Path or Datatype")]
      )
    )
    (define collected-domain-terms (all-domain-terms term))
    ;;; (debug-dump "\n   inside force-as-pair current collected-domain-terms: ~a" collected-domain-terms)
    (for/fold 
      ([acc-st st])
      ([each-projed-term collected-domain-terms])
        (state-typercd-cst-add acc-st (walk* each-projed-term sub) (set pair?))
    )
  )

  (for/fold
    ([acc-st st])
    ([each-tproj-term all-tprojs])
    
      (force-as-pair each-tproj-term st))

  ;;; (foldl (lambda (tp st) (force-as-pair tp st)) st (set->list all-tprojs))
)

;;; similar as above, but it deal with goal and returns goal
;;;  TODO: duplicate code: but abstract it away doesn't quite make interpretable sense
(define (domain-enforcement-goal goal)
  (define all-tprojs (collect-tprojs goal))
  ;;; var x goal -> goal
  (define (force-as-pair v g) (conj g (type-constraint v (set pair?))))
  (foldl (lambda (tp g) (force-as-pair (tproj-v tp) g)) goal (set->list all-tprojs))
)

;;; return the prop/goal a state stands for
;;;   i.e. a state stands for a bunch of equalities and disequalities..
;;;     this will transform each state into that
(define/contract (state->goal st)
  (?state? . -> . Goal?)
  (for/fold
    ([acc-g (Top)])
    ([each-g (conj-state->list-of-goals st)])
    (conj acc-g each-g))
)

;;; given a state with only conjunction, we go through and take out all the
;;;   atomic proposition
(define/contract (conj-state->list-of-goals st)
  (state? . -> . list?)
  (define eqs 
    (set->list 
      (list->set 
        (map (lambda (eq) (== (car eq) (cdr eq))) (state-sub st)))))
  (define diseqs 
    (set->list 
      (list->set (map (lambda (l) (let ([l (car l)]) (=/= (car l) (cdr l))) ) 
                      (state-diseq st)))))
  (define types 
    (let* ([typ-infos (hash->list (state-typercd st))])
      (map (lambda (term-type) (type-constraint (car term-type) (cdr term-type))) typ-infos)))
  (append eqs (append diseqs types))
)

;;; given compositions of data structure where there is tproj appearances
;;;  return a set of all tprojs appear inside
(define (collect-tprojs anything)
  (define result (mutable-set))
  (define (each-case rec-parent rec g)
    (match g
      [(tproj _ _) (set-add! result g)] ;; local side-effect
      [o/w (rec-parent g)]
    )
  )
  (define result-f 
    (compose-maps (list each-case goal-term-base-map pair-base-map state-base-endo-functor hash-key-value-map identity-endo-functor))
  )
  (result-f anything)
  result

)

(define/contract (eliminate-tproj-in-st st)
  (state? . -> . state?)
  (debug-dump "  eliminate-tproj-in-st: input state ~a \n" st)
  (define all-tprojs (set->list (collect-tprojs st)))
  (define-values 
    (var-cons-structure 
     tproj-maps-to-var)
    (match-let* ([(cons a b) (proj-free-equations-for-tproj all-tprojs)])
      (values a b)
    ))
  (let* ([tproj-removed-st (literal-replace* tproj-maps-to-var st)]
         [sub              (state-sub tproj-removed-st)]
         [newsub           (append var-cons-structure sub)])
    (state-sub-set tproj-removed-st newsub)))

;;; anything (most likely pairs of goals) -> anything x List of equation
;;;     will remove every tproj, 
;;;       an gives a set of equation explaining the remove
;;;     for example (tproj x car) == k
;;;       will transform to (a == k) and a list of equation [(x (cons a b))]
;;; TODO: this thing seems buggy ... try to replace it with eliminate-tproj-in-st
(define (eliminate-tproj-return-record anything) ;; tproj x car.cdr.car ;; x = (cons (cons _ (cons _ _)) _)
  (define all-tprojs (set->list (collect-tprojs anything)))
  (define all-tproj-removing-eqs (map equation-for-remove-tproj all-tprojs))
  ;;; Interestingly, at this stage, these equations are not "unified"
  ;;;   basically it can have ( a == (x y . z)) and (a == (f . d)), then if the 
  ;;;     later one is used for subst, then we cannot, proceed for (cdr cdr cdr a)
  (define unified-all-tproj-removing-eqs (consistent-subst-equation all-tproj-removing-eqs) )
  ;;; then we do huge literal-replace
  ;;;  the literal-replace respects 
  (define tproj-removed (literal-replace* (make-hash unified-all-tproj-removing-eqs) anything))
  ;;; (debug-dump "\n eliminate-tproj-return-record's input: \n ~a" anything)
  ;;; (debug-dump "\n eliminate-tproj-return-record's input's tprojs: \n ~a" all-tprojs)

  ;;; (debug-dump "\n eliminate-tproj-return-record's using initial equation: \n ~a" all-tproj-removing-eqs)
  ;;; (debug-dump "\n eliminate-tproj-return-record's using unified equation: \n ~a" unified-all-tproj-removing-eqs)
  ;;; ;;; TODO : make sure that the constraint about (tproj x car) is transferred to the newly introduced var
  ;;; (debug-dump "\n eliminate-tproj-return-record's return: \n ~a" tproj-removed)
  
  ;;; TODO : make it into a contract
  (let* ([all-tproj (collect-tprojs tproj-removed)])
    (if (not (set-empty? all-tproj)) 
        (raise-and-warn "\n tproj elimination-failed ~a \n -> \n ~a \n gen-context of ~a \n" anything tproj-removed all-tproj-removing-eqs)

        'pass))
  (cons tproj-removed unified-all-tproj-removing-eqs)
)


;;; given a state, and the scope with the set of vars should be considered fixed
;;;  return a goal/proposition that
;;;   is the complement the domain of var in the state
;;;   other variables not mentioned in scope and var should be dealt with properly
;;; precondition: 
;;;    st is in conjunction form (i.e. there is no disjunction in diseq)
;;;    st is in non-asymmretic form (i.e. no (var ..) =/= (cons ...))
;;;    st is in field-projection form, where mentioned var are scope + var
;;;    st is domain-enforced
(define (relative-complement st scope varx)
;;; 2.5 first we do DomainEnforcement-Goal, basically every existence of term (tproj x)
;;;         has to introduce type constraint x \in Pair
;;; 3. we then make sure all existence unmentioned (in diseq) will be replaced by true
;;; 4. we then really do relative-complement,
;;;  4.1 by first translate the state into set(conjunction) of atomic prop
;;;  4.1.5 then we do DomainEnforcement-Goal, basically every existence of term (tproj x)
;;;         has to introduce type constraint x \in Pair
;;;  4.2 we then only keep those with 'var' mentioned
;;;  4.3 we then take syntactical complement on (each of) them, 
;;;     and the set of atomic prop will be interpreted as disjunctions of atomic prop
;;;  4.4 we again use DomainEnforcement-Goal on each of them
;;;  4.5 we translate the set into big disjunction
  (define mentioned-vars (set-add scope varx))
  
  (define domain-enforced-st st)
  ;;;  we remove none-substed appearances of unmentioned var
  (define unmentioned-removed-st (unmentioned-totally-removed mentioned-vars domain-enforced-st))
  ;;; Step 3 done
  (define atomics-of-states (conj-state->list-of-goals unmentioned-removed-st))
  (define atomics-of-var-related (filter (lambda (x) (vars-member? (set varx) x)) atomics-of-states))
  (define atomics-of-var-unrelated (filter (lambda (x) (not (vars-member? (set varx) x))) atomics-of-states) )
  (define complemented-atomics-of-var-related 
    (map complement atomics-of-var-related))
  ;;;  Note: this following re-application of domain-enforcement is necessary
  ;;;     
  (define domain-enforced-complemented-atomics-of-var-related 
    (map domain-enforcement-goal complemented-atomics-of-var-related))
  ;;; we are almost done but we need to remove tproj
  (define conj-unrelated 
    (syntactical-simplify (foldl conj (Top) atomics-of-var-unrelated)))
  (define disj-related 
    (foldl disj (Bottom) domain-enforced-complemented-atomics-of-var-related))

  (define returned-content (conj conj-unrelated disj-related))
  
  (define tproj-eliminated (eliminate-tproj-return-record returned-content))
  (define tproj-eliminated-content (car tproj-eliminated))
  (define tproj-eliminated-evidence (cdr tproj-eliminated))
  (define tproj-eliminated-evidence-goal
    (foldl conj (Top)
      (map (lambda (x) (== (car x) (cdr x))) tproj-eliminated-evidence)
    )
  )

  (conj tproj-eliminated-evidence-goal tproj-eliminated-content)

)


;;; given a state, and the scope with the set of vars should be considered fixed
;;;   return a state that : 
;;;     we shrink the existence of vars to scope 
;;;     other variables not mentioned in scope and var should be dealt with properly
;;; precondition: 
;;;   st is in conjunction form (i.e. there is no disjunction in diseq)
;;;   st is in non-asymmretic form (i.e. no (var ..) =/= (cons ...))
;;;    st is in field-projected-form, where mentioned var are scope + var
;;;   st is domain-enforced
;;; WARNING: there might be many more bugs undiscovered
(define/contract (shrink-away st scope var)
  (state? set? var? . -> . state?)
  (define mentioned-vars (set-remove scope var))
  ;;;  we need to do extra unmentioned-substed because here var is considered unmentioned
  (debug-dump "\n shrinking var: shrink-var-removed-st: ~a" st)
  (define var-removed-st (unmentioned-substed-form mentioned-vars st))
  ;;; (debug-dump "\n shrinking var: shrink-var-removed-st: ~a" var-removed-st)
  (define domain-enforced-st var-removed-st)
  ;;;  we remove none-substed appearances of unmentioned var
  ;;; TODO : abstract this part away -- 
  ;;;   "unmentioned-totally-removed" replace those constraints into True
  (define unmentioned-removed-st (unmentioned-totally-removed mentioned-vars domain-enforced-st))
  ;;; (debug-dump "\n shrinking var: remove unmention in type/ineq-cst: ~a" unmentioned-removed-st)
  ;;; then we eliminate tproj

  ;;; (define tproj-eliminated (eliminate-tproj-return-record unmentioned-removed-st))
  ;;; (define tproj-eliminated-content (car tproj-eliminated))
  ;;; (define tproj-eliminated-evidence (cdr tproj-eliminated))
  ;;; (valid-type-constraints-check
  ;;;   (unifies-equations tproj-eliminated-evidence tproj-eliminated-content))
  
  (let* ([eliminated-tproj-st (eliminate-tproj-in-st unmentioned-removed-st)]
         [k (debug-dump "  eliminated-tproj-st: ~a\n" eliminated-tproj-st)])
    (valid-type-constraints-check eliminated-tproj-st))
  
)

;;; the same shrink-away but don't require much precondition
;;; return a stream of states
;;;   where the stream is equivalent to the states of clearing
;;;   also remove things from scope
(define/contract (clear-about state0 scope v)
  (state? set? var? . -> . any?)
  ;;; TODO: I will just currently make this assumption to empty...
  
  (define dnf-sym-stream (TO-DNF (TO-NON-Asymmetric '() (wrap-state-stream state0))))
  (debug-dump "\n clearing about: input sttate0 ~a" state0)
  (define mentioned-var (set-remove scope v))
  (define (map-clear-about st)
    (let* (
        [current-vars scope]
        [field-projected-st (field-proj-form st)]
        [domain-enforced-st (domain-enforcement-st field-projected-st)]
        [unmention-substed-st  domain-enforced-st]
        [k (begin   
                    (debug-dump "\n clearing about: current-vars ~a" current-vars)
                    (debug-dump "\n clearing about: input state0 ~a" state0)
                    (debug-dump "\n clearing about: sub-state ~a" st)
                    (debug-dump "\n clearing about: field-projected-st : ~a" field-projected-st)
                    (debug-dump "\n clearing about: domain-enforced-st: ~a" domain-enforced-st)
                    (debug-dump "\n clearing about: unmention-substed-st: ~a" unmention-substed-st)
                    ;;; (debug-dump "\n complemented goal: ")(debug-dump st-scoped-w/ov)
                    ;;; (debug-dump "\n next state ") (debug-dump next-st) 
                    ;;; (debug-dump "\n search with domain on var ")
                    ;;; (debug-dump v) (debug-dump " in ") (debug-dump cgoal) 
                    (debug-dump "\n"))
                    ] 
        [shrinked-st (shrink-away domain-enforced-st current-vars v)]
        [valid-shrinked-st (valid-type-constraints-check shrinked-st)] ;;; remove unnecessary information
        [k (begin  
                    (debug-dump "\n clearing about: shrinked-st on ~a: ~a" v shrinked-st) 
                    ;;; (debug-dump "\n complemented goal: ")(debug-dump st-scoped-w/ov)
                    ;;; (debug-dump "\n next state ") (debug-dump next-st) 
                    ;;; (debug-dump "\n search with domain on var ")
                    ;;; (debug-dump v) (debug-dump " in ") (debug-dump cgoal) 
                    (debug-dump "\n"))
                    ] 
        )
      (wrap-state-stream valid-shrinked-st)))
  (mapped-stream map-clear-about dnf-sym-stream)
)

;;; include mk-syntax here as we turns out need those things here as well
;;;     not only useful for the users

(include "mk-syntax.rkt")