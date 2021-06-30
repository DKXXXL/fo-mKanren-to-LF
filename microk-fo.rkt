#lang racket
(provide
  (all-from-out "microk-fo-unify.rkt")
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
  (struct-out type-constraint)
  ;;; no type constraint, only allow (not-)symbolo
  ;;; (struct-out type-constraint)
  


  (struct-out mplus)
  (struct-out bind)
  (struct-out pause)
  for-all
  for-bound
  for-bounds
  symbolo
  numbero
  stringo
  
  not-symbolo
  not-numbero
  not-stringo
  
  step
  mature
  mature?
  ;;; walk*/goal

  vars-member?
  vars-missing?
  goal-vars
  

  syntactical-simplify
  complement
  ;;; forall-into-disj-1
  ;;; replace-1-to-0

  ==

  define-relation
  fresh
  conde
  query
  run
  run/state
  run*

  subst

  conj*
  disj*

  simplify-dec+nondec
  decidable-goal?

  reify/initial-var/state
  )

(require "microk-fo-unify.rkt")
(require "microk-fo-def.rkt")
(require "proof-term.rkt")
;;; (require errortrace)


;;; The following are for functionality of error-trace

;;; (instrumenting-enabled #t)
;;; (profiling-enabled #t)
;;; (profiling-record-enabled #t)
;;; (execute-counts-enabled #t)
;;; (coverage-counts-enabled #t)


;;; used for contract
;;; TODO: change to better things
(define (any? _) #t)





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


(define (collect-all-that pred anything)
  (define result (mutable-set))
  (define (each-case rec-parent rec g)
    (match g
      [(? pred) (begin (set-add! result g) (rec-parent g))] ;; local side-effect
      [o/w (rec-parent g)]
    )
  )
  (define result-f 
    (compose-maps (list each-case goal-term-base-map pair-base-map state-base-endo-functor hash-key-value-map identity-endo-functor))
  )
  (result-f anything)
  result
)

;;; currently implemented with side-effect,
;;;   it is another kind of fold but I am bad at recursion scheme
;;;   basically return all variables appearing inside g
(define (goal-vars g)
  (define fvs (mutable-set))
  (define (counter rec-parent rec-root g)
    (match g
      [(? var?) (begin (set-add! fvs g) g)]
      [(tproj x _) (begin (set-add! fvs x) g)]
      [_ (rec-parent g)]
    )
  )

  (define g-visitor 
    (compose-maps (list counter goal-term-base-map pair-base-map state-base-endo-functor identity-endo-functor))
  )

  (g-visitor g)
  fvs
)



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
        (conj* (== a c) (== b d))] 
      [(cons (=/= a b) (=/= c d))
        (conj* (== a c) (== b d))]
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
      [(cons (Bottom) (Bottom))
        (wrap-state-stream st)]
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
(define/contract (simplify-dec+nondec g_)
  (Goal? . -> . pair?)
  (define g (all-linear-simplify g_))
  (if (decidable-goal? g)
      `(,g . ,(Top))
      (match-let* ([(cons a b) (split-dec+nondec g)])
        `(,(all-linear-simplify a) . ,(all-linear-simplify b)))
  )   
)



;;; if a stream is WHNF(?)  
(define (mature? s)
    (or (not s) (pair? s)))


(define (not-state? x) (not (state? x)))

;;; return a whnf of stream
(define (mature s)
    ;;; (Stream? . -> . Stream?)
    ;;; (assert-or-warn (not-state? s) "It is not supposed to be a state here")
    ;;; (debug-dump-off "\n maturing: ~a" s)
    (cond
      [(Stream? s)     (if (mature? s) s (mature (step s)))]
      [(GoalStream? s) (if (mature? s) s (mature (step-goal-stream s)))])
    )
  

;;; given a stream of states, 
;;;   return another stream of states 
;;;   make sure there is no disjunction in meaning of each state and 
;;;     all the disjunction are lifted to mplus
;;;  semantic of to-dnf
(define/contract (TO-DNF stream)
  (Stream? . -> . Stream?)
  ;;; (debug-dump-off "TO-DNF computing \n")
  (mapped-stream (lambda (st) (to-dnf st (get-state-DNF-initial-index st))) stream))


;;; return an equivalent stream of state
;;;   where each state has no assymetrical inequality inside 
;;;     i.e. we won't have ((cons a b) =/= y)
;;;         instead we will have (a =/= y.1) \/ (b =/= y.2) together with y = (y.1, y.2)
;;;           note: y.1, y.2 are both fresh variables (instead of tproj) 
;;;       of course together with the stream y is not even a pair
(define/contract (TO-NON-Asymmetric assmpt stream)
  (assumption-base? Stream? . -> . Stream?)
  ;;; (debug-dump-off "TO-NON-Asymmetric computing \n")
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
          ;;; Note! Here (Bottom? g) is important -- we only invoke syn solve
          ;;;   if ultimate goal is bottom and relate
          ;;;   that means when target goal is a simple goal, then we won't invoke
          ;;;   syn solve and try to falsify the assumption 
         (not (empty-assumption-base? assmpt))))
  
  (if heuristic-to-syn-solve 
      (debug-dump "  \n Currently solving ~a \n with assumption ~a \n and state ~a \n" g (map cdr assmpt) st)
      (void))

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
          (let* (
              [split-goal (conj (cimpl a g) (cimpl b g))]
              [reduced-assmpt (filter (lambda (x) (not (equal? top-name-assmpt x))) init-assmpt)]
              [w/-disj  (pause reduced-assmpt st split-goal)]
              [w/o-disj (syn-solve remain-assmpt init-assmpt st g)]    
              )
            (mplus w/-disj w/o-disj))]
      [(cimpl a b)
          (fresh-param (applied)
            (let* (
                [st  st]
                [k (debug-dump "\n ENTERING!!  ")]

                [reduced-assmpt (filter (lambda (x) (not (equal? top-name-assmpt x))) init-assmpt)]
                [new-assmpt (cons-assmpt applied b reduced-assmpt)]
                [w/-cimpl
                  (mapped-stream
                    (λ (st) (pause init-assmpt st a))
                    (pause new-assmpt st g))]
                [w/o-cimpl
                  (syn-solve remain-assmpt init-assmpt st g)]
                [k (debug-dump "\n w/-cimpl ~a \n  " (pause new-assmpt st g))]
    
              )
              (mplus w/-cimpl w/o-cimpl)
            ))]
      [(ex v t)
      ;;; the key idea is that
      ;;; ((forall v (R . cimpl . g)) and (ex v R)) . cimpl . g
            (let* (
                [subgoal-ty (for-all (x) ( (t . subst . [x // v]) . cimpl . g ))]
                [k (debug-dump-off "\n syn-solve on exists: Before ~a \n                    After ~a \n" top-assmpt subgoal-ty)]
            ;;; remove that existential assumption as well
            ;;; TODO: apparently there are some duplicate computation, 
            ;;;   with these unremoved assumption before top assmpt
            ;;;     (because the new subgoal-ty barely changed)
                [reduced-assmpt (filter (λ (a) (not (equal? top-name-assmpt a))) init-assmpt)]
                )
              (mplus 
                (syn-solve remain-assmpt init-assmpt st g)
                (pause reduced-assmpt st subgoal-ty)))]
      [(forall v domain t)
            (fresh-param (applied-term)
            (let* (
                [VT (fresh-var VT)]
                [forall-internal (cimpl domain t)]
                [applied-type (forall-internal . subst . [VT // v])]
                [k (debug-dump "\n syn-solve on forall:~a \n" applied-type)]
                ;;; Note: even though we seem to only allow for-all to be instantiated
                ;;;     with only one variable
                ;;;       the second instantiation will happen when our
                ;;;     proving goal is shifted from g
                [new-assmpt (cons-assmpt applied-term applied-type remain-assmpt)]
                    )
               
                (syn-solve new-assmpt init-assmpt st g)) )]
      ;;; atomic prop! just ignore them
      [o/w 

        (begin
          (debug-dump-off "\n Fail To Destruct Assumption ~a \n" top-assmpt)
          (syn-solve remain-assmpt init-assmpt st g))]
    )
  )

  (if (empty-assumption-base? assmpt)
    (and (ormap has-relate (all-assumption-goals init-assmpt)) 
         (unfold-assumption-solve init-assmpt st g)) 
    ;; TODO: change to re-invokable stream
    ;;; currently we expand the assumption to extract more information
    (match-let* 
        ([(cons (cons term-name ag) remain-assmpt) 
            (iter-assumption-base assmpt)]
         [if-top-level-match (unify/goal ag g st)] ;;; type: Stream?
         [if-top-level-match-filled if-top-level-match];;; fill the current proof term
        )
      (if if-top-level-match
          (begin
            (debug-dump "\n syn-solving assmpt: ~a" assmpt)
            (debug-dump "\n syn-solving goal: ~a" g)
            (debug-dump "\n Extra Matching: ~a ~a" ag g)
            (mplus if-top-level-match-filled
                (traversal-on-assmpt term-name ag remain-assmpt)))
          (begin
            (debug-dump "\n syn-solving assmpt: ~a" assmpt)
            (debug-dump "\n syn-solving goal: ~a" g)
            (debug-dump "\n Failed Matching: ~a ~a" ag g)
            (traversal-on-assmpt term-name ag remain-assmpt)))
    )
  )
)

;;; Also no proof-term generation for this part
;;;   unfold one-level of relation inside g
(define/contract (unfold-one-level-relate g)
  (Goal? . -> . Goal?)  
  (define (each-case rec-parent rec g)
    (match g
      [(relate thunk description) 
        (begin 
          (debug-dump-off "  Before Unfold : ~a \n After Unfold ~a \n" g (apply thunk (cdr description)))
          (apply thunk (cdr description)))] 
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
          [(relate _ _) (begin (set! result #t) g)] 
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
  (debug-dump " \n Before Unfold Assumption : ~a \n" conj-assumpt-ty)
  (define unfold-conj-assumpt-ty (unfold-one-level-relate conj-assumpt-ty))
  (define s-unfold-conj-assmpt-ty (all-linear-simplify unfold-conj-assumpt-ty st))

  (define unfolded-goal (cimpl-no-falsification s-unfold-conj-assmpt-ty goal)) 
  (debug-dump " \n After Unfold Assumption : ~a \n" s-unfold-conj-assmpt-ty)
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
  (debug-dump-off "  semantic-solving goal: ~a\n" (syntactical-simplify g))
  (and st ;;; always circuit the st
    (match g
    ;;; ((disj-1 g1 g2)
    ;;;  (step (mplus-1 (pause assmpt st g1)
    ;;;                 (pause assmpt st g2))))
    ((disj g1 g2)
     (step (mplus (pause assmpt st g1)
                  (pause assmpt st g2))))
    ((conj g1 g2)
    ;;; will add g1 into assumption when solving g2
    ;;;   different from cimpl that state will be impacted after solving g1
       (step (bind assmpt (pause assmpt st g1) g2)))
    ;;; the real syntactical solving for cimpl
    ((cimpl-syn g1 g2)
      (fresh-param (name-g1)
          (debug-dump "  \n ENTERING SEM_SOLVING cimpl-syn with ~a \n" g)
          (step (pause (cons-assmpt name-g1 g1 assmpt) st g2))
      ))
    ((cimpl g1 g2) 
      ;;; semantic solving of implication is 
      ;;;  g1 = g1-dec /\ g1-ndec
      ;;;     g1 -> g2 = g1-dec -> (g1-ndec -> g2)
      ;;;     = ~g1-dec \/ 
      ;;; [g1-dec /\ (g1-ndec -> bot)] \/ 
      ;;; [g1-dec /\ (g1-ndec -> g2)]
     
      ;;; TODO: rewrite the following into ANF-style (the push-let form)
      (match-let* 
            ([(cons g1-dec g1-ndec) (simplify-dec+nondec g1)]
             [k (debug-dump "\n dec comp: ~a \n undec comp ~a \n    want to solve goal ~a \n \n with state ~a" g1-dec g1-ndec g2 st)]
             [~g1-dec-ty (complement g1-dec)]
             [cimpl-syn-short-circuit 
                (λ (antc conseq) (if (equal? antc (Top)) conseq (cimpl-syn antc conseq)))]
             [try-falsification-goal 
                (if (cimpl-no-falsification? g) 
                    (Bottom)
                    (cimpl-syn g1-ndec (Bottom)))]
             [main-goal
                  (conj g1-dec 
                      (disj* 
                        try-falsification-goal ;;; and syntactical falsifying 
                        (cimpl-syn g1-ndec g2)      ;;; and syntactical solving
                        ))]
             [simpl-main-goal (all-linear-simplify main-goal st)]
             [k (debug-dump "  \n Syntactical solving goal ~a \n   simplified into ~a \n" main-goal simpl-main-goal)]
            )
        (mplus*
          (pause assmpt st ~g1-dec-ty)
          ;;; A -> bot /\ A
          ;;; Note: the following decides the soundness of the whole algorithm
          ;;;     because without it, we may not expand the definition of assumption
          ;;;     and really falsifying it
          (pause assmpt st simpl-main-goal)) 
 
    ))
    
    ((relate thunk descript)
      (pause assmpt st (apply thunk (cdr descript))))
    ((== t1 t2) (unify t1 t2 st))
    ((=/= t1 t2) (neg-unify t1 t2 st))

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
          [solving-gn (pause assmpt scoped-st gn)]
          ;;; we pop added scope information
          ;;;  and then make sure v become ground term (by using force-v-ground)
          ;;;  so that proof-term filling can succeed
          [remove-scoped-stream (mapped-stream remove-from-scope-stream solving-gn)]
          )
         remove-scoped-stream))

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
            ;;;  (k (begin (debug-dump-off "\n ~a : domain_ : ~a " var domain_)))
             ] 

        (match domain_

          ;;; in the bottom case, we know domain is simply unsatisfiable
          ;;;   thus domain must be empty, goal is trivially satisfied
          [(Bottom) (let* 
                        ([w/scope (state-scope st)]
                         [res (clear-about st (list->set (state-scope st)) var)])
                      res)]
          ;;; in the case that domain is satisfiable, note that
          ;;;     we actually want to check unsatisfiability w.r.t. *var*
          ;;;     so the above checking is actually a safe approximation
          ;;;   to find out the variable assignment of other variables so that
          ;;;     *var* is unsatisfiable, we need an unsatisfiable check
          [_ 
            
              (mplus*
                ;;; unsatisfiability check
                ;;; (let ([newv (fresh-var var)])
                ;;;   (unsatisfiable-wrt assmpt newv (domain_ . subst . [newv // var]) st)
                ;;; )
                (unsatisfiable-wrt assmpt var domain_ st)
                ;;; body check
                (bind-forall  assmpt
                            (set-add (state-scope st) var)
                            ;;; NOTE: the following "(ex var ..)" ex var is non-trivial and not removable.
                            ;;;     which is explicitly handling the scoped var
                            (TO-DNF (TO-NON-Asymmetric assmpt (pause assmpt st (ex var (conj domain_ goal)))) )
                            var 
                            (forall var domain_ goal))
                            
                )]
        )
      )
    )
    ((Top) (wrap-state-stream st))
    ((Bottom) (wrap-state-stream #f))
    ))
)
  
(define/contract (step-goal-stream s)
  (GoalStream? . -> . GoalStream?)
  (match s 
    [(disj-goal-stream s1 s2)
      (let ((s1 (if (mature? s1) s1 (step-goal-stream s1))))
            (cond ((not s1) s2)
                  ((pair? s1)
                    (cons (car s1)
                          (disj-goal-stream s2 (cdr s1))))
                  (else (disj-goal-stream s2 s1))))]
    [(conj-goal-stream s1 s2)
      (cond 
        [(not (mature? s1)) (conj-goal-stream (step-goal-stream s1) s2)]
        [(not s1) #f]
        [(not (mature? s2)) (conj-goal-stream s1 (step-goal-stream s2))]
        [(not s2) #f]
        [#t
          (match (cons s1 s2)
            [(cons (cons k1 s1r) (cons k2 s2r))
                (cons 
                  (all-linear-simplify (conj k1 k2))
                  (disj-goal-stream* 
                    (conj-goal-stream (wrap-goal-stream k1) s2r)
                    (conj-goal-stream s1r (wrap-goal-stream k2))
                    (conj-goal-stream s1r s2r))
                )])])]
    [(negate-st st)
      (cond 
        [(not (null? (state-sub st)))  
            (match-let*
              ([sub (state-sub st)]
               [(cons a b) (car sub)]
               [rest       (cdr sub)])
              (cons (domain-enforcement-goal (=/= a b)) (negate-st (state-sub-set st rest))))]
        [(not (hash-empty? (state-typercd st)))  
            (match-let*
              ([typercds   (state-typercd st)]
              ;;;  [typercds   (if (immutable? typercds) typercds (make-immutable-hash (hash->list typercds)))]
               [first-key      (car (hash-keys typercds))]
               [first-type     (hash-ref typercds first-key)]
               [rest       (hash-remove typercds first-key)]
               [typecst (type-constraint first-key first-type)])
              (cons (domain-enforcement-goal (complement typecst)) (negate-st (state-typercd-set st rest))))]
        [(not (null? (state-diseq st)))
            (match-let*
              ([(cons (cons a b) _) (car (state-diseq st))]
               [rest       (cdr (state-diseq st))])
              (cons (domain-enforcement-goal (== a b)) (negate-st (state-diseq-set st rest))))
          ]

        [#t #f]
      )
    ]
    [(mapped-stream-goal f s)
      (let* ([s (if (mature? s) s (step s))])
          (cond 
            [(not s)   #f]
            [(pair? s) (disj-goal-stream (f (car s)) (mapped-stream-goal f (cdr s)))]
            [#t        (mapped-stream-goal f s)]))]
    [(negate-stream s)
        (let* ([s (if (mature? s) s (step s))])
          (cond 
            [(not s)    (wrap-goal-stream (Top))] ;;; this means end of stream
            [(pair? s)  (conj-goal-stream (negate-st (car s)) (negate-stream (cdr s)))]
            [#t         (negate-stream (step s))]))]
  )

)


(define/contract (step s)
  (Stream? . -> . Stream?)
  ;;; (debug-dump-off "\n       step: I am going through ~a" s)
  (match s
    ;;; ((mplus-1 s1 s2)
    ;;;  (let ((s1 (if (mature? s1) s1 (step s1))))
    ;;;    (cond ((not s1) s2)
    ;;;          ((pair? s1) 
    ;;;             (if (car s1) (wrap-state-stream (car s1)) (mplus-1 (cdr s1) s2))) 
    ;;;             ;; differs from mplus, we give up searching s2 if we find something non-trivial
    ;;;          (else (mplus-1 s2 s1)))))
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
    ((syn-solve assmpt org-assmpt st g)
     (syn-solving assmpt org-assmpt st g))
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
    ((goal-stream-as-disj assmpt s st)
      (let ((s (if (mature? s) s (step-goal-stream s))))
        (cond 
          ((not s)   #f)
          ((pair? s) (mplus (pause assmpt st (car s))
                            (goal-stream-as-disj assmpt (cdr s) st)))
          (#t        (goal-stream-as-disj assmpt s st))
        )
      ))
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
                  ;;; field projection
                   [field-projected-st (field-proj-form st)]
                  ;;;  idempotent
                   [subst-canonical-st (unmentioned-substed-form mentioned-var field-projected-st)]
                  ;;;  make domain explicit 
                   [domain-enforced-st (domain-enforcement-st subst-canonical-st)]

                   [relative-complemented-goal-original (relative-complement domain-enforced-st current-vars v)]
                   [relative-complemented-goal (all-linear-simplify relative-complemented-goal-original)]
                  ;;;  remove more than one variable is good, make state as small as possible
                   
                  ;;;  domain filter 
                   [shrinked-st (shrink-away subst-canonical-st current-vars v)]
                  ;;;  [next-domain (simplify-domain-wrt assmpt (valid-type-constraints-check shrinked-st) (conj relative-complemented-goal domain) v)]
                  ;;;  [will-next-exit (equal? next-domain (Bottom))]
                  ;;;  [k (begin  

                  ;;;             (if #t
                  ;;;               (begin 
                  ;;;                 (debug-dump-off "\n current assumption base: ~v" assmpt)
                  ;;;                 (debug-dump-off "\n current state initial var: ~v" (reify/initial-var st))
                  ;;;                 (debug-dump-off "\n shrinked state initial var: ~v" (reify/initial-var shrinked-st))
                  ;;;                 (debug-dump-off "\n current state: ~v" st)
                  ;;;                 (debug-dump-off "\n following stream: ~v" (cdr s))
                  ;;;                 (debug-dump-off "\n field-projected-st: ~a"  field-projected-st)
                  ;;;                 ;;; (debug-dump-off "\n field-projected-st initial var: ~a" (reify/initial-var (eliminate-tproj-in-st field-projected-st)))
                  ;;;                 (debug-dump-off "\n subst-canonical-st: ~a" subst-canonical-st)
                  ;;;                 ;;; (debug-dump-off "\n unmention-substed-st initial var: ~a" (reify/initial-var (eliminate-tproj-in-st unmention-substed-st)))
                  ;;;                 (debug-dump-off "\n domain-enforced-st: ~a" domain-enforced-st)
                  ;;;                 ;;; (debug-dump-off "\n domain-enforced-st initial var: ~a" (reify/initial-var (eliminate-tproj-in-st domain-enforced-st)))

                  ;;;                 (debug-dump-off "\n relative-complemented-goal: ~v" relative-complemented-goal)
                  ;;;                 (debug-dump-off "\n relative-complemented-goal-original: ~v  on ~a" relative-complemented-goal-original v)
                  ;;;                 (debug-dump-off "\n shrinked-st on ~s: ~v \n \n" v shrinked-st) 
                  ;;;               )
                  ;;;               '()
                  ;;;             )


                  ;;;             )
                  ;;;             ]
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
      [(ex a gn)  (forall a (Top) (c gn))]
      [(forall v bound gn) ;; forall v. bound => g
        (ex v (conj bound (complement gn))) ]
      [(type-constraint t types) 
        (disj (type-constraint t (set-subtract all-inf-type-label types)) (is-of-finite-type t))]
      [(Top) (Bottom)]
      [(Bottom) (Top)]
    )
  )
)

;;; (define/contract (complement-st st)
;;;   (state? . -> . Stream?)
;;;   (define dnf-stream (TO-DNF st))
;;;   (define/contract (complement-each-st st)
;;;     (state? . -> . state?)
;;;     (define new-equalities (map (state-diseq st) car))
;;;     (define new-inequalities (state-sub st))
;;;   )
;;; )


;;; Find a variable assignment for all the vars except for *var*
;;;  s.t. goal is unsatisfiable for arbitrary var 
(define/contract (unsatisfiable-wrt assmpt var goal st)
  (assumption-base? var? decidable-goal? state? . -> . Stream?)
  (debug-dump-off "  unsatisfiable-wrt ~a ~a \n unsatisfiable-wrt ~a \n" var goal st)

  (define current-scope (set-remove (list->set (state-scope st)) var))
  ;;; transform goal into canonical states
  ;;;  also in DNF form
  (define goal-as-stream (pause empty-assumption-base empty-state (all-linear-simplify goal)))
  (debug-dump-off "  unsatisfiable-wrt negating: ~a \n" (all-mature-to-list goal-as-stream))
  (define negated-goal-as-stream-except-v (negate-except-var goal-as-stream current-scope var))

  (goal-stream-as-disj assmpt negated-goal-as-stream-except-v st)
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
  (if (first-non-empty-mature (pause empty-assumption-base st goal)) (all-linear-simplify goal) (Bottom))
  
  )

;;; some trivial rewrite to make goal easier/reable
;;;     equivalence is ensured
(define/contract (syntactical-simplify goal)
  (Goal? . -> . Goal?)
  (define (basic-tactic rec-parent rec goal)
    (define prev-result (rec-parent goal))
    (define singlerewrite 
      (match prev-result
        ;;; Because we are more likely to have Bottom
        ;;;     so we make those related to bottom at the top.
        [(conj x (Bottom)) (Bottom)]
        [(conj (Bottom) x) (Bottom)]
        [(disj (Bottom) x) x]
        [(disj x (Bottom)) x]
        [(cimpl (Bottom) x) (Top)]
        [(ex _ (Bottom)) (Bottom)]
        [(forall _ (Bottom) _) (Top)]
        [(forall _ (Top) (Bottom)) (Bottom)]
        [(conj (Top) x) x]
        [(conj x (Top)) x]
        [(disj (Top) x) (Top)]
        [(disj x (Top)) (Top)]
        [(conj x x) x]
        [(disj x x) x]
        [(cimpl x (Top)) (Top)]
        [(cimpl (Top) x) x]
        [(ex _ (Top)) (Top)]
        [(forall _ _ (Top)) (Top)]
        [_ 'rewrite-failed]
      )
    )
    (if (equal? singlerewrite 'rewrite-failed) prev-result (rec singlerewrite))
  )
  ((compose-maps (list basic-tactic goal-base-map  identity-endo-functor)) goal)
)

(define (all-mature-to-list stream)
  (let* ([stream (mature stream)])
    (cond
      [(not stream) '()]
      [(pair? stream) (cons (car stream) (all-mature-to-list (cdr stream)))]))
)

;;; estimate evaluation -- will evaluate taking st as upperbound of state
;;;   and return an upperbound of the resulting state
;;;   looks like a partial evaluation 
;;; precond: st as the upperbound of what goal will be solved upon
;;; 
(define/contract (est-eval goal st)
  (Goal? (or/c state? false/c) . -> . (cons/c Goal? (or/c state? false/c)))
  (define (all-mature stream)
    (if (mature? stream)
      (cons (car stream) (all-mature (cdr stream)))
      (mature stream)))
  (define (get-state-out-of-at-most-singleton-stream stream)
    (match stream 
      [(cons sth #f) sth]
      [#f #f]))

  (define (disj-merge-st st1 st2 orgst)
    (cond 
      [(not st1) st2]
      [(not st2) st1]
      [#t orgst]))

  (define result
    (if (not st)
      (cons (Bottom) #f)
      (match goal
        [(Top) (cons goal st)]
        [(Bottom) (cons goal #f)]
        [(conj a b) 
          (match-let* 
            ([(cons new-a st1) (est-eval a st)]
             [(cons new-b st2) (est-eval b st1)]
             [final-goal       (conj new-a new-b)])
            (cons final-goal st2))]
        [(disj a b)
          (match-let* 
            ([(cons new-a st-l) (est-eval a st)]
             [(cons new-b st-r) (est-eval b st)]
             [resulting-st      (disj-merge-st st-l st-r st)] ; merge to top of all the state
             [final-goal        (disj new-a new-b)])
            (cons final-goal resulting-st))]
        [(cimpl-no-falsification a b)
          (match-let* 
            ([(cons new-a _) (est-eval a st)]
             [(cons new-b _) (est-eval b st)]
             [resulting-st      st] ; merge to top of all the state
             [final-goal        (cimpl-no-falsification new-a new-b)])
            (cons final-goal resulting-st))]
        [(cimpl-syn a b)
          (match-let* 
            ([(cons new-a _) (est-eval a st)]
             [(cons new-b _) (est-eval b st)]
             [resulting-st      st] ; merge to top of all the state
             [final-goal        (cimpl-syn new-a new-b)])
            (cons final-goal resulting-st))]
        [(cimpl a b)
          (match-let* 
            ([(cons new-a _) (est-eval a st)]
             [(cons new-b _) (est-eval b st)]
             [resulting-st      st] ; merge to top of all the state
             [final-goal        (cimpl new-a new-b)])
            (cons final-goal resulting-st))]
        [(relate _ _) ; do nothing, otherwise how to terminate
          (cons goal st)]
        [(ex v g)
          (match-let* 
            ([(cons new-g new-st) (est-eval g st)]
             [resulting-st (and new-st st)])
            (cons (ex v new-g) resulting-st))]
        [(forall v d g)
          (match-let* 
            ([(cons (cimpl new-d new-g) new-st) (est-eval (cimpl d g) st)]
             [resulting-st (and new-st st)])
            (cons (forall v new-d new-g) resulting-st))
          ;;; (cons goal st)
          ]
        [_
          (let*
            ([k (debug-dump-off "  est-simplify on : ~a \n" goal)]
              ;;; since it is over estimation, we use equality rewrite here
            ;;;  [sub (state-sub st)]
            ;;;  [all-appearing-vars (goal-vars goal)]
            ;;;  [var-mapping 
            ;;;     (for/fold
            ;;;       ([acc (hash)])
            ;;;       ([each all-appearing-vars])
            ;;;       (let ([eachto (walk* each sub)])
            ;;;         (if (equal? each eachto)
            ;;;           acc
            ;;;           (hash-set acc each eachto))))]
            ;;;  [new-goal (literal-replace* var-mapping goal)]
            ;;;   why above is unsound?
             [new-goal goal]
             [all-states   (all-mature (pause '() st new-goal))]
             [actually-one (get-state-out-of-at-most-singleton-stream all-states)])
            (cons new-goal actually-one))]
        )
    ))
    ;;;  we make sure returns bottom if returning state is #f
    (if (not (cdr result))
        (cons (Bottom) #f)
        result)
)


;;; include all the simplification that 
;;;   only linear complexity to the size of g 
(define (all-linear-simplify g [state-init empty-state])
  ;;; (Goal? . -> . Goal?)
  (syntactical-simplify (est-simplify g state-init))
  ;;; (syntactical-simplify g)
)

(define/contract (est-simplify goal state-init)
  (Goal? state? . -> . Goal?)
  (match (est-eval goal state-init)
    [(cons res-g _) res-g]))





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
        #:when (hash-has-key? mapping x) ;;(not (equal? (hash-ref mapping x 'LITERAL-REPLACE-UNFOUND) 'LITERAL-REPLACE-UNFOUND))
        (walk* (hash-ref mapping x) subst-mapping) ]
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
               [new-mapping (make-immutable-hash new-hash-list)]
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
      (let ([smap (make-immutable-hash `((,from . ,to) ... ))])
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
  (define inequalities
    (foldl append '() (state-diseq st0)))
  (define recorded-vars
    (for/fold
      ([acc (set)])
      ([each-ineq inequalities])
      (match-let*
        ([(cons l r) each-ineq]
         [acc1 (if (and (var? l) (pair? r)) (set-add acc l) acc)]
         [acc2 (if (and (var? r) (pair? l)) (set-add acc1 r) acc1)])
        acc2)))
  ;;; (define (each-asymmetry rec-parent rec g)
  ;;;   (match g
  ;;;     ;;; thiss pattern matching i a bit dangerous
  ;;;     ;;; TODO: make equation/inequality into a struct so that pattern-matching can be easier
  ;;;     [(? (cons/c var? pair?)) 
  ;;;         (let* ([v (car g)])
  ;;;             (set-add! each-asymmetry-record! v)
  ;;;             g
  ;;;                )]
  ;;;     [(? (cons/c pair? var?)) 
  ;;;         (let* ([v (cdr g)])
  ;;;             (set-add! each-asymmetry-record! v)
  ;;;             g)]
  ;;;     [_ (rec-parent g)]

  ;;;   )
  ;;; )

  ;;; (define each-asymmetry-recorder
  ;;;   (compose-maps (list each-asymmetry pair-base-map identity-endo-functor))
  ;;; )
  ;;; (each-asymmetry-recorder (state-diseq st0))
  (set->list recorded-vars)
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
      ;;;  (type-constraint v (set pair?))
       (fresh (va vb) (== v (cons va vb)))  
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
  (debug-dump-off "\n assymetric-st:  ~a \n asymmetric-vars: ~a \n" st asymmetric-vars)
  (if (equal? (length asymmetric-vars) 0)
    (wrap-state-stream st)
    (mapped-stream (lambda (st) (remove-assymetry-in-diseq assmpt st)) (pair-or-not-pair-by-axiom assmpt asymmetric-vars st))))


;;;  Recall the definition of tproj:
;;; tproj :: var x List of ['car, 'cdr] 
;;; cxr as a path/stack of field projection/query
;;; (struct tproj (v cxr) #:prefab)
;;; (struct tcar (term) #:prefab)
;;; (struct tcdr (term) #:prefab)






;;; given a tproj, we construct a tproj-ectable term for it
;;;  return the equation for removing the tproj
;;; tproj -> pair as var, cons/tree of vars
;;;  example: a tproj-able term for (x.car.cdr == ..) 
;;;     will become (x == ((a b) c)) (a == ...) 
(define (equation-for-remove-tproj x)
  ;;; (define field-projection-list (tproj-cxr x))
  (match-let* 
    ([(cons var-cons-map _) (proj-free-equations-for-tproj (list x))])
    (car var-cons-map))
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
        (match-let* 
              ([oldvar  (hash-ref tp-to-var tp #f)]
               [(tproj v cxr) tp]
               [maybe-newvar  (if oldvar oldvar (tp-var v cxr))])
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


;;; transform every tp-var into a tproj inside st
(define/contract (tp-var-to-normal-var st)
  (state? . -> . state?)
  (define tp-var-to-var-hash (make-hash))
  (define (tp-var-to-var tpv)
    (if (hash-has-key? tp-var-to-var-hash tpv)
      (hash-ref tp-var-to-var-hash tpv)
      (let* ([newname (string->symbol (format "~a" tpv))]
               [vtpv    (var/fresh newname)]
               [_       (hash-set! tp-var-to-var-hash tpv vtpv)])
          vtpv)))
  (define (each-case rec-parent rec g)
    (match g
      [(tp-var _ _) (tp-var-to-var g)] 
      [o/w (rec-parent g)]))
  (define result-f 
    (compose-maps (list each-case goal-term-base-map pair-base-map state-base-endo-functor hash-key-value-map identity-endo-functor)))
  (result-f st)
)



;;; given a set of equation 
;;;  return an equivalent set of equation 
;;;  s.t. each equation won't have pair inside, and at each side of
;;;     one equation there is only one var
(define/contract (field-proj-form st)
  (state? . -> . state?)
  (define tp-free-st (tp-var-to-normal-var st))
  (define eqs (state-sub tp-free-st))

  (state-sub-set tp-free-st (eliminate-conses eqs))
)

;;; given a set of equations 
;;;  return an equivalent set of equations, with no pair inside 
;;;  also no duplicate form, i.e. a and a._1 won't appear together
;;;     but only tproj inside
;;; precondition: eqs is actually a substitution list
;;; precondition: no tproj in the beginning
(define (eliminate-conses eqs)
  ((list/c pair?) . -> . (list/c pair?))
  ;;; canonicalize all the variables, i.e. collect all variables and walk* them
  (define all-vars (set->list (goal-vars eqs)))
  ;;; (assert-or-warn (not (equal? (length all-vars) 0)) "\n eliminate-conses found no vars")
  (define each-var-canon-from
    (map (λ (t) (cons t (walk* t eqs))) all-vars))


  (define atomic-form? (or/c tproj? var?))
  (define (fst-eq eq) (cons (tcar (car eq)) (tcar (cdr eq))))
  (define (snd-eq eq) (cons (tcdr (car eq)) (tcdr (cdr eq))))

  ;;; given an equaition of var and pair, construct 
  (define/contract (var-pair-eq-to-tproj v-p-eq)
    ((cons/c atomic-form? any?) . -> . any?)
    ;;; BUGFIX: contract  
    ;;;   ((cons/c atomic-form? any?) . -> . (or/c null? (list/c pair?)))
    ;;;     is failing
    (define v (car v-p-eq))
    (define p (cdr v-p-eq))
    (if (not (pair? p)) 
        (if (equal? v p) '() (list v-p-eq))
        (append
          (var-pair-eq-to-tproj (fst-eq v-p-eq))
          (var-pair-eq-to-tproj (snd-eq v-p-eq)))))
  (for/fold 
    ([all-eqs       '()])
    ([each-v-p-pair each-var-canon-from])
    (append (var-pair-eq-to-tproj each-v-p-pair) all-eqs)))


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
;;;   return a state, where unmentioned-var are all replaced
;;;   while the original equality class information is untouched
;;;   more concretely
;;;   1. we make sure every equality class takes a mentioned var as representative
;;;   2. every var will be mapped to an equality class representative
;;;   3. in this case, mentioned-var won't be mapped to unmentioned var
;;;   4. but all the information will be the same -- 
;;;         we still have unmentioned-var maps to unmentioned-var
;;;       i.e. equivalent form
;;;   5. the output state will have even its subst list a canonicalized form 
;;;         i.e. each var will be directly mapped to (walk* var)
;;;       thus removing any appearance (of non-representative) will be trivial
;;;         by just syntactically removing it
;;; precondition: in field-proj-form
(define/contract (unmentioned-substed-form mentioned-vars st)
  (set? state? . -> . state?)
  (define sub (state-sub st))
  (define all-terms (collect-all-that (or/c tproj? var?) st))
  (define (is-mentioned? v)
    (vars-member? mentioned-vars v))
  (define (is-unmentioned? v) (not (is-mentioned? v)))
  (define-values (mentioned-terms unmentioned-terms)
    (for/fold 
      ([mentioned (set)] [unmentioned (set)])
      ([each all-terms])
      (values
        (if (is-mentioned? each)
            (set-add mentioned each)
            mentioned)
        (if (is-unmentioned? each)
            (set-add unmentioned each)
            unmentioned))))
  ;;; we get a subst all about mentioned, 
  ;;;     also can considered as a mapping from eac mentioned term to
  ;;;     its representative of equality class
  (define mentioned-subst
    (map (λ (t) (cons t (walk* t sub))) (set->list mentioned-terms)))
  
  (define all-subst
    (map (λ (t) (cons t (walk* t sub))) (set->list all-terms)))

  (debug-dump-off "     unmentioned-substed-form original sub: ~a \n" sub)
  (debug-dump-off "     unmentioned-substed-form after sub: ~a \n" all-subst)
  ;;; we take out all unmentioned-var-representative
  ;;;   find a mapping that will replace them
  (define unmentioned-mapping
    (for/fold
      ([acc (hash)])
      ([each mentioned-subst])
      (match-let* 
        ([(cons L R) each])
        (if (and (set-member? unmentioned-terms R) (not (hash-has-key? acc R))) 
            (hash-set acc R L) 
            acc))))

  (let* 
      ([remove-unmentioned-repr
          (literal-replace* unmentioned-mapping all-subst)]
       [all-subst-with-unmentioned-repr-changed
          (append remove-unmentioned-repr (hash->list unmentioned-mapping))]
       [new-sub
          (filter (λ (t) (not (equal? (car t) (cdr t)))) all-subst-with-unmentioned-repr-changed)]
       [st-w/o-sub      (state-sub-set st empty-sub)]
       [new-st-w/o-sub 
          (literal-replace* unmentioned-mapping st-w/o-sub)]
      ;;;  then remove any constraint on unmentioned stuff
       [new-st (state-sub-set new-st-w/o-sub new-sub)]
      )
      new-st)
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
         [no-unmentioned (lambda (p) (not (vars-missing? mentioned-vars p)))]
         [new-diseq (filter no-unmentioned diseqs)] 
         ;; diseqs must be list of singleton list of thing
         [type-rcd-lst (hash->list (state-typercd domain-enforced-st))]
         [new-typercd-lst (filter no-unmentioned type-rcd-lst)]
         [new-typercd (make-immutable-hash new-typercd-lst)]
         [new-subst   (filter no-unmentioned (state-sub st))]
         )
    (state-sub-set
      (state-diseq-set 
        (state-typercd-set domain-enforced-st new-typercd)
        new-diseq)
        new-subst) )
)


;;; DomainEnforcement -- 
;;;   basically currently make sure if term (tproj x car) appear
;;;     then x is of type pair ((has-type x pair) will appear)
(define (domain-enforcement-st st) ;; (tproj x car.cdr.car) (typeconstant x car) pair
  (define all-tprojs (collect-tprojs st))
  ;;; (debug-dump-off "\n    inside domain-enforcement-st all-tprojs: ~a" all-tprojs)
  (define sub (state-sub st))
  ;;; (tproj v path) x state -> state
  ;;; given a (possibly complicated) tproj, make st enforce on its domain
  ;;;   example, if term = x.car.cdr, then (pair? x), (pair x.car) will both be added
  (define/contract/optional (force-as-pair term st)
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
  (define (force-as-pair v g) (conj (type-constraint v (set pair?)) g))
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
  (collect-all-that tproj? anything)
)



(define/contract (eliminate-tproj-in-st st)
  (state? . -> . state?)
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
  (define tproj-removed (literal-replace* (make-immutable-hash unified-all-tproj-removing-eqs) anything))
  
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

  ;;; we have proj-free-equations-for-tproj to remove tproj
  ;;;     in each atom
  (define/contract/optional (remove-tproj-for-each-rel-atom a)
    (Goal? . -> . Goal?)
    (match-let* 
      ([(cons structure-eqs tproj-hash) (proj-free-equations-for-tproj (set->list (collect-tprojs a)))]
       [struct-eq (foldl (λ (t acc) (conj acc (== (car t) (cdr t)))) (Top) structure-eqs)]
       [new-a     (literal-replace* tproj-hash a)]
      )
      (conj struct-eq new-a)))

  ;;; for those unrelated, we don't touch them 
  (define conj-unrelated 
    (syntactical-simplify 
      (remove-tproj-for-each-rel-atom 
        (foldl conj (Top) atomics-of-var-unrelated))))

  ;;; for those related we need to relative complement, proj-remove 
  ;;;  Note: this following re-application of domain-enforcement is necessary
  ;;;     

  (define complemented-atomics-of-var-related 
    (map complement atomics-of-var-related))
  (define domain-enforced-complemented-atomics-of-var-related 
    (map domain-enforcement-goal complemented-atomics-of-var-related))

  (define tproj-removed-domain-enforced-complemented-atomics-of-var-related
    (map remove-tproj-for-each-rel-atom domain-enforced-complemented-atomics-of-var-related))
  

  (define disj-related 
    (foldl disj (Bottom) tproj-removed-domain-enforced-complemented-atomics-of-var-related))

  (conj conj-unrelated disj-related)
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
  (debug-dump-off "     shrink-away using unmentioned-subst-form: ~a \n" st)
  (define var-removed-st (unmentioned-substed-form mentioned-vars st))
  ;;; (debug-dump-off "\n shrinking var: shrink-var-removed-st: ~a" var-removed-st)
  (define domain-enforced-st var-removed-st)
  ;;;  we remove none-substed appearances of unmentioned var
  ;;; TODO : abstract this part away -- 
  ;;;   "unmentioned-totally-removed" replace those constraints into True
  (define unmentioned-removed-st (unmentioned-totally-removed mentioned-vars domain-enforced-st))
  ;;; (debug-dump-off "\n shrinking var: remove unmention in type/ineq-cst: ~a" unmentioned-removed-st)
  ;;; then we eliminate tproj
  (let* ([eliminated-tproj-st (eliminate-tproj-in-st unmentioned-removed-st)])
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
  ;;; (debug-dump-off "\n clearing about: input sttate0 ~a" state0)
  (define mentioned-var (set-remove scope v))
  (define (map-clear-about st)
    (let* (
        [current-vars scope]
        [field-projected-st (field-proj-form st)]
        [domain-enforced-st (domain-enforcement-st field-projected-st)]
        [unmention-substed-st  domain-enforced-st]
        [shrinked-st (shrink-away domain-enforced-st current-vars v)]
        [valid-shrinked-st (valid-type-constraints-check shrinked-st)] ;;; remove unnecessary information
        [k (debug-dump-off "      clearing-about ~a ~a  \n" v state0)]
        [k (debug-dump-off "      clearing-about-result ~a \n" valid-shrinked-st)]
        )
      (wrap-state-stream valid-shrinked-st)))
  (mapped-stream map-clear-about dnf-sym-stream)
)

;;; negate a given state stream, except for the var *v*
;;;     return the result as a GoalStream 
(define/contract (negate-except-var st-stream scope v)
  (Stream? set? var? . -> . GoalStream?)
  
  (define dnf-sym-stream (TO-DNF (TO-NON-Asymmetric '() st-stream)))
  ;;; (debug-dump-off "\n clearing about: input sttate0 ~a" state0)
  (define mentioned-var (set-remove scope v))
  (define (map-clear-about-in-field-proj st)
    (let* (
        [current-vars scope]
        [field-projected-st (field-proj-form st)]
        [domain-enforced-st (domain-enforcement-st field-projected-st)]
        ;;; [unmention-substed-st  domain-enforced-st]
        ;;; [shrinked-st (shrink-away domain-enforced-st current-vars v)]
        [var-removed-st  (unmentioned-substed-form mentioned-var domain-enforced-st)]
        [unmentioned-removed-st (unmentioned-totally-removed mentioned-var var-removed-st)])
      unmentioned-removed-st))
  (define clear-var-stream (mapped-stream map-clear-about-in-field-proj dnf-sym-stream))

  (debug-dump-off "   clear-var-stream: ~a \n" (all-mature-to-list clear-var-stream))

  (define negate-goals (negate-stream clear-var-stream))
  
  (debug-dump-off "   negating-goals result ~a \n" (all-mature-to-list negate-goals))
  (define negate-goal-stream (goal-stream-as-disj empty-assumption-base negate-goals empty-state))
  
  (debug-dump-off "   negating-goals-to-states result ~a \n" (all-mature-to-list negate-goal-stream))  
  ;;; remove field projection form
  (define negate-goal-stream-fpfree
    (mapped-stream
      (λ (st)
        (valid-type-constraints-check (eliminate-tproj-in-st st))) 
      negate-goal-stream))
  
  (define result 
    (mapped-stream-goal 
      (λ (st)
        (wrap-goal-stream (state->goal st))) 
      negate-goal-stream-fpfree))

  (debug-dump-off "   negating-goals final result ~a \n" (all-mature-to-list result))
  result
  
)



;;; ;;; make every disj that directly scoped by forall
;;; ;;;     transformed into disj-1
;;; (define/contract (forall-into-disj-1 g)
;;;   (Goal? . -> . Goal?)

;;;   (define (case-exist g)
;;;     (define (each-case-exist rec-parent rec g)
;;;       (match g
;;;         [(forall v d b) (forall v d (case-forall b))] 
;;;         [o/w (rec-parent g)]))
;;;       (let ([result-f
;;;             (compose-maps 
;;;                 (list each-case-exist goal-term-base-map pair-base-map identity-endo-functor))])
;;;         (result-f g)))

;;;   (define (case-forall g)
;;;     (define (each-case-forall rec-parent rec g)
;;;       (match g
;;;         [(disj a b)     (disj-1 (rec a) (rec b))]
;;;         [(ex v b)       (ex v (case-exist b))] 
;;;         [o/w (rec-parent g)]))
;;;       (let ([result-f
;;;             (compose-maps 
;;;                 (list each-case-forall goal-term-base-map pair-base-map identity-endo-functor))])
;;;         (result-f g)))

;;;   (case-exist g)
;;; )


(define/contract (symbolo t)
  (any/c . -> . Goal?)
  (type-constraint t (set symbol?))
)


(define/contract (numbero t)
  (any/c . -> . Goal?)
  (type-constraint t (set number?))
)

(define/contract (stringo t)
  (any/c . -> . Goal?)
  (type-constraint t (set string?))
)


(define/contract (not-symbolo t)
  (any/c . -> . Goal?)
  (disj 
    (type-constraint t (set-remove all-inf-type-label symbol?))
    (is-of-finite-type t))
)


(define/contract (not-numbero t)
  (any/c . -> . Goal?)
  (disj 
    (type-constraint t (set-remove all-inf-type-label number?))
    (is-of-finite-type t))
)

(define/contract (not-stringo t)
  (any/c . -> . Goal?)
  (disj 
    (type-constraint t (set-remove all-inf-type-label string?))
    (is-of-finite-type t))
)

;;; reify state

(define (reify/initial-var/state st)
  
  (define everything-related 
    (list initial-var (state-diseq st) (hash-keys (state-typercd st))))

  (match-define (cons var-mapping full-sub)
      (get-sub-for-reify everything-related st))


  (define eq-result (walk* initial-var full-sub))
  
  (define cst-st (state-sub-set st empty-sub))
  (define printing-st (literal-replace* var-mapping cst-st))
  (define printing-cst (syntactical-simplify (state->goal printing-st)))
  (cons eq-result printing-cst)
)


;;; include mk-syntax here as we turns out need those things here as well
;;;     not only useful for the users

(include "mk-syntax.rkt")