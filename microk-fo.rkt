#lang racket
(provide
  (all-from-out "common.rkt")
  (struct-out disj)
  (struct-out conj)
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
  step
  mature
  mature?
  walk*/goal
  

  syntactical-simplify
  replace-1-to-0
  )

(require "common.rkt")
(require errortrace)

(instrumenting-enabled #t)

;; first-order microKanren
;;; goals
(struct disj   (g1 g2) 
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a ∨ ~a)" (disj-g1 val) (disj-g2 val)))]
)

(struct conj   (g1 g2)  
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a ∧ ~a)" (conj-g1 val) (conj-g2 val)))]
)
(struct relate (thunk description)      ;;;#:prefab
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a" (relate-description val)))]
)
(struct ==     (t1 t2)
  #:transparent               
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a =ᴸ ~a" (==-t1 val) (==-t2 val)))]
     ;;; L stands for Lisp Elements
)
(struct ex     (varname g) 
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∃~a. ~a" (ex-varname val) (ex-g val)))]
)
;;; meta-data ex, actually will be ignored at this stage
;;;   indicating the scope of varname, 
;;;   but only as a hint

;;; we need implement the first version of complement,
;;;   so the complement version of each operation need to be defined
(struct =/= (t1 t2)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ≠ᴸ ~a" (=/=-t1 val) (=/=-t2 val)))]
)

(struct forall (varname domain g)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∀~a. ~a" (forall-varname val)  (forall-g val)))]
)

(struct symbolo (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "symbol ~a" (symbolo-t val)))]
)

(struct not-symbolo (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-symbol ~a" (not-symbolo-t val)))]
)


(struct numbero (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "number ~a" (numbero-t val)))]
)

(struct not-numbero (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-number ~a" (not-numbero-t val)))]
)


(struct stringo (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "string ~a" (stringo-t val)))]
)

(struct not-stringo (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-string ~a" (not-stringo-t val)))]
)


;;; haven't decided introduce or not
;;;   details in domain-exhausitive check
;;; (struct pairo (t)
;;;   #:methods gen:custom-write
;;;   [(define (write-proc val output-port output-mode)
;;;      (fprintf output-port "not-string ~a" (not-stringo-t val)))]
;;; )


(struct Top ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "T" ))]
)


(struct Bottom ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "⊥" ))]
)


;;; Denote Goal-EndoFunctor type as
;;;      (goal -> goal) -> (goal -> goal) -> goal -> goal
;;; extensible function on pattern matching
;;;  pretentious "endofunctor" just means it maps goal to goal
;;; goal-base-endofunctor : (goal -> goal) -> (goal -> goal) -> goal -> goal
;;;  prev-f will call the one on the past overloading functor
;;;   extended-f will use the whole composed functor
;;;  this functor will do nothing but recurse on the tree
(define (goal-base-endofunctor prev-f rec g)
  ;;; (define rec extended-f)
  (match g
    [(disj a b) (disj (rec a) (rec b))]
    [(conj a b) (conj (rec a) (rec b))]
    [(ex v g) (ex v (rec g))]
    [(forall v b g) (forall v (rec v) (rec g))]
    [_ (prev-f g)] ;; otherwise do nothing
  )
)


(define (identity-endo-functor prev-f rec g) g)

(define (goal-identity g) g)


;;; this one basically can help me solve the expression problem
;;;   I can extend state as I want now  
;;; [(goal -> goal) -> (goal -> goal) -> goal -> goal] -> (goal -> goal)
(define (overloading-functor-list endofuncs)
  (define (overloading-functor-list-with-extf endofuncs extf)
    (match endofuncs
      [(cons fst then)
        (let* ([prev-f (overloading-functor-list-with-extf then extf)])
          (lambda (g) (fst prev-f extf g))
        )]
      ['() (lambda (x) x)]
    )
  )
  (define (resultf g)
    ((overloading-functor-list-with-extf endofuncs resultf) g) )
  resultf
)

;;; example usage
;;; not-symbolo will be translated into (numbero v stringo v pairo v boolo)
;;; (define remove-neg-by-decidability
;;;   (define (match-single prev-f ext-f g)
;;;     (match g
;;;       [(not-symbolo x) (disj (pairo x) (boolo x) (numbero x) (stringo x))]
;;;       [(not-numbero x) (disj (pairo x) (boolo x) (symbolo x) (stringo x))]
;;;       [(not-stringo x) (disj (pairo x) (boolo x) (numbero x) (symbolo x))]
;;;       [_ (prev-f g)]
;;;     )
;;;   )
;;;   (overloading-functor-list (list match-single goal-base-endofunctor))
;;; )


;;; homomorphism on pair, will respect pair construct
;;;  will also respect tproj
(define (pair-base-endofunctor prev-f extended-f g)
  (define rec extended-f)
  (match g
    ['() '()]
    [(cons a b) (cons (rec a) (rec b))]
    [(tproj tm cxr) (tproj_ (rec tm) cxr)] ;; respect tproj
    [_ (prev-f g)]
  )
)



;;; homomorphism on pair, except that each "composed node" will translate to "or"
;;;   it's just mapping pairs into arithmetic
;;; for example, we have cons and unit in the language of lisp
;;; now you can basically look at it as another AST
;;;   now if we map cons to or, '() to Boolean value, then it is a kind of 
;;;     folding after evaluation
(define (pair-base-functor op-mapping)
  (define (pair-base-functor- prev-f extended-f g)
    (define rec extended-f)
    (match g
      ['() (op-mapping '())]
      [(cons a b) ((op-mapping cons) (rec a) (rec b))]
      [_ (op-mapping 'default )] ;;; otherwise use op-mapping's default
    )
  )
  pair-base-functor-
)


(define there-is-pair-base-mapping
  (hash
    'default #f
    '() #f
    cons (lambda (x y) (or x y)) ;; no short-circuting anymore
  )
)

;;; mapping every cons to or, '() to false, and others to default-v and fold the result
(define (there-is-in-pair-base-functor default-v)
  (define defaulted (hash-set there-is-pair-base-mapping 'default default-v))
  (pair-base-functor (lambda (x) (hash-ref defaulted x 'NotFound))))
  

(define (there-is-vars-in var-indices pair-goal)
  (define (each-case prev-f rec g)
    (match g
      [(var _ index) (member index var-indices)]
      [o/w (prev-f g)]
    )
  )

  (define result-f 
    (overloading-functor-list (list each-case goal-base-endofunctor (there-is-in-pair-base-functor #f)))
  )
  (result-f pair-goal)
)

(define (there-is-var-not-in var-indices pair-goal)
  (define (each-case prev-f rec g)
    (match g
      [(var _ index) (not (member index var-indices))]
      [o/w (prev-f g)]
    )
  )

  (define result-f 
    (overloading-functor-list (list each-case goal-base-endofunctor (there-is-in-pair-base-functor #f)))
  )
  (result-f pair-goal)
)


;;; example : replace 1 with 0 in an arbitrary list
(define (replace-1-to-0 k)
  (define (case1 prev-f extended-f g)
    (if (equal? g 1) 0 (prev-f g)))
  
  ((overloading-functor-list (list case1 pair-base-endofunctor  identity-endo-functor)) k)
)


;;; currently implemented with side-effect,
;;;   it is another kind of fold but I am bad at recursion scheme
;;;   basically return all free-variables
(define (freevar g)
  (define fvs (mutable-set))
  ;;; (define (counter prev-f ext-f g)
  ;;;   (match g
  ;;;     []
  ;;;     [_ (prev-f g)]
  ;;;   )
  ;;; )
  (void)
)

;;; streams
(struct bind   (scope bind-s bind-g)          #:prefab)
(struct mplus  (mplus-s1 mplus-s2)      #:prefab)
(struct pause  (pause-state pause-goal) #:prefab)


;;; the special stream only used for forall
;;;   all the possibe results of first-attempt-s
;;;   will be complemented and intersect with the domain of the bind-g
;;;   bind-g will have to be a forall goal
(struct bind-forall   (scope first-attempt-s dv bind-g)          #:prefab)


(define (mature? s) 
    (or (not s) (pair? s)))
(define (mature s)
    (if (mature? s) s (mature (step s))))
  
(define (total-mature s)
  (match s
    [(cons a b) (cons a (total-mature b))]
    [#f #f]
  )
)


;;; term-finite-type : term x state -> stream
;;;  this will assert t is either #t, #f, or '()
(define (term-finite-type t st)
  (pause st (disj* (== t '()) (== t #t) (== t #f)))
)


;;; run a goal with a given state
;;; note that when st == #f, the returned stream will always be #f
(define/contract (start st g)
  (?state? any? . -> . any?)
  (and st ;;; always circuit the st
    (match g
    ((disj g1 g2)
     (step (mplus (pause (trace-left st) g1)
                  (pause (trace-right st) g2))))
    ((conj g1 g2)
     (step (bind (state-scope st) (pause st g1) g2)))
    ((relate thunk _)
     (pause st (thunk)))
    ((== t1 t2) (unify t1 t2 st))
    ((=/= t1 t2) (neg-unify t1 t2 st))
    ((symbolo t1)  (wrap-state-stream (check-as-inf-type symbol? t1 st)))
    ((not-symbolo t1) 
      (mplus 
        (term-finite-type t1 st)
        (wrap-state-stream (check-as-inf-type-disj (remove symbol? all-inf-type-label) t1 st)))) 
    ((numbero t1) (wrap-state-stream (check-as-inf-type number? t1 st)))
    ((not-numbero t1)  
      (mplus 
        (term-finite-type t1 st)
        (wrap-state-stream (check-as-inf-type-disj (remove number? all-inf-type-label) t1 st)))) 
    ((stringo t1) (wrap-state-stream (check-as-inf-type string? t1 st)))
    ((not-stringo t1)  
      (mplus 
        (term-finite-type t1 st)
        (wrap-state-stream (check-as-inf-type-disj (remove string? all-inf-type-label) t1 st))))
    ((ex v gn) 
      (start (state-scope-update st (lambda (scope) (set-add scope v))) gn))
    ;;; forall is tricky, 
    ;;;   we first use simplification to
    ;;;   we first need to consider forall as just another fresh
    ;;;   and "bind" the complement of result to the nexttime forall as domain
    ;;;   
    ;;; 
    ((forall var domain goal) 
      (let* [(domain_ (simplify-wrt st domain var))
             (k (begin (display var) (display ": domain_: ") (display domain_) (display "\n")))
            ] 

        (match domain_
          [(Bottom) (wrap-state-stream st)]
          [_ (bind-forall (state-scope st) (start st (ex var (conj domain_ goal)))  var (forall var domain_ goal))]
        )
      )
    )
    ((Top) (wrap-state-stream st))
    ((Bottom) (wrap-state-stream #f))
    ))
)
  

(define (step s)
  (match s
    ((mplus s1 s2)
     (let ((s1 (if (mature? s1) s1 (step s1))))
       (cond ((not s1) s2)
             ((pair? s1)
              (cons (car s1)
                    (mplus s2 (cdr s1))))
             (else (mplus s2 s1)))))
    ((bind scope s g)
     (let ((s (if (mature? s) s (step s))))
       (cond ((not s) #f)
             ((pair? s)
              (step (mplus (pause (state-scope-set (car s) scope) g)
                           (bind scope (cdr s) g))))
             (else (bind scope s g)))))
    ;;; bind-forall is a bit complicated
    ;;;   it will first need to collect all possible solution of
    ;;;   s, and complement it, and intersect with 
    ((bind-forall current-vars s v (forall v domain goal))
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
                  ;;;  TODO: figure out trace!
                   [st-scoped-w/v (shrink-into (set-add current-vars v) st)]
                   [st-scoped-w/ov (shrink-into (set-remove current-vars v) st) ]
                   [complemented-goal (syntactical-simplify (complement (extract-goal-about v st-scoped-w/v)))]
                   [(cons next-st cgoal) (eliminate-tproj st-scoped-w/ov complemented-goal)]
                   [k (begin (display " current scope: ")(display current-vars)  
                              (display "\n next state ") (display next-st) (display "\n search with domain on var ")
                              (display v) (display " in ") (display complemented-goal) (display "\n"))]
                    )
              ;;; forall x (== x 3) (== x 3)
              ;;;   forall x (conj (== x 3) (=/= x 3)) (== x 3)
              ;;;  forall x () (symbolo x) /\ (not-symbolo x)
              (step (mplus (pause next-st (forall v (conj cgoal domain) goal))
                           (bind-forall current-vars (cdr s) v (forall v domain goal)))))) ;;; other possible requirements search

        (else (bind-forall current-vars s v (forall v domain goal))))

             ))
    ((pause st g) (start st g))
    (_            s)))


;;; walk*/goals :: Goal x subst -> Goal
;;;  precondition: subst has to be idempotent
(define (walk*/goal goal subst)
  (let* ([rec (lambda (g) (walk*/goal g subst))])
    (match goal
    ;;; non trivial parts
    ;;;   deal with terms
      ((== t1 t2) 
        (== (walk* t1 subst) (walk* t2 subst)))
    ;;; ex needs shadow the exvar
      ((ex exvar gn) 
        (ex exvar (walk*/goal gn (shadow-idempotent-sub exvar subst))))
    ;;; dead recursion on others
      ((disj g1 g2)
        (disj (rec g1) (rec g2)))
      ((conj g1 g2)
        (conj (rec g1) (rec g2)))
      ((relate thunk _)
        (relate (lambda () (rec (thunk)))))
    )
  )
)

;;; trivially negate the goal, relies on the fact that
;;;  we have a dualized goals
(define (complement g)
  (let ([c complement])
    (match g
      [(disj g1 g2) (conj (c g1) (c g2))]
      [(conj g1 g2) (disj (c g1) (c g2))]
      [(relate _ _) (raise "User-Relation not supported.")]
      [(== t1 t2) (=/= t1 t2)]
      [(=/= t1 t2) (== t1 t2)]
      [(ex a gn) (forall a (c gn))]
      [(forall v bound gn) (raise "Not supported complement on higher-ranked.") ]
      [(numbero t) (not-numbero t)]
      [(not-numbero t) (numbero t)]
      [(stringo t) (not-stringo t)]
      [(not-stringo t) (stringo t)]
      [(symbolo t) (not-symbolo t)]
      [(not-symbolo t) (symbolo t)]
      [(Top) (Bottom)]
      [(Bottom) (Top)]
    )
  )
)


;;; following is a none opaque decision procedure for exhaustive domain checking
;;;   one day it needs to be translate to corresponding LF-term 
;;;   for credentials


;;; (define (pairo x) (disj (== x '()) (fresh (y z) (== x (cons y z)))))
;;; (define (boolo x) (disj (== x #t) (== x #f)))



;;; simplify goal w.r.t. a domain variable, constant parameters acceptable
;;;   if satisfiable, then act as identity
;;;   otherwise return False
;;; simplify-wrt : state x goal x var -> goal
(define (simplify-wrt st goal var) 
  ;;; just run miniKanren!
  (define (first-non-empty-mature stream)
    (match (mature stream)
      [#f #f]
      [(cons #f next) (first-non-empty-mature next)]
      [v v]))
  (if (first-non-empty-mature (pause st goal)) (syntactical-simplify goal) (Bottom)))

;;; some trivial rewrite to make things easier
(define (syntactical-simplify goal)
  (define (basic-tactic prev-f rec goal)
    (define prev-result (prev-f goal))
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
  ((overloading-functor-list (list basic-tactic goal-base-endofunctor  identity-endo-functor)) goal)
)

;;; appearances of nested list
(define (member-nested v l)
  (match l ['() #f] 
    [(cons h t) 
      (or (match h [(? pair?) (member-nested v h)] [_ (equal? h v)]) (member-nested v t))]))


;;; (list true? false? null? pair? number? string? symbol?)

(define-syntax fresh_
  (syntax-rules ()
    ((_ (x ...) g0 gs ...)
     (let ((x (var/fresh 'x)) ...)  (conj* g0 gs ...)))))

(define-syntax fresh-var
  (syntax-rules ()
    ((_ x)
     (let ((x (var/fresh 'x)))  x))))


(define-syntax disj*
  (syntax-rules ()
    ((_)           fail)
    ((_ g)         g)
    ((_ g0 gs ...) (disj g0 (disj* gs ...)))))

(define-syntax conj*
  (syntax-rules ()
    ((_)                succeed)
    ((_ g)              g)
    ((_ gs ... g-final) (conj (conj* gs ...) g-final))))

(define type-label-to-type-goal
  (hash
    symbol? symbolo
    pair? (lambda (term) (fresh_ (y z) (== term (cons y z))))
    number? numbero
    string? stringo
  )
)


;;; getting the goals that is translating
;;;   the state 'st', also goals include the type constraints about v
;;;  var x state -> goal
(define/contract (extract-goal-about v st)
  (any? state? . -> . any?)
  (define (extract-from-each-subst pair)
      (match pair [(cons l r) (== l r)]))
  
  (define from-subst 
    (foldl conj (Top)
      (map extract-from-each-subst (state-sub st) )))
  
  ;;; stage each (list as) disjunction of inequalities into literal goals
  (define (stage-disj disj-list)
    (define (each-to-diseq p) (=/= (car p) (cdr p)))
    (foldl disj (Bottom) (map each-to-diseq disj-list)))

  ;;; stage each (list as) conjunction of disjunction of inequalities into literal goals
  (define (stage-conj-disj conj-disj-list)
    (foldl conj (Top) (map stage-disj conj-disj-list)))

  (define from-diseq
    ;;; make a conjunction of disjunction of inequalities
    ;;;   into literal goals
    (stage-conj-disj (state-diseq st)))

  (define from-typecsts
    ; just take out the typercd about v
    ;;; and translate to goals
    (let* ([tyr (state-typercd st)]
           [type-labels (hash-ref tyr v '())]
           [type-label-to-goal (lambda (label) ((hash-ref type-label-to-type-goal label (void)) v))]
           [type-csts (map type-label-to-goal type-labels)])
      (foldl conj (Top) type-csts)))
  
  (conj from-subst (conj from-diseq from-typecsts))
)

;;; replace one var with another
;;;  var x var x state -> state
;;;   but will only touch the type constraint 
;;;    s.t. after's type will be intersected with from's type constraint
;;;           if both after and from are variables
(define/contract (literal-replace from after st)
  (any? any? state? . -> . state?)
  (define (literal-replace-from-after prev-f rec obj)
    (match obj
      [x 
        #:when (equal? x from) 
        after]
      ;;; other extended construct -- like state
      ;;;  very untyped...
      [(state a scope trace direction d e) (state (rec a) scope trace direction (rec d) (rec e))]
      ;;; or type constraint information,
      ;;;  we only need to deal with type information

      ;;; TODO: there is some problem here
      ;;;   basically it is possible that from will be walked into another var
      ;;;    that has the correct type constraint information
      [(? hash?) 
        (let* ([at-key (hash-ref obj from #f)])
          (if at-key (hash-set (hash-remove obj from) after at-key) obj))
        ]
      [_ (prev-f obj)]))

  (define internal-f (overloading-functor-list (list literal-replace-from-after pair-base-endofunctor goal-base-endofunctor identity-endo-functor)))
  ;;; return the following
  (internal-f st))

;;;  a series of shrink into
;;; shrink-into :: set of var x state -> state
;;;  it will make state only about vars
;;;    !!! OVER/UNDER APPROXIMATION !!! can happen here
;;;   basically we don't really have to have [st] iff [shrink-into .. st]
;;;    [st] implies [shrink-into .. st] and 
;;;    [shrink-into .. st] implies [st] are both possibly ok! since we are doing *automated proving*
;;;      if we strengthen/weaken the condition, but somehow we still can deduce the goal, then we are fine!

(define (shrink-away var-from term-to st)
  (literal-replace var-from term-to st))

;;; [(term, term)] x state -> state
;;;  unifies each equation one by one
(define (unifies-equations list-u-v-s st)
  (foldl (lambda (eq st) (car (unify (car eq) (cdr eq) st))) st list-u-v-s)
)

(define (shrink-into vars st)
;;; 0. we first make sure there is no asymmetry on each inequalities
;;;   0.1 by going through all the inequalities, with cons on one side and var on the other,
;;;   0.2 we use "sketch" to construct the "frames" of the var (construct-conses)
;;;   0.3 we unifie these sketches with vars to remove the asymetry of the inequalitie  
;;; 1. we first use unmentioned-exposed-form 
;;;     to remove asymmetry form of equation, i.e. the unmentioned var in a composed structure
;;; 2. we go through the subst, one by one, if any side of equation has a var not in vars, we use shrink-away/literal to replace
;;;   At this point, we are finally doing shrink-into
;;; 3. removing those not-wanted var in diseqs by replacing them with True 
  (define diseqs (state-diseq st))

  (define (construct-conses x)
    (define rec construct-conses)
    (match x
      [(cons a b) (cons (rec a) (rec b))]
      [_ (fresh-var fpu)]
    )
  )

  ;;; use side-effect to record the encountered asymmetry equation
  (define each-asymmetry-record! '())

  (define (each-asymmetry prev-f rec g)
    (match g
      ;;; thiss pattern matching i a bit dangerous
      ;;; TODO: make equation/inequality into a struct so that pattern-matching can be easier
      [(cons (var _ _) (cons _ _)) 
          (let* ([v (car g)]
                 [composed (cdr g)])
              (set! each-asymmetry-record! 
                (cons (cons v (construct-conses composed)) each-asymmetry-record!))
              g
                 )]
      [(cons (cons _ _) (var _ _)) 
          (let* ([v (cdr g)]
                 [composed (car g)])
              (set! each-asymmetry-record! 
                (cons (cons v (construct-conses composed)) each-asymmetry-record!))
              g
                 )]
      [_ (prev-f g)]

    )
  )

  (define each-asymmetry-recorder
    (overloading-functor-list (list each-asymmetry pair-base-endofunctor identity-endo-functor))
  )
  (each-asymmetry-recorder diseqs)
  (define each-asymmetry-record each-asymmetry-record!)
  ;;; step 0.3 
  (define st-symmetric-on-diseqs (unifies-equations each-asymmetry-record st))
  ;;; now the diseqs have same AST height on each side
  (define subst-st-symmetric-on-diseqs (state-sub st))
  (define remove-asym-on-subst (unmentioned-exposed-form vars subst-st-symmetric-on-diseqs))
  (define st-symmetry-everywhere (state-subst-set st-symmetric-on-diseqs remove-asym-on-subst))
  ;;; step 2: now go through each equation in subst, doing real shrinking
  (define (eliminate-unmentioned-var-in-subst st)
    (define current-subst (state-subst st))
    
    (if (equal? current-subst '())
      st
      (let*
        ([fst-eq (car current-subst)]
         [next-st (state-sub-update st cdr)])
        (match fst-eq
          [(cons (var a b) rhs)
            #:when (not (member (var a b) vars))
            (eliminate-unmentioned-var-in-subst (shrink-away (var a b) rhs next-st))]
          ;;; lhs must be a var that is also mentioned, 
          ;;;   then by post-condition of "unmentioned-exposed-form",
          ;;;   we know the rhs must all be mentioned
          ;;; TODO: so actually the following clause can be ignored 
          [(cons lhs (var a b))
            #:when (not (member (var a b) vars))
            (eliminate-unmentioned-var-in-subst (shrink-away (var a b) lhs next-st))]
          [_
            (state-subst-update 
              (lambda (x) (cons fst-eq x))
              (eliminate-unmentioned-var-in-subst next-st))
          ]
      ))
    )
  )

  (define st-removed-unmentioned-in-subst (eliminate-unmentioned-var-in-subst st-symmetry-everywhere))

  ;;; precondition: each inequalties only have var on both sides
  (define (eliminate-unmentioned-var-in-diseq diseq)
    (define (not-list x)
      (not (or (equal? x '()) (pair? x))))
    (define (each-inequality prev-f rec g)
      (match g
        ;;; this pattern matching is a bit dangerous
        ;;; TODO: make equation/inequality into a struct so that pattern-matching can be easier
        [(cons (var _ _) (var _ _))
          #:when (there-is-var-not-in vars g) 
          (Top)]
        [_ (prev-f g)]
      )
    )

    (define deal-with-inequalities
      (overloading-functor-list (list each-inequality pair-base-endofunctor identity-endo-functor))
    )
    (deal-with-inequalities diseq)
  )

  (state-diseq-update deal-with-inequalities st-removed-unmentioned-in-subst)

)

;;; tproj :: var x List of ['car, 'cdr] 
;;; cxr as a path/stack of field projection/query
(struct tproj (v cxr) #:prefab)
;;; (struct tcar (term) #:prefab)
;;; (struct tcdr (term) #:prefab)

(define (tcar t) 
  (match t 
    [(cons a b) a]
    [(tproj x y) (tproj x (cons 'car y))]
    [(var _ _) (tproj t (list 'car))]
    [_ (raise "Unexpected Value")]
  ))

(define (tcdr t) 
  (match t 
    [(cons a b) b]
    [(tproj x y) (tproj x (cons 'cdr y))]
    [(var _ _) (tproj t (list 'cdr))]
    [_ (raise "Unexpected Value")]
  ))

;;; normalize a tproj term so that tproj-v is always a var 
(define (tproj_ term cxr)
  
  ;;; (define (m x) (match x ['car tcar] ['cdr tcdr]))
  ;;; (define (compose f g) (lambda (x) (f (g x))))
  ;;; (define mcxr (map m cxr))
  ;;; (define )
  (match cxr
    [(cons 'car rest) (tcar (tproj_ term rest))]
    [(cons 'cdr rest) (tcdr (tproj_ term rest))]
    ['() term] 
  )
)

;;; given a tproj, we construct a tproj-ectable term for it
;;;  return the equation for removing the tproj
;;; tproj -> pair as var, cons/tree of vars
(define (equation-for-remove-tproj x)
  ;;; (define field-projection-list (tproj-cxr x))
  (define (construct-sketch path)
    (match path
      [(cons 'car rest)  (cons (construct-sketch rest) (fresh-var fpu))]
      [(cons 'cdr rest)  (cons (fresh-var fpu) (construct-sketch rest))]
      ['() (fresh-var fpu)]
    )
  )
  (cons (tproj-v x) (construct-sketch (tproj-cxr x)))
)

;;; given st x goal -> st x goal
;;;  with tproj all removed
(define (eliminate-tproj st goal)
  ;;; 0. we first collect all occurrence of tproj, collect into a set
  ;;; 1. we use equation-for-remove-tproj to remove each tproj, 
  ;;;     and remember what variable each tproj will be mapped to
  ;;; 2. we then do literal replace to remove tproj occurrences
  ;;; 3. we use unify-equations to make sure the equations are satisfied

  (define (collect-tproj)
    (define record! (mutable-set))
    (define (when-tproj prev-f rec g)
      (match g
        [(tproj _ _) (begin (set-add! record! g) g)]
        [_ (prev-f g)]
      )
    )

    (define record-tproj-on-pair-and-goals 
      (overloading-functor-list (list collect-tproj goal-base-endofunctor pair-base-endofunctor identity-endo-functor)))
    (record-tproj-on-pair-and-goals (list (state-subst st) (state-diseq st) goal) )
    (set->list record!)
  )
  ;;; the collected tprojs
  (define all-tprojs (collect-tproj))
  ;;;  the corresponding equation for each tproj
  (define removing-equations (map equation-for-remove-tproj all-tprojs))
  ;;; for each equation ((var y) (cons ...)), originated from  (tproj y ...)
  ;;;   we record ((tproj y ...), (var ...))
  ;;; (define tproj-map-to (map 
  ;;;                         (lambda (tproj equ) (cons tproj (tproj_ (car equ) (cdr equ))))
  ;;;                          all-tprojs removing-equations))
  (define tproj-mapped-to 
    (map (lambda (tproj-info equ) (tproj_ (cdr equ) (tproj-cxr tproj-info))) 
          all-tprojs removing-equations))
  ;;; we have for each (tproj y ..) a var v standing for it in the context of removing equations
  ;;; (define tproj-hash-map (make-hash tproj-map-to))

  (define tproj-replaced-st
    (foldl (lambda (ttproj v st) (literal-replace ttproj v st)) st all-tprojs tproj-mapped-to))

  (define tproj-replaced-goal
    (foldl (lambda (ttproj v g) (literal-replace ttproj v g)) goal all-tprojs tproj-mapped-to))
  
  (define tproj-removed-st
    (unifies-equations removing-equations tproj-replaced-st)
  )

  `(,tproj-removed-st . ,tproj-replaced-goal)
  
)

;;; make sure there is no cons on each side of equation
;;;  by transforming each equations to two sub equations
;;; List of pair of terms -> List of pair of terms
(define (eliminate-cons subs)
  (define (tcar-eq eq) 
    (define res (map tcar eq))
    (match res [(cons _ (var _)) (cons (cdr res) (car res))] [_ res])
  )
  (define (tcdr-eq eq) 
    (define res (map tcdr eq))
    (match res [(cons _ (var _)) (cons (cdr res) (car res))] [_ res])
  )
  (define (each-eliminate-cons single-eq) (list (tcar-eq single-eq) (tcdr-eq single-eq)))
  (match subs
    [(cons head-eq rest) 
      (match head-eq 
        [(cons (cons _ _) rhs) 
          #:when (not (pair? rhs))
            (append (each-eliminate-cons head-eq) rest)]
        [(cons lhs (cons _ _))
          #:when (not (pair? lhs)) 
            (append (each-eliminate-cons head-eq) rest)]
        [_ (cons head-eq (eliminate-cons rest))]
        )
    ]
    ['() '()]
  )
)


(define (tcar-eq eq) 
  (define res (map tcar eq))
  (match res 
    [(cons (var _ _) _) res]
    [(cons _ (var _ _)) (cons (cdr res) (car res))] 
    [_ res])
)
(define (tcdr-eq eq) 
  (define res (map tcdr eq))
  (match res 
    [(cons (var _ _) _) res]
    [(cons _ (var _ _)) (cons (cdr res) (car res))] 
    [_ res])
)

;;; given a set of equation (lhs must be var)
;;;  return an equivalent set of equation (lhs must be var)
;;;  s.t. the returned set won't have a equation like below
;;; (mentioned-var = (cons ... unmentioned-var ...))
;;; i.e. if one-side is mentioned var, then the other-side must be all mentioned
(define (unmentioned-exposed-form mentioned-vars eqs)
  (define (each-eliminate-cons single-eq) (list (tcar-eq single-eq) (tcdr-eq single-eq)))
  ;;; given one eq
  ;;;  return a list of eqs equivalent
  ;;;  and make sure in unmentioned-exposed-form 
  (define (single-unmentioned-exposed-form eq)
    (define fst (car eq))
    (define snd (cde eq))
    (define is-unexposed-form
      (and (member fst mentioned-vars)
           (there-is-var-not-in mentioned-vars snd)))
    (define cons-at-right
      (pair? snd))
    (define is-simple-form
      (and (var? fst) (var? snd)))
    (if is-unexposed-form
      ;;; the following is quite twisted... 
      ;;; basically there are too many preconditions 
      (if simple-form 
        (list (cons snd fst))
        (if cons-at-right 
          (eliminate-conses (each-eliminate-cons eq)) 
          (raise "Unexpected Equation Form")))
      (list eq)
    )
  )
)

;;; given a set of equations (lhs doesn't have to be variable)
;;;  return an equivalent set of equations (lhs must be variable)
(define (eliminate-conses eqs)
  (define (each-eli-eq single-eq)
    ;;; won't stop if either side has cons
    (match single-eq
      [(cons (tproj _ _) (tproj _ _)) 
        (raise "Cannot Eliminate Conses if there is no conses")]
      [(cons (cons _ _) _) (eliminate-conses (list (tcar-eq single-eq) (tcdr-eq single-eq)))]
      [(cons _ (cons _ _)) (eliminate-conses (list (tcar-eq single-eq) (tcdr-eq single-eq)))]
      [_ (list single-eq)] ;; 
    )
  )

  (define (lhs-must-var eq)
    (match eq
      [(cons (var _ _) _) eq]
      [(cons _ (var _ _)) (cons (car eq) (cdr eq))]
      [_ (raise "Not A proper substution-form Equation!")]
    )
  )
  (map lhs-must-var 
    (foldl append '() 
      (map each-eli-eq eqs)))
)

;;; clear everything about v on st
;;;  var x state -> state
;;;   done easily by replace v with a brand new var everywhere in the st
(define/contract (clear-about v st)
  (any?  ?state? . -> . ?state?)
  ;;; (display st)
  (let* ([vname (symbol->string (var-name v))]
         [new-v (var/fresh (string->symbol (string-append vname "D")))]
         [replaced (literal-replace v new-v st)]
         )
    replaced )
)

;;; will declare variable, and assert goal on all its domain
(define-syntax for-all
  (syntax-rules ()
    ((_ (x ...) g0 gs ...)
     (let ((x (var/fresh 'x)) ...) (given (x ...) (conj* g0 gs ...)) ))))

;;; given (a series of) variable(s) we will assert the goal on all its possible
;;;  domain
;;;   using the original variables
(define-syntax given
  (syntax-rules ()
    ((_ () g) g)
    ((_ (x xs ...) g)
      (forall x (Top) (given (xs ...) g)))))

