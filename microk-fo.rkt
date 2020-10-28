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
  step
  mature
  mature?
  walk*/goal)

(require "common.rkt")

;; first-order microKanren
;;; goals
(struct disj   (g1 g2) 
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ∨ ~a" (disj-g1 val) (disj-g2 val)))]
)

(struct conj   (g1 g2)  
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ∧ ~a" (conj-g1 val) (conj-g2 val)))]
)
(struct relate (thunk description)      ;;;#:prefab
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a" (relate-description val)))]
)
(struct ==     (t1 t2)               
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a =ᴸ ~a" (==-t1 val) (==-t2 val)))]
     ;;; L stands for Lisp Elements
)
(struct ex     (varname g) 
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
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ≠ᴸ ~a" (=/=-t1 val) (=/=-t2 val)))]
)

(struct forall (varname domain g)
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∀~a. ~a" (ex-varname val) (ex-g val)))]
)

(struct symbolo (t)
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "symbol ~a" (symbolo-t val)))]
)

(struct not-symbolo (t)
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-symbol ~a" (not-symbolo-t val)))]
)


(struct numbero (t)
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "number ~a" (numbero-t val)))]
)

(struct not-numbero (t)
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-number ~a" (not-numbero-t val)))]
)


(struct stringo (t)
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "string ~a" (stringo-t val)))]
)

(struct not-stringo (t)
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
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "⊤" (not-stringo-t val)))]
)


(struct Bottom ()
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "⊥" (not-stringo-t val)))]
)


;;; Denote Goal-EndoFunctor type as
;;;      (goal -> goal) -> (goal -> goal) -> goal -> goal
;;; extensible function on pattern matching
;;;  pretentious "endofunctor" just means it maps goal to goal
;;; goal-base-endofunctor : (goal -> goal) -> (goal -> goal) -> goal -> goal
;;;  prev-f will call the one on the past overloading functor
;;;   extended-f will use the whole composed functor
;;;  this functor will do nothing but recurse on the tree
(define (goal-base-endofunctor prev-f extended-f g)
  (define rec extended-f)
  (match g
    [(disj a b) (disj (rec a) (rec b))]
    [(conj a b) (conj (rec a) (rec b))]
    [(ex v g) (ex v (rec g))]
    [(forall v b g) (ex v (rec v) (rec g))]
    [_ g] ;; otherwise do nothing
  )
)

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
      ['() goal-identity]
    )
  )
  (define (resultf g)
    (overloading-functor-list-with-extf endofuncs resultf))
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
(struct bind   (bind-s bind-g)          #:prefab)
(struct mplus  (mplus-s1 mplus-s2)      #:prefab)
(struct pause  (pause-state pause-goal) #:prefab)


;;; the special stream only used for forall
;;;   all the possibe results of first-attempt-s
;;;   will be complemented and intersect with the domain of the bind-g
;;;   bind-g will have to be a forall goal
(struct bind-forall   (first-attempt-s dv bind-g)          #:prefab)


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


(define (start st g)
  (match g
    ((disj g1 g2)
     (step (mplus (pause (trace-left st) g1)
                  (pause (trace-right st) g2))))
    ((conj g1 g2)
     (step (bind (pause st g1) g2)))
    ((relate thunk _)
     (pause st (thunk)))
    ((== t1 t2) (unify t1 t2 st))
    ((=/= t1 t2) (neg-unify t1 t2 st))
    ((symbolo t1)  (check-as symbol? t1 st))
    ((not-symbolo t1) (check-as-disj (remove symbol? type-label-top) t1 st)) 
    ((numbero t1) (check-as number? t1 st))
    ((not-numbero t1)  (check-as-disj (remove number? type-label-top) t1 st)) 
    ((stringo t1) (check-as string? t1 st))
    ((not-stringo t1)  (check-as-disj (remove string? type-label-top) t1 st))
    ((ex _ gn) (start st gn))
    ;;; forall is tricky, 
    ;;;   we first use simplification to
    ;;;   we first need to consider forall as just another fresh
    ;;;   and "bind" the complement of result to the nexttime forall as domain
    ;;;   
    ;;; 
    ((forall var domain goal) 
      (let* [(domain_ (simplify-wrt st domain var))] 
        (if (equal? domain_ Bottom) 
          (wrap-state-stream st)
          (bind-forall (start st (ex var (conj domain_ goal))) var (forall var domain goal))
        )
      )
    )
    ))

(define (step s)
  (match s
    ((mplus s1 s2)
     (let ((s1 (if (mature? s1) s1 (step s1))))
       (cond ((not s1) s2)
             ((pair? s1)
              (cons (car s1)
                    (mplus s2 (cdr s1))))
             (else (mplus s2 s1)))))
    ((bind s g)
     (let ((s (if (mature? s) s (step s))))
       (cond ((not s) #f)
             ((pair? s)
              (step (mplus (pause (car s) g)
                           (bind (cdr s) g))))
             (else (bind s g)))))
    ;;; bind-forall is a bit complicated
    ;;;   it will first need to collect all possible solution of
    ;;;   s, and complement it, and intersect with 
    ((bind-forall s v (forall v domain goal))
     (let ((s (if (mature? s) s (step s))))
       (cond 
        ;;; unsatisfiable, then the whole is unsatisfiable
        ((not s) #f)
        ;;; possible to satisfy! we complement this current requirement/condition
        ;;;  to initiate the search for the remaining domain
        ;;;  and the same time, other possible 

        ;;;   to initiate the search for remaining domain is hard: 
        ;;;   1. we use the result for the previous search, and complement only on v 
        ;;;       (because all other vars should be fixed)
        ;;;     1.a but to complement on v, it is hard because state has conjunction of disjunction of inequality
        ;;;     1.b so we make state "pair s" into "pair s_" s
        ;;;           .t. (car s_) has only conjunction of inequality about v or just unchanged (if no inequality about v)
        ;;;           "split-diseqs-of-state"
        ;;;         and also make sure other parts of the inequality list is not relevent to x
        ;;;     1.c then we can take complement -- 
        ;;;         by first extract info about v from (car s_) into goals "to-complement"
        ;;;         and then remove info about v from (car s_) into 
        ;;;   2. after complement, we just conjunction the domain with original forall's domain and (pause st g)
        ((pair? s)
            (let* ([first-st (car s)]
                   [split-states (split-diseqs-of-state v first-st)] 
                  ;;;  now we have a list of state; 
                  ;;;  and for each state we will get 
                  ;;;  1. the cleared states about v 2. the corresponding complemented goal 
                   [extract-complement-goal (lambda (st) (complement (extract-goal-about v st)))]
                   [clear-state-on-v (lambda (st) (clear-about v st))]
                  ;;;  now construct a bunch of stream according to those
                   [new-conj-domains (map extract-complement-goal split-states)]
                   [new-states (map clear-state-on-v split-states)]
                   [streams (map (lambda (complemented-goal state) 
                                  (pause state (forall v (conj complemented-goal domain) goal))) 
                                    new-conj-domains new-states)]
                   [converged-streams (foldl mplus #f streams)]
                    )
              ;;; forall x (== x 3) (== x 3)
              ;;;   forall x (conj (== x 3) (=/= x 3)) (== x 3)
              ;;;  forall x () (symbolo x) /\ (not-symbolo x)
              (step (mplus converged-streams
                           (bind-forall (cdr s) v (forall v domain goal)))))) ;;; other possible requirements search

        (else (bind-forall s v (forall v domain goal))))

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
  (void)
)

;;; appearances of nested list
(define (member-nested v l)
  (match l ['() #f] 
    [(cons h t) 
      (or (match h [(? pair?) (member-nested v h)] [_ (equal? h v)]) (member-nested v t))]))

;;; variable x state -> List[state]
;;;   we will make a given state into a stream of states
;;;    that has equivalent semantic
;;;    but also, each conj component in the state will either only about v
;;;       or not about v at all 
;;;    (i.e. each disjunct is about v or none of disjunct is about v) 
(define (split-diseqs-of-state v st) 
  (define inequalities (state-diseq st))
  ;;; 1. first sort the conjunction of disjunction
  ;;; state -> state, that will make conjunction component with appearances of v appear ahead



  ;;; transform to conjunction of pair of disjunction
  ;;; i.e. list of pair of list

  ;;;  given a disjuncts, we return a list of disjuncts, where the first element
  ;;;     is all about v while the second is not
  ;;;  disjunct = list of inequalities
  ;;; disjunct -> pair of disjunct
  ;;; 
  (define (split-disj disj)
    (cons
      (filter (lambda (x) (member-nested v x)) disj)
      (filter (lambda (x) (not (member-nested v x))) disj)
    )
  )

  ;;; given a list of disjunct [A, B, C], return a list of list of disjunct
  ;;;   as [[split-disj A . 0, split-disj B . 0, split-disj C . 0],
  ;;;       [split-disj A . 1, split-disj B . 0, split-disj C . 0] ...]
  ;;; list of disjunction -> list of list of disjunction
  ;;; conjunction of disjunction -> disjunction of conjunction of disjunction
  (define (split-disjs disjs)
    (match disjs
      ['() (list (list))]
      [(cons h t) 
        (match-let* 
         ([later (split-disjs t)] ;;; list of list of disjunct
          [(cons has-v no-v) (split-disj h)] ;;; pair of disj
          ;;;  has-v : disjunct
          ;;; if any of the has-v/no-v is actually empty, then
          ;;;   (basically disjunct of empty is False)
          ;;;   we will have to ignore 
          [empty '()]
          [add-has-v (if (null? has-v) 
                          empty 
                          (append empty (map (lambda (x) (cons has-v x)) later) ))]
          [add-no-v (if (null? no-v)
                        add-has-v
                        (append empty (map (lambda (x) (cons no-v x)) later) ) )])
          add-no-v     
        )
      ]
    )
  )

  (define each-conjunction (split-disjs inequalities))
  (define all-state (map (lambda (conj) (state-diseq-set st conj)) each-conjunction))
  
  ;;; return the list of states
  all-state

  ;;; now compute the set of conjunctions of disjunctions
  
)

;;; (list true? false? null? pair? number? string? symbol?)

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 gs ...)
     (let ((x (var/fresh 'x)) ...) (ex-s (x ...) (conj* g0 gs ...))))))

(define type-label-to-type-goal
  (hash
    symbol? symbolo
    pair? (lambda (term) (fresh (y z) (== term (cons y z))))
    number? numbero
    string? stringo
  )
)


;;; getting the goals that is directly translating
;;;   the state 'st', the goals are all about v
;;;  var x state -> goal
;;;   precondition: 
;;;   state has each disjunction in diseq only about v or not at all about v
(define (extract-goal-about v st)
  (define (extract-from-each-subst pair)
      (match pair [(cons l r) (== l r)]))
  
  (define from-subst 
    (foldl conj Top
      (map extract-from-each-subst 
        (filter (lambda (x) (member-nested v x)) (state-sub st)))))
  
  ;;; stage each (list as) disjunction of inequalities into literal goals
  (define (stage-disj disj-list)
    (define (each-to-diseq p) (=/= (car p) (cdr p)))
    (foldl disj Bottom (map each-to-diseq disj-list)))

  ;;; stage each (list as) conjunction of disjunction of inequalities into literal goals
  (define (stage-conj-disj conj-disj-list)
    (foldl conj Top (map stage-disj conj-disj-list)))

  (define from-diseq
    ;;; make a conjunction of disjunction of inequalities
    ;;;   into literal goals
    (stage-conj-disj (filter (lambda (l) (member-nested v l)) (state-diseq st)) )
  )

  (define from-typecsts
    ; just take out the typercd about v
    ;;; and translate to goals
    (let* ([tyr (state-typercd st)]
           [type-labels (hash-ref tyr v '())]
           [type-label-to-goal (lambda (label) ((hash-ref type-label-to-type-goal label (void)) v))]
           [type-csts (map type-label-to-goal type-labels)])
      (foldl conj Top type-csts)))
  
  (conj from-subst (conj from-diseq from-typecsts))
)

;;; homomorphism on pair, will respect pair construct
(define (pair-base-endofunctor prev-f extended-f g)
  (define rec extended-f)
  (match g
    ['() '()]
    [(cons a b) (cons (rec a) (rec b))]
    [_ g]
  )
)


;;; clear everything about v on st
;;;  var x state -> state
;;;   done easily by replace v with a brand new var everywhere in the st
(define (clear-about v st)
  (define (literal-replace from after obj)
    (define (literal-replace-from-after prev-f ext-f obj)
      (define rec extended-f)
      (match obj
        [(? (lambda (x) (equal? x from))) after]
        ;;; other extended construct -- like state
        ;;;  very untyped...
        [(state a b c d e) (state (rec a) (rec b) (rec c) (rec d) (rec e))]
        ;;; or type constraint information,
        ;;;  we only need to deal with type information
        [(? hash?) 
          (let* ([at-key (hash-ref obj from #f)])
            (if at-key (hash-set (hash-remove obj from) after at-key) obj))
          ]
        [_ (prev-f obj)]))
  
    ((overloading-functor-list (list literal-replace-from-after pair-base-endofunctor)) obj))

  (let* ([vname (symbol->string (var-name v))]
         [new-v (var/fresh (string->symbol (string-append vname "-dummy")))])
    (literal-replace v new-v st))
)