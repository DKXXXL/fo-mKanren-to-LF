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

  there-is-var-in
  there-is-var-not-in
  freevar
  

  syntactical-simplify
  complement
  ;;; replace-1-to-0
  )

(require "common.rkt")
(require errortrace)

(instrumenting-enabled #t)


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

;;; typeinfo is a set of type-symbol
;;; indicating t is union of these type
;;;   this goal is usually not interfaced to the user

(struct type-constraint (t typeinfo)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "type-constraint ~a ~a" (type-constraint-t val) (type-constraint-typeinfo val)))]
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

(define succeed (Top))
(define fail    (Bottom))
(define-syntax conj*
  (syntax-rules ()
    ((_)                succeed)
    ((_ g)              g)
    ((_ gs ... g-final) (conj (conj* gs ...) g-final))))
(define-syntax disj*
  (syntax-rules ()
    ((_)           fail)
    ((_ g)         g)
    ((_ g0 gs ...) (disj g0 (disj* gs ...)))))


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

(define (goal-term-base-endofunctor prev-f rec g)
  ;;; (define rec extended-f)
  (match g
    [(== x y) (== (rec x) (rec y))]
    [(=/= x y) (=/= (rec x) (rec y))]
    [(symbolo x) (symbolo (rec x))]
    [(not-symbolo x) (not-symbolo (rec x))]
    [(numbero x) (numbero (rec x))]
    [(not-numbero x) (not-numbero (rec x))]
    [(stringo x) (stringo (rec x))]
    [(not-stringo x) (not-stringo (rec x))]
    [(type-constraint x types) (type-constraint (rec x) types)]
    [(disj a b) (disj (rec a) (rec b))]
    [(conj a b) (conj (rec a) (rec b))]
    [(ex v g) (ex v (rec g))]
    [(forall v b g) (forall v (rec v) (rec g))]
    [_ (prev-f g)] ;; otherwise do nothing
  )
)

(define (state-base-endo-functor prev-f rec g)
  (match g
    [(state a scope trace direction d e)
      (state (rec a) scope trace direction (rec d) (rec e))]
    [_ (prev-f g)]
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
  

(define/contract (there-is-var-in vars pair-goal)
  (set? any? . -> . boolean?)
  (define all-fvs (freevar pair-goal))
  (not (set-empty? (set-intersect vars all-fvs)))
)

;;; (define/contract (there-is things pair-goal)
;;;   (set? any? . -> . boolean?)
;;;   (define (each-case prev-f rec g)
;;;     (if (set-member? things g) #t (prev-f g))
;;;   )

;;;   (define result-f 
;;;     (overloading-functor-list (list each-case goal-base-endofunctor (there-is-in-pair-base-functor #f)))
;;;   )
;;;   (result-f pair-goal)
;;; )

(define/contract (there-is-var-not-in vars pair-goal)
  (set? any? . -> . boolean?)
  (define all-fvs (freevar pair-goal))
  (set-subtract! all-fvs vars)
  (not (set-empty? all-fvs))
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
  (define (counter prev-f ext-f g)
    (match g
      [(var _ _) (begin (set-add! fvs g) g)]
      [o/w (prev-f g)]
    )
  )
  
  (define result-f 
    (overloading-functor-list (list counter goal-term-base-endofunctor pair-base-endofunctor state-base-endo-functor identity-endo-functor))
  )

  (result-f g)
  fvs
)

;;; streams
(struct bind   (scope bind-s bind-g)          #:prefab)
(struct mplus  (mplus-s1 mplus-s2)      #:prefab)
(struct pause  (pause-state pause-goal) #:prefab)
(struct mapped-stream (f stream) #:prefab)
;;; f :: state -> stream of states
;;; mapped-stream f (cons a s) = mplus (f a) (mapped-stream f s)
(struct to-dnf (state mark) #:prefab)
;;; semantically there is or in the "state"
;;;   this will lift the "or"s into stream
;;;   at the current stage, mark is used for pointing to
;;;     the disj component

;;; since a state has semantic of disjunction
;;;  we transform it into DNF and we should be able to index each disjunct component
;;; 
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
(define (index-incremenent-by-one l range)
  (match (cons l range)
    [(cons '() '()) #f]
    [(cons (cons a s) (cons r t))
      (if (< (+ 1 a) r)
        (cons (+ 1 a) s)
        (let* ([up-level (index-incremenent-by-one s t)])
          (and up-level
            (cons 0 up-level))))]
  )
)


(define (get-state-DNF-next-index st index)
  (define range (get-state-DNF-range st))
  (index-incremenent-by-one index range))


(define (get-state-DNF-by-index st index)
  (define conjs (state-diseq st))
  (define indexed-conjs (map (lambda (disjs pos) (list (list-ref disjs pos))) conjs index))
  (state-diseq-set st indexed-conjs)
)

;;; the special stream only used for forall
;;;   all the possibe results of first-attempt-s
;;;   will be complemented and intersect with the domain of the bind-g
;;;   bind-g will have to be a forall goal
(struct bind-forall   (scope first-attempt-s dv bind-g)          #:prefab)


(define (mature? s) 
    (or (not s) (pair? s)))

(define (not-state? x) (not (state? x)))

(define/contract (mature s)
    (not-state? . -> . any?)
    (debug-dump "\n maturing: ~a" s)
    (if (mature? s) s (mature (step s))))
  
(define (total-mature s)
  (match s
    [(cons a b) (cons a (total-mature b))]
    [#f #f]
  )
)

;;; given a stream of states, 
;;;   return another stream of states 
;;;   make sure there is no disjunction in meaning of each state and 
;;;     all the disjunction are lifted to mplus
(define (TO-DNF stream)
  ;;; (debug-dump "TO-DNF computing \n")
  (mapped-stream (lambda (st) (to-dnf st (get-state-DNF-initial-index st))) stream))

(define (TO-NON-Asymmetric stream)
  ;;; (debug-dump "TO-NON-Asymmetric computing \n")
  (mapped-stream remove-assymetry-in-diseq stream)
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
     (step (mplus (pause st g1)
                  (pause st g2))))
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

    ((type-constraint t types)
      (wrap-state-stream (check-as-inf-type-disj types t st)))
    ((ex v gn) 
      ;;; TODO: make scope a ordered set (or just a list)
      (start (state-scope-update st (lambda (scope) (set-add scope v))) gn))
    ;;; forall is tricky, 
    ;;;   we first use simplification to
    ;;;   we first need to consider forall as just another fresh
    ;;;   and "bind" the complement of result to the nexttime forall as domain
    ;;;   
    ;;; 
    ((forall var domain goal) 
      (let* [(domain_ (simplify-wrt st domain var))
             (k (begin (debug-dump "\n ~a : domain_ : ~a " var domain_)))
            ] 

        (match domain_
          ;;; BUGFIX: shrink-into about st
          [(Bottom) (clear-about st (list->set (state-scope st)) var)]
          ;;; [(Bottom) (wrap-state-stream st)] 
          [_ (bind-forall (state-scope st) 
                          (TO-DNF (TO-NON-Asymmetric (pause st (ex var (conj domain_ goal)))))  
                          var 
                          (forall var domain_ goal))]
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
    ((to-dnf st mark)
      ;;; mark is the index
      (and mark
          (let ([ret (get-state-DNF-by-index st mark)]
                [next-mark (get-state-DNF-next-index st mark)])
            (cons ret (to-dnf st next-mark)))))

    ((mapped-stream f stream)
      ;;; TODO: recheck this part .. it might be not correct searching strategy
      (let ((s (if (mature? stream) stream (step stream))))
        (cond ((not s) #f)
              ((pair? s)
                (step (mplus (f (car s))
                             (mapped-stream f (cdr s)))))
              (else (mapped-stream f s)))))
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
                   [current-vars (list->set current-vars)]
                   [w/o-v (set-remove current-vars v)]
                  ;;;  TODO: figure out trace!
                   [mentioned-var (set-add current-vars v)]

                   ;; (x = (cons x y) ) (cons a x) = (cons a y) -> x = y
                  ;;;  (x = (cons a y)) => (a = x.car, y = x.cdr  )
                   [unmentioned-exposed-st (unmentioned-exposed-form mentioned-var st)]
                   
                   [unmention-substed-st (unmentioned-substed-form mentioned-var unmentioned-exposed-st)]
                   
                   [domain-enforced-st (domain-enforcement-st unmention-substed-st)]
                   
                   [relative-complemented-goal (relative-complement domain-enforced-st current-vars v)]
                   [shrinked-st (shrink-away domain-enforced-st current-vars v)]
                   [k (begin  (debug-dump "\n st: ~a" st)
                              ;;; (debug-dump "\n unmention-exposed-st: ")(debug-dump unmentioned-exposed-st)
                              (debug-dump "\n unmention-substed-st: ~a" unmention-substed-st)
                              (debug-dump "\n shrinked-st: ~a" shrinked-st) 
                              (debug-dump "\n relative-complemented-goal: ~a" relative-complemented-goal)
                              ;;; (debug-dump "\n complemented goal: ")(debug-dump st-scoped-w/ov)
                              ;;; (debug-dump "\n next state ") (debug-dump next-st) 
                              ;;; (debug-dump "\n search with domain on var ")
                              ;;; (debug-dump v) (debug-dump " in ") (debug-dump cgoal) 
                              (debug-dump "\n"))
                              ]
                    )
              ;;; forall x (== x 3) (== x 3)
              ;;;   forall x (conj (== x 3) (=/= x 3)) (== x 3)
              ;;;  forall x () (symbolo x) /\ (not-symbolo x)
              (step (mplus (pause shrinked-st (forall v (conj relative-complemented-goal domain) goal))
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
;;; doesn't support user-customized goal, and universal-quantification
(define (complement g)
  ;;; (goal? . -> . goal?)
  (let ([c complement])
    (match g
      [(disj g1 g2) (conj (c g1) (c g2))]
      [(conj g1 g2) (disj (c g1) (c g2))]
      [(relate _ _) 
        (raise-and-warn "User-Relation not supported.")]
      [(== t1 t2) (=/= t1 t2)]
      [(=/= t1 t2) (== t1 t2)]
      [(ex a gn) (forall a (c gn))]
      [(forall v bound gn) 
        (raise-and-warn "Not supported complement on higher-ranked.") ]
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
(define/contract (member-nested v l)
  (any? list? . -> . list?)
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




(define type-label-to-type-goal
  (hash
    symbol? symbolo
    pair? (lambda (term) (fresh_ (y z) (== term (cons y z))))
    number? numbero
    string? stringo
  )
)



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

  (define (literal-replace-from-after prev-f rec obj)
    (match obj
      [x 
        #:when (hash-ref mapping x #f) 
        (hash-ref mapping x #f)]
      ;;; other extended construct -- like state
      ;;;  very untyped...
      ;;;  (a = a) (type-constrant a (number?))
      [(state a scope trace direction d e) 
        (let* ([new-sub-possible-with-cycle (rec a)] 
               [new-sub (filter (lambda (x) (not (equal? (car x) (cdr x)))) new-sub-possible-with-cycle)]
                ;;; TODO: we will only remove (a = a) and 
                ;;;   forget about possible cycle cases like (a = b, b = a)
               [old-hash-list (hash->list mapping)]
               [new-hash-list 
                (map (lambda (x) (cons (car x) (walk* (cdr x) new-sub))) old-hash-list)]
               [new-mapping (make-hash new-hash-list)]
               [rec (lambda (any) (literal-replace* new-mapping any)) ])
          (state new-sub scope trace direction (rec d) (rec e)))]
      ;;; or type constraint information,
      ;;;  we only need to deal with type information


      [(? hash?) 
        ;;; type-constraint!
        (let* ([type-infos (hash->list obj)]
               [new-type-infos (rec type-infos)])
          (foldl hash-table-add (hash) new-type-infos) ) ]
      [_ (prev-f obj)]))

  (define internal-f (overloading-functor-list (list literal-replace-from-after pair-base-endofunctor goal-term-base-endofunctor identity-endo-functor)))
  ;;; return the following
  (internal-f st)
)

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

;;;  a series of shrink into
;;; shrink-into :: set of var x state -> state
;;;  it will make state only about vars
;;;    !!! OVER/UNDER APPROXIMATION !!! can happen here
;;;   basically we don't really have to have [st] iff [shrink-into .. st]
;;;    [st] implies [shrink-into .. st] and 
;;;    [shrink-into .. st] implies [st] are both possibly ok! since we are doing *automated proving*
;;;      if we strengthen/weaken the condition, but somehow we still can deduce the goal, then we are fine!

;;; (define (shrink-away var-from term-to st)
;;;   (literal-replace var-from term-to st))

;;; [(term, term)] x state -> state
;;;  unifies each equation one by one
(define (unifies-equations list-u-v-s st)
  (foldl (lambda (eq st) (car (unify (car eq) (cdr eq) st))) st list-u-v-s)
)

;;; return a set of vars, indicating that those vars, "s" are in the
;;;  form of "s =/= (cons ...)", and thus we need to break down s themselves
(define (record-vars-on-asymmetry-in-diseq st)
  (define each-asymmetry-record! (mutable-set))
  (define (each-asymmetry prev-f rec g)
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
      [_ (prev-f g)]

    )
  )

  (define each-asymmetry-recorder
    (overloading-functor-list (list each-asymmetry pair-base-endofunctor identity-endo-functor))
  )
  (each-asymmetry-recorder (state-diseq st))
  (set->list each-asymmetry-record!)
)

;;; var -> goal
;;;   a bunch of goal asserts v is of finite type
(define (is-of-finite-type v)
  (disj* (== v #t) (== v #f) (== v '()))
)
;;; given the st, we will break down a bunch of v's domain by the domain axiom
;;;  return an equivalent stream of states s.t. v is pair in one state and not pair in the others
(define (pair-or-not-pair-by-axiom vs st)
  (define (decides-pair-goal v) 
    (disj* 
       (type-constraint v (list pair?)) 
       (type-constraint v (remove pair? all-inf-type-label))
       (is-of-finite-type v)
    ))
  (define axioms-on-each 
    (map decides-pair-goal vs))
  
  (define conj-axioms
    (foldl conj (Top) axioms-on-each))
  
  (pause st (conj conj-axioms (== 1 1)))
)

;;; return an equivalent stream of state, given a state
;;;  but in each state, there is no assymetric disequality
;;;     i.e. (var s) =/= (cons ...)
(define (remove-assymetry-in-diseq st)
  (define asymmetric-vars (record-vars-on-asymmetry-in-diseq st))
  (debug-dump "\n assymetric-st:  ~a \n asymmetric-vars: ~a" st asymmetric-vars)
  (if (equal? (length asymmetric-vars) 0)
    (wrap-state-stream st)
    (mapped-stream remove-assymetry-in-diseq (pair-or-not-pair-by-axiom asymmetric-vars st))))


;;; tproj :: var x List of ['car, 'cdr] 
;;; cxr as a path/stack of field projection/query
;;; (struct tproj (v cxr) #:prefab)
;;; (struct tcar (term) #:prefab)
;;; (struct tcdr (term) #:prefab)



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
  ;;; TODO: figure out why this reverse is necessary! -_-
  (cons (tproj-v x) (construct-sketch (reverse (tproj-cxr x))))
)

;;; given st x goal -> st x goal
;;;  with tproj all removed
(define (eliminate-tproj st goal)
  ;;; 0. we first collect all occurrence of tproj, collect into a set
  ;;; 1. we use equation-for-remove-tproj to remove each tproj, 
  ;;;     and remember what variable each tproj will be mapped to
  ;;; 2. we then do literal replace to remove tproj occurrences
  ;;; 3. we use unify-equations to make sure the equations are satisfied

  ;;; the collected tprojs
  (define all-tprojs (collect-tprojs st))
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
  (define res `(,(tcar (car eq)) . ,(tcar (cdr eq))))
  (match res 
    [(cons (var _ _) _) res]
    [(cons _ (var _ _)) (cons (cdr res) (car res))] 
    [_ res])
)
(define (tcdr-eq eq) 
  (define res `(,(tcdr (car eq)) . ,(tcdr (cdr eq))))
  (match res 
    [(cons (var _ _) _) res]
    [(cons _ (var _ _)) (cons (cdr res) (car res))] 
    [_ res])
)

;;; for Lisp universe, the only
;;;   non simple thing is pair
(define (not-simple-form x) (pair? x))
(define (is-simple-form x) (not (not-simple-form x)))

;;; given a set of equation (lhs must be var)
;;;  return an equivalent set of equation (lhs must be var)
;;;  s.t. the returned set won't have a equation like below
;;; (mentioned-var = (cons ... unmentioned-var ...))
;;; i.e. if one-side is mentioned var, then the other-side must be all mentioned
;;; TODO: 
;;;   change the algorithm to ranked-exposed-form
;;;     the var on right hand side must have lower rank then that on the LHS
;;;     the rank is decided by scope/mentioned-vars, as an ordered
(define/contract (unmentioned-exposed-form mentioned-vars st)
  (set? state? . -> . state?)
  (define eqs (state-sub st))
  ;;; (define (each-eliminate-cons single-eq) (list (tcar-eq single-eq) (tcdr-eq single-eq)))
  ;;; given one eq
  ;;;  return a list of eqs equivalent
  ;;;  and make sure in unmentioned-exposed-form 
  (define (single-unmentioned-exposed-form eq)
    (define fst (car eq))
    (define snd (cdr eq))
    
    
    (define is-unexposed-form
      (and (there-is-var-in mentioned-vars fst)
           (there-is-var-not-in mentioned-vars snd)))
    (define cons-at-right
      (pair? snd))
    (define is-simple-eq
      (and (is-simple-form fst) (is-simple-form snd)) )
    (if is-unexposed-form
      ;;; the following is quite twisted... 
      ;;; basically there are too many preconditions 
      (if is-simple-eq
        (list (cons snd fst))
        (if cons-at-right 
          ;;; at this point, we know 
          (eliminate-conses (list eq)) 
          (raise-and-warn "Unexpected Equation Form")))
      (list eq)
    )
  )
  (define new-eqs 
    (foldl append '()
      (map single-unmentioned-exposed-form eqs)))
  (state-sub-set st new-eqs)
)

;;; given a set of equations (lhs doesn't have to be variable)
;;;  return an equivalent set of equations (lhs must be variable)
(define (eliminate-conses eqs)
  (debug-dump "\n eliminate-conses's input: ~a" eqs)
  (define (each-eli-eq single-eq)
    ;;; won't stop if either side has cons
    (match single-eq
      [(cons LHS RHS)
        #:when (and (is-simple-form LHS) (is-simple-form RHS)) 
        (list single-eq)]
      [(cons (cons _ _) _) (eliminate-conses (list (tcar-eq single-eq) (tcdr-eq single-eq)))]
      [(cons _ (cons _ _)) (eliminate-conses (list (tcar-eq single-eq) (tcdr-eq single-eq)))]
      [_ (list single-eq)] ;; 
    )
  )

  (define (lhs-must-simple-var eq)
    (match eq
      [(cons LHS _) 
        #:when (term? LHS) 
        eq]
      [(cons LHS RHS) 
        #:when (term? RHS)
        (cons RHS LHS)]
      [_ (raise-and-warn "\n Not A proper substution-form Equation! ~a \n" eq)]
    )
  )
  (map lhs-must-simple-var
    (foldl append '() 
      (map each-eli-eq eqs)))
)

;;; ;;; clear everything about v on st
;;; ;;;  var x state -> state
;;; ;;;   done easily by replace v with a brand new var everywhere in the st
;;; (define/contract (clear-about v st)
;;;   (any?  ?state? . -> . ?state?)
;;;   ;;; (debug-dump st)
;;;   (let* ([vname (symbol->string (var-name v))]
;;;          [new-v (var/fresh (string->symbol (string-append vname "D")))]
;;;          [replaced (literal-replace v new-v st)]
;;;          )
;;;     replaced )
;;; )

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

;;; ;;; given a state, we 
;;; (define (not-mention-means-always-True st mentioned)

;;; )



;;; given a state in unmentioned-exposed-form
;;;   return a state, where unmentioned-var are replaced as much as possible
;;;     "as much as" is because there are cases that unmentioned-var
;;;     has no relationship with other vars, so cannot be eliminated
(define/contract (unmentioned-substed-form mentioned-vars st)
  (set? state? . -> . state?)
  (define old-eqs (state-sub st))
  (debug-dump "\n unmentioned-substed-form's input st: ~a" st)
  ;;; precondition: st has empty sub
  (define (unmention-remove-everywhere eqs st)
    ;;; (define eqs (state-sub st))
    (if (equal? eqs '())
      st
      (match (car eqs)
        [(cons v rhs)
          #:when (not (set-member? mentioned-vars v))
          (unmention-remove-everywhere (cdr eqs) (literal-replace v (walk* rhs (cdr eqs)) st))]
        [(cons v rhs)
          (state-sub-update 
            (unmention-remove-everywhere (cdr eqs) st)
            (lambda (eqs-) (cons (cons v rhs) eqs-)))]
      )
    ))
  ;;; (define new-eqs (filter (lambda (x) (set-member? mentioned-vars (car x))) old-eqs))
  
  (unmention-remove-everywhere old-eqs (state-sub-set st '()))
    
)



;;; DomainEnforcement -- basically currently make sure if term (tproj x car) appear
;;;   then x is of type pair
(define (domain-enforcement-st st) ;; (tproj x car.cdr.car) (typeconstant x car) pair
  (define all-tprojs (collect-tprojs st))
  (define sub (state-sub st))
  ;;; (tproj v path) x state -> state
  (define (force-as-pair term st) 
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
      (state-typercd-cst-add acc-st (walk* each-projed-term sub) (set pair?)))
  )
  (foldl (lambda (tp st) (force-as-pair tp st)) st (set->list all-tprojs))
)

;;; similar as above, but it deal with goal and returns goal
;;;  TODO: duplicate code: but abstract it away doesn't quite make interpretable sense
(define (domain-enforcement-goal goal)
  (define all-tprojs (collect-tprojs goal))
  ;;; var x goal -> goal
  (define (force-as-pair v g) (conj g (type-constraint v (list pair?))))
  (foldl (lambda (tp g) (force-as-pair (tproj-v tp) g)) goal (set->list all-tprojs))
)

;;; (define (state->goal st)
;;;   (define eqs (map (lambda (eq) (== (car eq) (cdr eq))) (state-sub st)))
;;;   (define types)
;;;   (define (disjunct-diseqs ls) 
;;;     (define all-eqs (map (lambda (eq) (=/= (car eq) (cdr eq))) ls))
;;;     (foldl disj (Top) all-eqs))
;;;   (define diseqs ())
;;;   (syntactical-simplify (conj (eqs types) disj))
;;; )

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

;;; given compositions of DS where there is tproj appearances
;;;  return a set of all tprojs
(define (collect-tprojs anything)
  (define result (mutable-set))
  (define (each-case prev-f rec g)
    (match g
      [(tproj _ _) (set-add! result g)] ;; local side-effect
      [o/w (prev-f g)]
    )
  )
  (define result-f 
    (overloading-functor-list (list each-case goal-term-base-endofunctor pair-base-endofunctor state-base-endo-functor identity-endo-functor))
  )
  (result-f anything)
  result

)

;;; anything (most likely pairs of goals) -> anything x List of equation
;;;   will remove every tproj, 
;;;    an gives a set of equation explaining the remove
;;;  for example (tproj x car) == k
;;;    will transform to (a == k) and a list of equation [(x (cons a b))]
(define (eliminate-tproj-return-record anything) ;; tproj x car.cdr.car ;; x = (cons (cons _ (cons _ _)) _)
  (define all-tprojs (set->list (collect-tprojs anything)))
  (define all-tproj-removing-eqs (map equation-for-remove-tproj all-tprojs))
  ;;; then we do huge literal-replace
  ;;;  the literal-replace respects 
  (define tproj-removed (literal-replace* (make-hash all-tproj-removing-eqs) anything))
  (debug-dump "\n eliminate-tproj-return-record's input: ~a" anything)
  (debug-dump "\n eliminate-tproj-return-record's input's tprojs: ~a" all-tprojs)

  (debug-dump "\n eliminate-tproj-return-record's using equation: ~a" all-tproj-removing-eqs)
  ;;; TODO : make sure that the constraint about (tproj x car) is transferred to the newly introduced var
  (debug-dump "\n eliminate-tproj-return-record's return: ~a" tproj-removed)
  
  ;;; TODO : make it into a contract
  (let* ([all-tproj (collect-tprojs tproj-removed)])
    (if (not (set-empty? all-tproj)) 
        (raise-and-warn "\n tproj elimination-failed ~a \n -> \n ~a \n gen-context of ~a \n" anything tproj-removed all-tproj-removing-eqs)

        'pass))
  (cons tproj-removed all-tproj-removing-eqs)
)


;;; given a state, and the scope with the set of vars should be considered fixed
;;;  return a goal/proposition that
;;;   is the complement the domain of var in the state
;;;   other variables not mentioned in scope and var should be dealt with properly
;;; precondition: 
;;;    st is in conjunction form (i.e. there is no disjunction in diseq)
;;;    st is in non-asymmretic form (i.e. no (var ..) =/= (cons ...))
;;;    st is in unmentioned-substed-form, where mentioned var are scope + var
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
  ;;; (define unmentioned-exposed-subst (unmentioned-exposed-form mentioned-vars (state-sub st)))
  ;;; Step 1 done
  ;;; this will literally remove the appearances of unmentioned var
  ;;;  according to eqs, except for those inside subst of st
  

  ;;; (define unmention-substed-st st)
  ;;; Step 2 done
  (define domain-enforced-st st)
  ;;;  we remove none-substed appearances of unmentioned var
  (define unmentioned-removed-st
    (let* ([diseqs (state-diseq domain-enforced-st)]
           [new-diseq (filter (lambda (p) (not (there-is-var-not-in mentioned-vars p))) diseqs)] ;; diseqs must be list of singleton list of thing
           [type-rcd-lst (hash->list (state-typercd domain-enforced-st))]
           [new-typercd-lst (filter (lambda (v) (not (there-is-var-not-in mentioned-vars v))) type-rcd-lst)]
           [new-typercd (make-hash new-typercd-lst)])
    (state-diseq-set 
      (state-typercd-set domain-enforced-st new-typercd)
      new-diseq)))
  ;;; Step 3 done
  (define atomics-of-states (conj-state->list-of-goals unmentioned-removed-st))
  (define atomics-of-var-related (filter (lambda (x) (there-is-var-in (set varx) x)) atomics-of-states))
  (define atomics-of-var-unrelated (filter (lambda (x) (not (there-is-var-in (set varx) x))) atomics-of-states) )
  (define complemented-atomics-of-var-related 
    (map complement atomics-of-var-related))
  (define domain-enforced-complemented-atomics-of-var-related 
    (map domain-enforcement-goal complemented-atomics-of-var-related))
  ;;; we are almost done but we need to remove tproj
  (define conj-unrelated 
    (syntactical-simplify (foldl conj (Top) atomics-of-var-unrelated)))
  (define disj-related 
    (foldl disj (Bottom) domain-enforced-complemented-atomics-of-var-related))
  ;;; (define disj-related-
  ;;;   (if (equal? disj-related (Bottom))
  ;;;     (Top)
  ;;;     disj-related
  ;;;   )
  ;;; )

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
;;;    st is in unmentioned-substed-form, where mentioned var are scope + var
;;;   st is domain-enforced
(define/contract (shrink-away st scope var)
  (state? set? var? . -> . state?)
  (define mentioned-vars (set-remove scope var))
  (define v-exposed-st (unmentioned-exposed-form mentioned-vars st))
  (define var-removed-st (unmentioned-substed-form mentioned-vars v-exposed-st))
  ;;; (define var-removed-st st)
  ;;; (debug-dump "\n shrink-var-removed-st: ~a" var-removed-st)
  (define domain-enforced-st var-removed-st)
  ;;;  we remove none-substed appearances of unmentioned var
  (define unmentioned-removed-st
    (let* ([diseqs (state-diseq domain-enforced-st)]
           [new-diseq (filter (lambda (p) (not (there-is-var-not-in mentioned-vars p))) diseqs)] ;; diseqs must be list of singleton list of thing
           [type-rcd-lst (hash->list (state-typercd domain-enforced-st))]
           [new-typercd-lst (filter (lambda (v) (not (there-is-var-not-in mentioned-vars v))) type-rcd-lst)]
           [new-typercd (make-hash new-typercd-lst)])
    (state-diseq-set 
      (state-typercd-set domain-enforced-st new-typercd)
      new-diseq)))
  ;;; then we eliminate tproj
  (define tproj-eliminated (eliminate-tproj-return-record unmentioned-removed-st))
  (define tproj-eliminated-content (car tproj-eliminated))
  (define tproj-eliminated-evidence (cdr tproj-eliminated))
  (unifies-equations tproj-eliminated-evidence tproj-eliminated-content)
)

;;; the same shrink-away but don't require much precondition
;;; return a stream of states
;;;   where the stream is equivalent to the states of clearing
;;;   also remove things from scope
(define/contract (clear-about state scope v)
  (state? set? var? . -> . any?)
  (define dnf-sym-stream (TO-DNF (TO-NON-Asymmetric (wrap-state-stream state))))

  (define mentioned-var (set-remove scope v))
  (define (map-clear-about st)
    (let* (
        [current-vars scope]
        [unmentioned-exposed-st (unmentioned-exposed-form mentioned-var st)]
        [unmention-substed-st (unmentioned-substed-form mentioned-var unmentioned-exposed-st)] 

        [domain-enforced-st (domain-enforcement-st st)]
        [shrinked-st (shrink-away domain-enforced-st current-vars v)]
        )
        (wrap-state-stream (state-scope-update shrinked-st (lambda (scope) (set-remove scope v))))
        ))
  (mapped-stream map-clear-about dnf-sym-stream)
)