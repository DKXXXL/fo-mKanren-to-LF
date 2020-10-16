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

;;; streams
(struct bind   (bind-s bind-g)          #:prefab)
(struct mplus  (mplus-s1 mplus-s2)      #:prefab)
(struct pause  (pause-state pause-goal) #:prefab)


;;; the special stream only used for forall
;;;   all the possibe results of first-attempt-s
;;;   will be complemented and intersect with the domain of the bind-g
;;;   bind-g will have to be a forall goal
(struct bind-forall   (first-attempt-s bind-g)          #:prefab)


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
    ((symbolo t1) (wrap-state-stream (check-as symbol? t1 st)))
    ((numbero t1) (wrap-state-stream (check-as number? t1 st)))
    ((stringo t1) (wrap-state-stream (check-as string? t1 st)))
    ((ex _ gn) (start st gn))
    ;;; forall is tricky, 
    ;;;   we first use simplification to
    ;;;   we first need to consider forall as just another fresh
    ;;;   and "bind" the complement of result to the nexttime forall as domain
    ;;;   
    ((forall var domain goal) 
      (let* [(domain_ (simplify-wrt domain var (void)))] 
        (if (equal? domain_ False) 
          (wrap-state-stream st)
          (bind-forall (start st (ex var (conj domain goal))) g)
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
    ((bind-forall s (forall v domain goal))
      (let* [] 

      )
    )
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
      [(forall a gn) (ex a (c gn))]
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


;;; the following two requires some design pattern.
;;;  I am doing too much traversal

;;; not-symbolo will be translated into (numbero v stringo v pairo)
(define (remove-neg-by-decidability goal)
  (define (match-single g)
    (match g
      [(not-symbolo x) ]
    )
  )
)

;;; simplify goal w.r.t. a domain variable, constant parameters acceptable
;;;   do nothing on higher-order goal (for example, the ex and forall)
;;;   higher-order goal is not likely to happen as the answer for each run 
;;;     doesn't have exists/forall as result
;;;  this procedure currently is 
;;; 0. it will directly evaluate the constraints only on constant parameters
;;;     because they are constants, and every atomic statement now is decidable
;;; 1. it will first transform each not-TYPEO into a disjunction of TYPEO, 
;;;     and we will introduce existential quantifier for pairo
;;; 2. it will then transform into disjunctive normal form, "higher-order goals" (pairo)
;;;  are just considered as a whole
;;;     Note: we should be able to control the shape of "higher-order  goals" to make sure
;;;       it won't be arbitrarily complicated, so that syntactical level simplification can
;;;       still be effective...
;;; 3. for each conjunction component, we will do simiplification
;;;  3.1 by first sort all the constraints -- equality constraint is at the beginning 
;;;     and then type constraints 
;;;     and then inequality, and then it is the higher-order goals (pairo)
;;;  3.2 then we do simplification on each conjunctive component
;;; 4. then we sort the disjunctive list of conjunction component (and do simplification?)
;;;   4.1 we don't quite care about the disjunction actually, as long as not all of conjunctive
;;;   component is bottom, then we should continue the search (domain is non-empty)
;;;  the main goal is to evaluate the "goal" into Bottom as much as possible
;;;   it is mainly used for domain exhaustive check
(define (simplify-wrt goal dv dec-constant-statement)
  (void)
)
;;; simplify list of goal
;;;  given a list of goals indicating the conjunction of goals
;;;     each goal has to be atomic (i.e. no conjunction inside)
;;;    we will do simplification with respect to a single dv (domain-variables)
;;;   other variables will be considered as constant, and thus they should be 
;;;     evaluated to Bottom or Top immediately
;;;     as currently every atomic statement is decidable
;;;  currently it is at least O(n^2), there is definitely optimization
;;;    

;;; map each label into a higher order goal constructor
;;; LABEL -> (term -> goal)
;;;  for example, predicate "number?" will be mapped to numbero
(define (label-to-goal label)
  (match label
    [number? numbero]
    []
  )
)

;;; map a list of labels to disjunctive of goal constructor
;;; "Set of LABEL" -> (term -> goal)
;;;  used when typercd encode disjunction of types
(define (labels-to-goal labels) 
  ;;; disjunc : (term -> goal) x (term -> goal) -> (term -> goal)
  (define (disjunc f g) (lambda (term) (disj (f term) (g term))))
  (define disjunc-id (lambda (term) Bottom))
  (foldl disjunc disjunc-id (map labels labels)))

;;; this function will translate state into goals
(define (state-to-goal st)
  (let* ([sub (state-sub st)]
         [eqs-goal (foldl (lambda (p g) (conj (== (car p) (cdr p)) g)) 
                     Top sub)]
         [diseq (state-diseq st)]
        ;;;  recall diseq is list of list of pairs
        ;;;   indicating disjunction of conjunction of inequality
            [conj-diseq-fold 
              (lambda (l) (foldl (lambda (p g) (conj (=/= (car p) (cdr p)) g)) Top l))]
            [disj-conj-diseq-fold
              (lambda (l) (foldl (lambda (lp g) (disj (conj-diseq-fold lp) g)) Bottom l))]
         [diseqs-goal (disj-conj-diseq-fold diseq)]
         [type-dict (state-typercd st)]
         [type-pairs (hash->list type-dict)]
         [type-goals (foldl )]
         )

  )
)