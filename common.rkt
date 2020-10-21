#lang racket
(provide
  (struct-out var)
  initial-var
  var/fresh
  (struct-out state)
  empty-state
  state-sub
  state-direction-set
  shadow-idempotent-sub
  trace-left
  trace-right
  unify
  walk*
  unitize-metavar
  reify
  reify/initial-var
  neg-unify
  wrap-state-stream
  check-as-disj
  check-as
  type-label-top
  true?
  false?
  )

;;; bear with it now.... let me search if there is
;;;  extensible record later
(require struct-update)

;; Logic variables
(struct var (name index) ;;;#:prefab
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a#~a" (var-name val) (var-index val)))]
)
(define (var=? x1 x2)
  (= (var-index x1) (var-index x2)))
(define initial-var (var #f 0))

(define var/fresh (void))
;; return a new var with incremented id
(define var-reset! (void)) 
;; reset the maximum existing var-id to 0
(define var-number (void)) 
;; return the maximum existing var-id, unless it is 0


(let ((index 0))
  (begin 
    (set! var/fresh     
      (lambda (name) 
        (set! index (+ 1 index))
        (var name index)))
    (set! var-reset!
      (lambda () (set! index 0)))
    (set! var-number (lambda () index))  
  )
)

;;; (define var/fresh
;;;   (let ((index 0))
;;;     (lambda (name) (set! index (+ 1 index))
;;;       (var name index))
;;;       ))

;; States
(define empty-sub '())
(define (walk t sub)
  (let ((xt (and (var? t) (assf (lambda (x) (var=? t x)) sub))))
    (if xt (walk (cdr xt) sub) t)))
(define (occurs? x t sub)
  (cond ((pair? t) (or (occurs? x (walk (car t) sub) sub)
                       (occurs? x (walk (cdr t) sub) sub)))
        ((var? t)  (var=? x t))
        (else      #f)))

(define (extend-sub x t sub)
  (and (not (occurs? x t sub)) `((,x . ,t) . ,sub)))
;;; the above version is causing substitution "non-compositional"
;;;   the reason this thing comes up is motivated by two reasons:
;;; 1. each sigma is not idempotent currently 
;;;  (this sentence might not make sense, )
;;; 2. there is no easy way to represent sigma_1 \compose sigma_2, 
;;;       where sigma_1,2 are both of type List, and their composition is still List
;;;    (the real reason is 1.) 
;;; 3. there is no easy way to represent (shadow x sigma_1), 
;;;     i.e. subst everything as sigma except variable x
;;;    (the real reason is still 1.)
;;;     for example [(v1 v3) (v2 v1) (v3 1)] , 
;;;       whose idempotent version is [(v1 1) (v2 1) (v3 1)]
;;;     and if we want to shadow v1 (fix v1 unchanged)
;;;       we cannot just remove (v1 v3) from the list, otherwise we will get a thing
;;;       that is [(v2 v1) (v3 1)], that cannot map v1 to 1
;;;     similarly, [(v1 v1) (v1 v3) (v2 v1) (v3 v1)] won't work 


;;; same as extend-sub, except the input has to be idempotent, 
;;;   and its output is also idempotent 
(define (extend-idempotent-sub x t sub)
  ;;; TODO: to implement in the future, currently just use the non-idempotent version
  (extend-sub x t sub)
)

;;; var x [(var . term)] -> [(var . term)]
;;;  precondition: subst is already idempotent, 
;;;   i.e. the range of subst doesn't intersect its domain 
;;;  specification: it will substitute just as subst, except for x, it won't change
(define (shadow-idempotent-sub x subst)
  (filter (lambda (pair) (not (equal? (car pair) x))) subst)
)

(define (true? v) (equal? v #t))
(define (false? v) (equal? v #f))
;;; (null? '() )

(define type-label-top (list true? false? null? pair? number? string? symbol?))
;;; TODO: if all of the elements in type set are for the finite, 
;;;   then inequality might cause trouble  
;;;   for example, (exists x y z.) they are all different, they are all booleans

;;; sub -- list of substution 
;;; diseq -- list of list of subsitution 
;;;     -- interpreted as conjunction of disjunction of inequality 
;;; assymbol/asstring/asnumber are all a list of variables
;;;   to indicate disjoint sets
;;;   typercd : a dictionary index -> type-encoding 
;;;     "as disjunction of possible types"
;;;   
(struct state (sub trace direction diseq typercd) #:prefab)
(define empty-state (state empty-sub '() '() '() (hash)))
(define-struct-updaters state)

(define (trace-left st)
  (state-trace-update st (lambda (x) (cons 'left x))))

(define (trace-right st)
  (state-trace-update st (lambda (x) (cons 'right x))))
;;;  purely functional structure update, 


;;;  TODO:let's later make trace-left/right row polymorphic
;;;   so that we can decouple trace field and direction field out of state


;; Unification
(define (unify/sub u v sub)
  (let ((u (walk u sub)) (v (walk v sub)))
    (cond
      ((and (var? u) (var? v) (var=? u v)) sub)
      ((var? u)                            (extend-sub u v sub))
      ((var? v)                            (extend-sub v u sub))
      ((and (pair? u) (pair? v))           (let ((sub (unify/sub (car u) (car v) sub)))
                                             (and sub (unify/sub (cdr u) (cdr v) sub))))
      (else                                (and (eqv? u v) sub)))))


;;; (define (unify u v st)
;;;   (let ((sub (unify/sub u v (state-sub st))))
;;;     (and sub (cons (state sub (state-trace st)) #f))))

(define (wrap-state-stream st) (and st (cons st #f)))


(define (unify u v st)

  ;;; inequality-recheck :: state -> state
  (define (inequality-recheck st)
    (define conj-all-diseq (state-diseq st))
    (foldl neg-unify* st conj-all-diseq)
  )

  (let* ([sub (unify/sub u v (state-sub st))]
         [htable (state-typercd st)])
    (and sub
      (let* ([unified-state (state-sub-set st sub)]
              ;;;  sub : var -> term
              ;;;   term -> type
              ;;;  check
              [new-subst (extract-new sub (state-sub st))]
              ;;;  extract newly added variables
              ;;;  [(u v), (j k)]
              [new-vars (map car new-subst)]
              [new-vars-indices (map var-index new-vars)]
              ;;; TODO: unifies the representation
              [new-vars-types (map (lambda (x) (hash-ref htable x #f) ) new-vars-indices)]
              [erased-htable (foldl (lambda (index htable) (hash-remove htable index)) htable new-vars-indices)]
              [erased-type-state (state-typercd-set unified-state erased-htable)]
              ;;; TODO: check-as-disj might have corner 
              ;;;   case where first element is null
              ;;; helper function that do things like flatmap
              ;;;  check-as-on-each :: type-label  x term x stream[st] -> stream[st]
              ;;;  erased-type-state :: st  (as initial state)
              ;;;  new-vars-types :: list of type-label
              ;;;  new-vars :: list of term
              ;;; checked-type-states :: matured-stream[st]
              [checked-type-states (foldl check-as-on-each 
                                         (wrap-state-stream erased-type-state)
                                         new-vars-types new-vars)]
              ;;; [all-diseq (and checked-type-state 
              ;;;             (state-diseq checked-type-state))]
              )
        ;;;  TODO: short-circuit the possible #f appearing inside foldl
        (map inequality-recheck checked-type-states)
  ))))

;; Reification
(define (walk* tm sub)
  (let ((tm (walk tm sub)))
    (if (pair? tm)
        `(,(walk* (car tm) sub) .  ,(walk* (cdr tm) sub))
        tm)))
(define (reified-index index)
  (string->symbol
    (string-append "_." (number->string index))))

;;; initial version of reify, for future reference
(define (reify tm st)
  (define index -1)
  (walk* tm (let loop ((tm tm) (sub (state-sub st)))
              (define t (walk tm sub))
              (cond ((pair? t) (loop (cdr t) (loop (car t) sub)))
                    ((var? t)  (set! index (+ 1 index))
                               (extend-sub t (reified-index index) sub))
                    (else      sub)))))

(define (reify-cst tm st)
  (define index -1)
  (define everything-to-print 
    (list tm (state-diseq st)))
  ;;; we need to fill in the un-restricted value, for example, (== x x)
  ;;;   it means no restriction is required, and for them, _.0 as value will be ok
  ;;;   the complicated loop below is to fill-in those un-restricted value
  (define full-sub 
    (let loop ((tm everything-to-print) (sub (state-sub st)))
        (define t (walk tm sub))
        (cond ((pair? t) (loop (cdr t) (loop (car t) sub)))
              ((var? t)  (set! index (+ 1 index))
                          (extend-sub t (reified-index index) sub))
              (else      sub))))
  (define tm-result (walk* tm full-sub))
  (define conj-disj-diseqs 
    ;;; TODO: pretty print it! 
    (walk* (state-diseq st) full-sub)
    )
  
  `(,tm-result : ≠ ,conj-disj-diseqs )
  )           
(define (reify/initial-var st)
  (reify initial-var st))

;;; reify the variable toggether with the constraints
;;; 
(define (reify/initial-var/csts st)
  (reify/initial-var st)
)


;; Replace Meta-var inside term with Unit
(define (unitize-metavar tm)
  (let ([um unitize-metavar])
    (match tm
      [(var _ _) '()]
      [(cons a b) (cons (um a) (um b))]
      [x x]
    )
  )
)


;;; subroutine : extract the added substiution
;;;  or return #f if input is #f 
;;; 
(define (extract-new new original)
  (and new
    (if (eq? new original)
    '()
    (match new 
      [(cons fst tail) (cons fst (extract-new tail original))])))
)


;;; dis-unification, we try to find the solution
;;;   for u =/= v
;;;   and return a list of state that satisfies the inequalities between u v
(define (neg-unify u v st)
  (let* ([result (neg-unify* (list `(,u . ,v)) st)])
    (and result (cons result #f)))
)

;;; neg-unify* : given a list of pairs, indicating 
;;;   disjunction of inequality, solve them according to the current state
;;;   return a state that satisifies the disjunction of inequalities
(define (neg-unify* list-u-v st)
  (match list-u-v 
    ['() #f]
    [(cons (cons u v) rest) 
        (let* (
          [subst (state-sub st)]
          [unification-info (unify/sub u v subst)]
          [newly-added (extract-new unification-info subst)]
              ;;; I should check unification result
          )
    (match newly-added
      ;;; 1. if unification fails, then inequality is just satisfied 
      ;;;     st is directly returned
      [#f st]
      ;;; 2. if unification succeeded, this mean the current state cannot
      ;;;     satisifies the inequality, let's consider the next possible-inequality
      ['() (neg-unify* rest st)]
      ;;; 3. if unification succeeded with extra condition
      ;;;     that means inequality should succeed with extra condition
      ;;;     we lazily put these things together and store into state
      [(cons _ _) 
        (state-diseq-update st (lambda (x) (cons (append newly-added rest) x)))
        ])       
        )
      ]
  )
)

(define (neg-unify-with-typeinfo* list-u-v st)
  (define (compute-newly-added u-v)
    (let* ([subst (state-sub st)]
           [unification-info (unify/sub (car u-v) (cdr u-v) subst)]
           [newly-added (extract-new unification-info subst)])
      newly-added      
    )
  )

  (let* ([list-newly-adds-on-each-u-vs (map compute-newly-added list-u-v)]
         )
    (if (ormap not list-newly-adds-on-each-u-vs) 
      st
      (match (append* list-newly-adds-on-each-u-vs)
      ['() #f]
      [(list (cons u #f)) (check-as-disj (remove false? type-label-top) u st)]
      ;;; TODO: #t, '()
      ;;;  we need to upgrade inequality into type constraint
      [_
       (state-diseq-update st (lambda (x) (cons new-adds-on-all x)))
      ]
    )
  )


  )
)


;;; neg-unify* : given a list of list of pairs, indicating 
;;;   conjunction of disjunction of inequality, 
;;;    solve them according to the current state
;;; (define (neg-unify** list-list-u-v st)
;;;   (match list-list-u-v
;;;     ['() st]
;;;     [(cons head tail) 
;;;       (neg-unify** tail (neg-unify* head st))
;;;     ]
;;;   )
;;; )


(define singleton-type-map
  (hash
    true? #t
    false? #f
    null? '()
  )
)

(define (is-singleton-type x) (hash-ref singleton-type-map x #f))


;;; check-as-disj: List[type-predicate] x term x state -> Stream[state]
;;;  currently it will use predicate as marker
;;;  if type-predicate == #f, then state unchanged returned
;;;  precondition: type?* is never #f, st is never #f
(define (check-as-disj type?* t st)

  (define inf-type?* (filter (lambda (x) (not (is-singleton-type x))) type?*))

  (define infinite-type-checked-state ;;; type : state
    (match (walk* t (state-sub st))
          [(var _ index) 
            ;;; check if there is already typercd for index on symbol
            (let* ([htable (state-typercd st)]
                   [type-info (hash-ref htable index #f)])
              (if type-info
                ;;; type-info is a set of predicates
                ;;;  disjunction of type is conflicting
                (let* ([intersected (set-intersect type-info type?*)])
                ;;;  TODO: when intersected result is actually just pair?, 
                ;;;    we need to make a substitution

                ;;; if it is empty list then we failed
                  (match intersected
                    ['() #f]
                    ;; this part is very weird... as we can see most fresh is not really existential
                    ;;;   quantifier because they don't specify scope!!
                    ;;;  here it is even more complicated ... what is the scope of a b?
                    ;;;    if we don't know the scope, will it cause problem when generating trace?
                    [(list pair?) (fresh (a b) (== t (cons a b)))]  
                    [_   (state-typercd-update st (lambda (x) (hash-set x index intersected)))]
                    )
                  
                )
                 (state-typercd-update st (lambda (x) (hash-set x index type?*)))) ) ]

          [v (and (ormap (lambda (x?) (x? v)) type?*) st)]) )
    
    ;;; each possible type indicate a different state in the returned list
    (define finite-type-checked-states ;;; list of states
      (define finite-type-labels (filter is-singleton-type type?*))
      (define finite-objects (map (lambda (x) (hash-ref singleton-type-map x #f)) finite-type-labels))
      
      (define (check-as-object each-obj) ;;; state
        (match (walk* t (state-sub st))
          [(var _ index) 
            ;;; check if there is already typercd for index on symbol
            (let* ([htable (state-typercd st)]
                   [type-info (hash-ref htable index #f)])
              (if type-info
                ;;; type-info is a set of non-empty predicates
                ;;;  directly conflicting, 
                #f
                (state-sub-update st (lambda (sub) (unify/sub t each-obj sub) )) ) ) ]
          [v (state-sub-update st (lambda (sub) (unify/sub t each-obj sub) )) ])
      )
      (map check-as-object finite-objects)
    )

    (define all-type-checked-states
      (filter (lambda (x) x) (cons infinite-type-checked-state finite-type-checked-states))
    )
    (match all-type-checked-states
      ['() #f]
      [_ (foldl cons #f all-type-checked-states)]
    )
    ;;; then we combine into stream of state
)

;;; check-as :: type-label  x term x st -> stream[st]
(define (check-as type? t st) (check-as-disj (list type?) t st))

(define (map-matured-stream f stream)
  (match stream
    [#f #f]
    [(cons h t) (cons (f h) (map-matured-stream f t))]
  )
)

(define (fold-matured-stream binary initial-state stream)
  (match stream
    [#f initial-state]
    [(cons h t) (fold-matured-stream binary (binary h initial-state) t)]
  )
)

(define (append-matured-stream a b)
  (match a 
    [#f b]
    [(cons h t) (cons h (append-matured-stream t b))]
  )
)

;;; lift check-as onto stream
;;; check-as-on-each :: type-label  x term x matured-stream[st] -> matured-stream[st]
;;;  when type-label = #f, we think of it as don't do any check, thus return original stream
(define (check-as-on-each type? t sts)
  (if (equal? type? #f)
    sts
    (fold-matured-stream 
        append-map-matured-stream 
        #f 
        (map-matured-stream (lambda (st) (check-as type? t st)) sts))
  )
)
