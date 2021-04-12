#lang errortrace racket
(provide
  (struct-out var)
  initial-var
  var/fresh
  (struct-out tp-var)
  (struct-out state)
  (struct-out tproj)
  tcar
  tcdr
  tproj_
  empty-state
  state-sub
  state-sub-set
  state-sub-update
  state-diseq-set
  state-diseq-update
  state-scope-update
  state-scope-set
  state-typercd-cst-add
  state-typercd-set
  unify
  unify/sub
  walk*
  term?
  reify
  reify/initial-var
  neg-unify
  wrap-state-stream
  check-as-inf-type-disj
  check-as-inf-type
  type-label-top
  all-inf-type-label
  true?
  false?
  any?
  ?state?
  debug-dump-w/level
  debug-dump
  debug-dump-off
  raise-and-warn
  assert-or-warn
  assert
  valid-type-constraints-check
  set-debug-info-threshold!
  )


(require racket/contract)
(require errortrace)
(require "microk-fo-def.rkt")


;;; we introduce monadic style of coding
;;;   as we will need to change state during

;;; we need to introduct a racket/generic for isNothing
;;; so that WithBackground is basically StateT (Maybe T)
;;;  see https://docs.racket-lang.org/reference/struct-generics.html

;;; we can even later supports polymorphic rows/effect for it
;;;  as we are untyped stuff
;;; TODO: bg->front = bg -> (bg, front | #f)
;;;   and bg supports Emptyable as racket/generic
;;;     Emptyable supports isNone? and none operation
(struct WithBackground (bgType bg->front) 
    #:guard (lambda (bgT? bgf type-name)
                    (cond
                      [(andmap procedure? (list bgT? bgf)) 
                       (values 
                          bgT? 
                          (invariant-assertion 
                            (bgT? . -> . (pair-of? bgT? any?)) 
                            bgf))]
                      [else (error type-name
                                   "Should be a hashmap")]))
;;; #:prefab
)


(define (WithBackgroundOf? u?) 
  (λ (k)
    (and (WithBackground? k) (u? (WithBackground-bgType k)))))


(define (=== k) (λ (x) (equal? x k)))

;;; dbginfo
(define/contract (>>= fwb domap dbginfo)
  (WithBackground? (any? . -> . WithBackground?) any? . -> . WithBackground?)
  (WithBackground
    (WithBackground-bgType fwb)
    (let*
      ([isNone? false/c] ;; BUGFIX: adopt to generic later
       [fwbdo (WithBackground-bg->front fwb)])
        (λ (bg)
            (if (isNone? bg)
              (cons bg #f)
              (match-let* 
                  ([(cons bg1 fr1) 
                      (with-handlers 
                        ([any? (λ (e) (printf "Error is invoked from do: ~s\n" dbginfo) (raise e))])
                        (fwbdo bg))]
                   [(WithBackground _ swbdo) (domap fr1)]
                   [bg2+fr2 (swbdo bg1)])
                bg2+fr2))))))

(define (>> a b) (>>= a (λ (_) b) #f))

;;; Recall that
;;; get :: (WB state-type state-type)
;;; set :: state-type -> (WB state-type '())
;;;   we might be able to support polymorphic rows/effect (not type inference)
;;;     on this two operations
;;; >>= :: (WB x K) x (K -> WB x Y) -> (WB x Y)
;;; most importantly : do notation
;;; (do [x = y] sth ...) = match-let ([x y]) in (do sth ...) : (WithBackground ...)
;;; (do [x <- y] sth ...) = 
;;;     assert y of type (WB ...)
;;;     y >>= \x -> (do sth ...)
;;; with above it is easy to see that we can 
;;; (do [_ <- y] sth ...) = y >> (do sth ...) 
;;; (do [<-end x]) = x
;;; (do [<-return x]) = (pure-st x)
;;;     usually it is  

;;; (define-syntax (here stx)
;;;     #`(list (quote-line-number #,stx)))

;;; (define-syntax stab-trace
;;;   (syntax-rules ()
;;;     ((_ number k)
;;;        ((λ (_ t) t) "INFO" k) )
;;;     ((_ k)
;;;        ((λ (_ __ t) t) "LINE" (here) k) )   ))

(define-syntax do
  (syntax-rules (<- <-end <-return =)
    ((_ [ x = y ] sth ...) 
      (match-let ([x y]) (do sth ...)))
    ((_ [ x <- y ] sth ...) 
      (let* ([_ (assert-or-warn (WithBackground? y) "Type Error at :~s\n" #'y)])
         (>>= y (match-lambda [x (do sth ...)]) #'y)) ) 
    ((_ [ <-end y ]) 
      (let* ([_ (assert-or-warn (WithBackground? y) "Type Error at :~s\n" #'y)]) 
        y))
    ((_ [ <-return y ]) 
      (pure-st y))
  ))


;;; can we multi-stage it? I mean partially evaluate monadic style
;;; change the following into macro
(define (get ty) (WB ty (λ (bg) (cons bg bg))))
(define (set ty) (λ (term) (WB ty (λ (_) (cons term '())))))
(define (pure ty) (λ (term) (WB ty (λ (bg) (cons bg  term)))) )
(define (run ty)  
  (invariant-assertion
    (ty (WithBackgroundOf? (=== ty)) . -> . any?)
    (λ (st wb)
    (match-let* 
      ([(WithBackground ty? bg->front) wb]
       [_ (assert-or-warn (ty? st) "Wrong WithBackground Invocation\n")])
      (bg->front st))))
  )
(define (modify ty)
  (λ (f)
    (do [st <- get-st]
        [_ <- (set-st (f st))]
        [<-return '()])))




(define get-st  (get state-type?))
(define set-st  (set state-type?))
(define pure-st (pure state-type?))
(define run-st  (run state-type?))
(define modify-st (modify state-type?))
(define failed-current-st
  (do 
    [_ <- (set-st #f)]
    [<-return #f]
  ) 
)




;;; Will totally ignore tproj (doing nothing on them)
(define (walk t sub)
  ;;; (debug-dump "walk: ~a with ~a \n" t sub)
  (match t
    [(? var?) 
      (let ((xt (assf (lambda (x) (equal? t x)) sub)))
        (if xt (walk (cdr xt) sub) t))]
    [_ t]
  )
)


;;; TODO: think about if tproj will cause problems
(define (occurs? x t sub)
  (cond ((pair? t) (or (occurs? x (walk (car t) sub) sub)
                       (occurs? x (walk (cdr t) sub) sub)))
        ((var? t)  (equal? x t))
        (else      #f)))

(define (extend-sub x t sub)
  (and (not (occurs? x t sub)) `((,x . ,t) . ,sub)))



(define (true? v) (equal? v #t))
(define (false? v) (equal? v #f))


(define type-label-top (set true? false? null? pair? number? string? symbol?))
(define all-inf-type-label (set pair? number? string? symbol?))





;; Unification
(define (unify/sub u v sub)
  (let ((u (walk u sub)) (v (walk v sub)))
    (cond
      ((and (var? u) (var? v) (equal? u v)) sub)
      ((var? u)                            (extend-sub u v sub))
      ((var? v)                            (extend-sub v u sub))
      ((and (pair? u) (pair? v))           (let ((sub (unify/sub (car u) (car v) sub)))
                                             (and sub (unify/sub (cdr u) (cdr v) sub))))
      (else                                (and (eqv? u v) sub)))))


;;; return a state where except for substitution list, 
;;;   every variable appearing 
;;;     is the representative of the equality class of the variable
;;; Note: if st has type-constraint on two var (with same equality class)
;;;     this might lead to some problems
(define/contract (canonicalize-state st)
  (state? . -> . state?)
  (define current-sub (state-sub st))
  (define current-scope (state-scope st))
  (define st-without-sub-and-scope 
    (state-scope-set (state-sub-set st empty-sub) '()))

  (define (each-case rec-parent rec g)
    (match g
      [(var _ _) (walk* g current-sub)] 
      [o/w (rec-parent g)]))
  (define result-f 
    (compose-maps (list each-case goal-term-base-map pair-base-map state-base-endo-functor hash-key-value-map identity-endo-functor)))
  (state-scope-set
    (state-sub-set (result-f st-without-sub-and-scope) current-sub)
    current-scope
    )
)

;;; return a state where except for substitution list, 
;;;   every variable appearing 
;;;     is the representative of the equality class of the variable
;;; Note: if st has type-constraint on two var (with same equality class)
;;;     this might lead to some problems
(define/contract (canonicalized-state? st)
  (state? . -> . boolean?)
  (define current-sub (state-sub st))
  (define st-without-sub-and-scope 
    (state-scope-set (state-sub-set st empty-sub) '()))

  ;;; using visitor + side effect
  (define there-is-non-canonical-var? #f)
  (define (each-case rec-parent rec g)
    (match g
      [(var _ _)
          (begin 
            (if (not (equal? g (walk* g current-sub)))
                (set! there-is-non-canonical-var? #t)
                (void))
            g)] 
      ;;; short-circuit
      [o/w (if there-is-non-canonical-var? g (rec-parent g))]))
  (define result-f 
    (compose-maps (list each-case goal-term-base-map pair-base-map state-base-endo-functor hash-key-value-map identity-endo-functor)))
  (result-f st-without-sub-and-scope)
  (not there-is-non-canonical-var?)
)

(define ?canonicalized-state? (or/c false/c canonicalized-state?))



(define (wrap-state-stream st) (and st (cons st #f)))

;;; state x var x (set of/list of) typeinfo -> state
(define/contract (state-typercd-cst-add st v type-info)
  (state? term? set? . -> . state?)

  (define typerc (state-typercd st))
  ;;; (define type-info (if (set? type-info) type-info (set type-info)))
  (define org (hash-ref typerc v #f))
  (define new-type-info 
    (if org 
      (hash-set typerc v (set-intersect org type-info))
      (hash-set typerc v type-info)))
  (state-typercd-set st new-type-info)
)

(define (any? _) #t)

;;; check if a given state has a valid/consistent type constraints
;;;   if not, return #f
(define/contract (valid-type-constraints-check st)
  (state? . -> . any?)
  (define typecses (state-typercd st))
  (define old-st (state-typercd-set st (hash)))
  (for/fold
    ([acc-st old-st])
    ([each-var-types (hash->list typecses)])
    (check-as-inf-type-disj (cdr each-var-types) (car each-var-types) acc-st)))

(define/contract (unify u v st)
  (any? any? state? . -> . Stream?)
  ;;; inequality-recheck :: state -> state
  (define (inequality-recheck st)
    (define conj-all-diseq (state-diseq st))
    (define (neg-unify*-on-corner list-u-v st)
      (and st (neg-unify* list-u-v st))
    )
    (foldl neg-unify*-on-corner (state-diseq-set st '()) conj-all-diseq)
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
              ;;; [new-vars-indices (map var-index new-vars)]
              ;;; TODO: unifies the representation
              [new-vars-types (map (lambda (x) (hash-ref htable x #f) ) new-vars)]
              [erased-htable (foldl (lambda (index htable) (hash-remove htable index)) htable new-vars)]
              [erased-type-state (state-typercd-set unified-state erased-htable)]
              ;;; TODO: check-as-inf-type-disj might have corner 
              ;;;   case where first element is null
              [check-as-inf-type-disj*-c 
                (lambda (type?* t st) (if (and type?* st) (check-as-inf-type-disj type?* t st) st))]
              [checked-type-state (foldl check-as-inf-type-disj*-c
                                         erased-type-state 
                                         new-vars-types new-vars)]
              [after-ineq-check-st (and checked-type-state
                                        (inequality-recheck checked-type-state))]
              [_ (assert ((or/c false/c canonicalized-state?) after-ineq-check-st))])
        ;;;  TODO: short-circuit the possible #f appearing inside foldl
        (wrap-state-stream after-ineq-check-st))
  
  )))


(define/contract (unify/st u v)
  (any? any? . -> . (WithBackgroundOf? ?canonicalized-state?))
  ;;; inequality-recheck :: state -> state
  (define/contract (inequality-recheck conj-disj-pair)
    (list? . -> . (WithBackgroundOf? ?canonicalized-state?))
    (for/fold 
      ([acc       (pure-st #f)])
      ([each-disj-list conj-disj-pair])
        ((neg-unify*/state each-disj) . >> . acc)))

  (define/contract (typecst-recheck var-type-pair)
    (list? . -> . (WithBackgroundOf? ?canonicalized-state?))
    (for/fold 
      ([acc (pure-st '())])
      ([each var-type-pair])
      (match-let* 
        ([(cons v cst) each])
        ((if (set? cst)
             (do [<-end (check-as-inf-type-disj/state v cst)])
             (pure-st '())) 
         . >> . acc))))
  (do 
    [old-st     <- get-st]
    [old-htable = (state-typercd old-st)]
    [old-ineq   = (state-diseq old-st)]
    [old-sub    = (state-sub old-st)]
    [new-sub    = (unify/sub u v old-sub)]
    ;;; [extra-sub  = (extract-new new-sub old-sub)]
    ;;; [new-vars      = (map car new-subst)]
    ;;;   above are for incremental information
    [all-type-csts = (hash->list old-htable)]
    [rechecking-st = 
        (state-sub-set
          (state-typercd-set 
            (state-diseq-set old-st '()) (hash)) new-sub)]\
    [_ <- (set-st rechecking-st)]
    ;;; TODO: Incrementally recheck state information
    [_ <- (typecst-recheck related-type-csts)]
    [_ <- (inequality-recheck unified-st-ineq)]
    [<-return '()]
  ))

;; Reification
(define (walk* tm sub)
  (let ((tm (walk tm sub)))
    (if (pair? tm)
        `(,(walk* (car tm) sub) .  ,(walk* (cdr tm) sub))
        tm)))

(define/contract (walk*/st tm)
  (any . -> . (WithBackgroundOf? state?))
  (do 
    [st  <- get-st]
    [sub =  (state-sub st)]
    [tm  =  (walk tm sub)]
    [<-return 
      (if (pair? tm)
          `(,(walk* (car tm) sub) .  ,(walk* (cdr tm) sub))
          tm)]))

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

;;; TODO: make constraint information printed, just for debugging purpose
;;;       make it an option

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
  ;;; (debug-dump "\n reify with state: ~a" st)
  (reify initial-var st))

;;; reify the variable toggether with the constraints
;;; 
(define (reify/initial-var/csts st)
  (reify/initial-var st)
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
(define/contract (neg-unify u v st)
  (any? any? state? . -> . Stream?)
  (let* ([result (neg-unify* (list `(,u . ,v)) st)])
    (and result (cons result #f)))
)

;;; neg-unify* : given a list of pairs, indicating 
;;;   disjunction of inequality, solve them according to the current state
;;;   return a state that satisifies the disjunction of inequalities
(define (neg-unify* list-u-v st)
  ((list/c pair?) state? . -> . (or/c false/c canonicalized-state?))
  (match list-u-v 
    ['() #f]
    [(cons (cons u v) rest) 
        (let* (
          [subst (state-sub st)]
          ;;; [old-type-info (state-typercd st)]
          [unification-info-single-stream (unify u v st)]
          [unification-info-st 
            (and unification-info-single-stream 
                 (car unification-info-single-stream))]
          [unification-info 
            (and unification-info-st 
                 (state-sub unification-info-st))]
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

;;; neg-unify* : given a list of pairs, indicating 
;;;   disjunction of inequality, solve them according to the current state
;;;   return a state that satisifies the disjunction of inequalities
(define (neg-unify*/st list-u-v)
  ((list/c pair?) . -> . (WithBackgroundOf? ?canonicalized-state?))
  (match list-u-v 
    ['() failed-current-st]
    [(cons (cons u v) rest) 
        (do 
          [old-st <- get-st]
          ;;; run with nested do
          ;;;     because this do is a composition of maybe and state
          ;;;     so we can avoid 
          [(cons _ newly-added) =
            (run-st old-st
              (do [_ <- (unify/st u v)]
                  [new-st  <- get-st]
                  [old-sub = (state-sub old-st)]
                  [new-sub = (state-sub new-st)]
                  [<-return (extract-new new-sub old-sub)]))]
          [<-end 
            (match newly-added
              ;;; 1. if unification fails, then inequality is just satisfied 
              ;;;     st is directly returned
              [#f   (pure-st '())]
              ;;; 2. if unification succeeded, this mean the current state cannot
              ;;;     satisifies the inequality, let's consider the next possible-inequality
              ['()  (neg-unify*/st rest)]
              ;;; 3. if unification succeeded with extra condition
              ;;;     that means inequality should succeed with extra condition
              ;;;     we lazily put these things together and store into state
              [(cons _ _) 
                  (set-st 
                    (state-diseq-update old-st 
                      (lambda (x) (cons (append newly-added rest) x))))
                ])])]))


(define (state-sub-update-nofalse st f)
  (define st- (state-sub-update st f))
  (and (state-sub st-) st-)
)

(define singleton-type-map
  (hash
    true? #t
    false? #f
    null? '()
  )
)


;;; ;;; To check singleton-type or not
;;; (define (is-singleton-type x) 
;;;   (define k (hash-ref singleton-type-map x 'False)) 
;;;   (if (equal? k 'False) #f #t)
;;;   )
;;; (define (not-singleton-type x) (not (is-singleton-type x)))

;;; check-as-inf-type-disj: set[inf-type-predicate] x term x state -> state
;;;  currently it will use predicate as marker
;;;  precondition: type?* is never #f, st is never #f
;;;   precondition: type?* \subseteq all-inf-type-label
(define/contract (check-as-inf-type-disj type?* t st)
  (set? any? (or/c false/c canonicalized-state?) . -> . (or/c false/c canonicalized-state?))
  (assert-or-warn (subset? type?* all-inf-type-label) 
    "check-as-inf-type-disj cannot handle these type constraints ~a" type?*)
  ;;; TODO: fixing the case when type?* is actually empty
  ;;;     if it is empty, then we state that t is of finite type
  ;;; (assert-or-warn (not (set-empty? type?*) ) 
  ;;;   "check-as-inf-type-disj cannot handle when type?* is empty")
  
  (define inf-type?* type?* )

  (define infinite-type-checked-state ;;; type : state
    (and 
      st 
      (not (set-empty? inf-type?*))
      ;;; TODO: fixing the case when type?* is actually empty
      ;;;     if it is empty, then we state that t is of finite type
      (match (walk* t (state-sub st))
          ;;; BUGFIX: here we have tp-var as well!!
          [(var name index) 
            ;;; check if there is already typercd for index on symbol
            (let* ([v (var name index)]
                   [htable (state-typercd st)]
                   [type-info (hash-ref htable v 'False)])
              (if (not (equal? type-info 'False))
                ;;; type-info is a set of predicates
                ;;;  disjunction of type is conflicting
                (let* ([intersected (set-intersect type-info inf-type?*)])
                ;;;  TODO: when intersected result is actually just pair?, 
                ;;;    we need to make a substitution

                ;;; if it is empty list then we failed
                  (match intersected
                    [(? set-empty?) #f]
                    ;; this part is very weird... as we can see most fresh is not really existential
                    ;;;   quantifier because they don't specify scope!!
                    ;;;  here it is even more complicated ... what is the scope of a b?
                    ;;;    if we don't know the scope, will it cause problem when generating trace?
                    [(? (λ (the-set) (equal? the-set (set pair?))))
                      (let* ([t1 (var/fresh 't1)]
                             [t2 (var/fresh 't2)]
                             [st-unify-updated 
                                    (state-sub-update-nofalse st 
                                      (lambda (sub) (unify/sub t (cons t1 t2) sub)))]
                             [st-tyrcd-updated
                                    (state-typercd-update st-unify-updated (lambda (tyrcd) (hash-remove tyrcd t))) ]
                             )
                        ;;; TODO: recheck this part 
                        ;;; 1. these two new vars have no good scope info *
                        ;;; 2. unify/sub doesn't seem to do more checking? ** 
                        ;;; 3. then we remove type information
                        st-tyrcd-updated) ]  
                    [_   (state-typercd-update st (lambda (x) (hash-set x v intersected)))]
                    )
                  
                )
                (state-typercd-update st (lambda (x) (hash-set x v type?*)))) ) ]

          [v (and (ormap (lambda (x?) (x? v)) (set->list inf-type?*)) st)]) ))
    ;;; return the following
    infinite-type-checked-state
)

;;; check-as-inf-type :: inf-type-label  x term x (state or #f) -> (state or #f)
;;;  precondition: type? \in all-inf-type-label 
;;;  if type-label = #f, then we will just return st
(define/contract (check-as-inf-type type? t st) 
  (any? any? ?state? . -> . ?state?)
  (if (and type? st)
    (check-as-inf-type-disj (set type?) t st)
    st)
)
