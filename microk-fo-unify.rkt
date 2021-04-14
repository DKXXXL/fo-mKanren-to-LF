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



(define (any? _) #t)
;;; (define type-label-top (set true? false? null? pair? number? string? symbol?))
(define all-inf-type-label (set pair? number? string? symbol?))






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
                          ;;; (invariant-assertion 
                          ;;;   (bgT? . -> . (cons/c bgT? any?)) 
                          ;;;   bgf)
                          bgf
                            )]
                      [else (error type-name
                                   "Should be a hashmap")]))
;;; #:prefab
)


;;; (define (WithBackgroundOf? u?) 
;;;   (λ (k)
;;;     (and (WithBackground? k) (equal? u? (WithBackground-bgType k)))) )


(define (WithBackgroundOf? u?) 
  WithBackground?)

(define (=== k) (λ (x) (equal? x k)))

;;; dbginfo
(define/contract (>>= fwb domap dbginfo)
  (WithBackground? (any? . -> . WithBackground?) any? . -> . WithBackground?)
  (WithBackground
    (WithBackground-bgType fwb)
    (let*
      ([isNone? (λ (t) (equal? t #f))] ;; BUGFIX: adopt to generic later
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


;;; (define-syntax do
;;;   (syntax-rules (<- <-end <-return =)
;;;     ((_ [ x = y ] sth ...) 
;;;       (match-let ([x y]) (do sth ...)))
;;;     ((_ [ x <- y ] sth ...) 
;;;       (let* ([_ (assert-or-warn (WithBackground? y) "Type Error at :~s\n" #'y)])
;;;          (>>= y (match-lambda [x (do sth ...)]) #'y)) ) 
;;;     ((_ [ <-end y ]) 
;;;       (let* ([_ (assert-or-warn (WithBackground? y) "Type Error at :~s\n" #'y)]) 
;;;         y))
;;;     ((_ [ <-return y ]) 
;;;       (pure-st y))
;;;   ))

(define (?canonicalized-state? t) (λ (t) (or/c false/c canonicalized-state?)))



(define-syntax do
  (syntax-rules ()
    ((_ k ...) 
      (do/type ?canonicalized-state? k ...))

  ))

(define-syntax do/type
  (syntax-rules ()
    ((_ type-predicate k ...) 
      (WithBackground type-predicate
        (λ (bg)
          (do-on bg type-predicate k ...))))
  ))

(define-syntax do-on
  (syntax-rules (<- <-end <-return =)
    ((_ bg type? [ x = y ] sth ...) 
      (match-let ([x y]) (do-on bg type? sth ...)))
    ((_ bg type? [ x <- y ] sth ...) 
      (match-let* 
            ([_           (assert-or-warn (WithBackground? y) "Type Error at :~s\n" #'y)]
             [wbƛ         (WithBackground-bg->front y)]
             [wbguard     (WithBackground-bgType    y)]
             [(cons bg2 x) (wbƛ bg)]
             [isNone?     (λ (t) (not t))]
             [_           (assert-or-warn ((and/c wbguard type?) bg2) "Background Type Error at :~s\n" #'y)])
           (if (isNone? bg2)
             (cons bg2 #f)  ;; short circuiting.
             (do-on bg2 wbguard sth ...)) )) 
    ((_ bg type? [ <-end y ]) 
      (do-on bg type? [ y_ <- y ] [ <-return y_]))
    ((_ bg type? [ <-return y ]) 
      (cons bg y))
  ))

(define WB WithBackground)

;;; can we multi-stage it? I mean partially evaluate monadic style
;;; change the following into macro
(define (get ty) (WB ty (λ (bg) (cons bg bg))))
(define (sets ty) (λ (term) (WB ty (λ (_) (cons term '())))))
(define (pure ty) (λ (term) (WB ty (λ (bg) (cons bg  term)))) )
(define (run ty)  
  (invariant-assertion
    (ty (WithBackgroundOf? (=== ty)) . -> . (cons/c ty any?))
    (λ (st wb)
    (match-let* 
      ([(WithBackground ty? bg->front) wb]
       [_ (assert-or-warn (ty? st) "Wrong WithBackground Invocation\n")])
      (bg->front st))))
  )
(define (modify ty)
  (λ (f)
    (do [st <- get-st]
        [_  <- (set-st (f st))]
        [<-return '()])))




(define get-st  (get (or/c false/c state?)))
(define set-st  (sets (or/c false/c state?)))
(define pure-st (pure (or/c false/c state?)))
(define run-st  (run (or/c false/c state?)))
(define modify-st (modify (or/c false/c state?)))
(define failed-current-st
  (do 
    [_ <- (set-st #f)]
    [k <- get-st]
    [_ = (printf "after failing... : ~a" k)]
    [<-return #f]
  ) 
)




;;; Will totally ignore tproj (doing nothing on them)
(define (walk t sub)
  ;;; (debug-dump "walk: ~a with ~a \n" t sub)
  (match t
    [(? (or/c var? tproj?)) 
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
  (state-scope-set
    (state-sub-set (canonicalize st-without-sub-and-scope current-sub) current-sub)
    current-scope
    ))

;;; return element
(define/contract (canonicalize x current-sub)
  (any? list? . -> . any?)

  (define (each-case rec-parent rec g)
    (match g
      [(var _ _) (walk* g current-sub)] 
      [o/w (rec-parent g)]))
  (define result-f 
    (compose-maps (list each-case goal-term-base-map pair-base-map state-base-endo-functor hash-key-value-map identity-endo-functor)))
  (result-f x)  
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



(define/contract (wrap-state-stream st)
  ((or/c false/c state?) . -> . (or/c false/c Stream?))
  (and st (cons st #f)))

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
  (wrap-state-stream
    (car (run-st st (unify/st u v))))
)


(define/contract (unify/st u v)
  (any? any? . -> . (WithBackgroundOf? ?canonicalized-state?))
  ;;; inequality-recheck :: state -> state
  (define/contract (inequality-recheck conj-disj-pair)
    (list? . -> . (WithBackgroundOf? ?canonicalized-state?))
    (for/fold 
      ([acc       (pure-st #f)])
      ([each-disj-list conj-disj-pair])
        ((neg-unify*/st each-disj-list) . >> . acc)))

  (define/contract (typecst-recheck var-type-pair)
    (list? . -> . (WithBackgroundOf? ?canonicalized-state?))
    (for/fold 
      ([acc (pure-st '())])
      ([each var-type-pair])
      (match-let* 
        ([(cons v cst) each])
        ((if (set? cst)
             (do [<-end (check-as-inf-type-disj/st cst v)])
             (pure-st '())) 
         . >> . acc))))
  (do 
    [old-st     <- get-st]
    [old-htable = (state-typercd old-st)]
    [old-ineq   = (state-diseq old-st)]
    [old-sub    = (state-sub old-st)]
    [new-sub    = (unify/sub u v old-sub)]
    [_          <- (if new-sub (pure-st '()) failed-current-st)]
    
    [_          <- (pure-st '())] ;; a mysterious bug will appear if remove this line
    ;;; [extra-var  = (map car (extract-new new-sub old-sub))]
    ;;; [new-vars      = (map car new-subst)]
    ;;;   above are for incremental information
    [all-type-csts = (hash->list old-htable)]
    ;;; [new-type-csts = 
    ;;;   (map (λ (t) (cons t (hash-ref old-htable t #f))) extra-var)]
    ;;; [related-type-csts =
    ;;;   (filter (λ (t) (cdr t)) new-type-csts)]
    ;;; [erased-htable     =
    ;;;   (foldl (λ (index htable) (hash-remove htable index)) old-htable extra-var)]
    [rechecking-st = 
        (state-sub-set
          (state-typercd-set 
            (state-diseq-set old-st '()) (hash)) new-sub)]
    [_ <- (set-st rechecking-st)]
    ;;; TODO: Incrementally recheck state information
    [_ <- (typecst-recheck all-type-csts)]
    [_ <- (inequality-recheck old-ineq)]
    [<-return '()]
  ))

;; Reification
(define/contract (walk* tm sub)
  (any? list? . -> . any?)
  (let ((tm (walk tm sub)))
    (if (pair? tm)
        `(,(walk* (car tm) sub) .  ,(walk* (cdr tm) sub))
        tm)))

(define/contract (walk*/st tm)
  (any/c . -> . (WithBackgroundOf? state?))
  (do 
    [st  <- get-st]
    [sub =  (state-sub st)]
    [tm  =  (walk* tm sub)]
    [<-return tm]))

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
  (any? any? canonicalized-state? . -> . Stream?)
  (let* ([result (neg-unify* (list `(,u . ,v)) st)])
    (and result (cons result #f)))
)

;;; neg-unify* : given a list of pairs, indicating 
;;;   disjunction of inequality, solve them according to the current state
;;;   return a state that satisifies the disjunction of inequalities
(define (neg-unify* list-u-v st)
  ((list/c pair?) state? . -> . (or/c false/c canonicalized-state?))
  (car (run-st st (neg-unify*/st list-u-v)))
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
          [(cons _ newly-added-uncanonical) =
            (run-st old-st
              (do [_ <- (unify/st u v)]
                  [new-st  <- get-st]
                  [old-sub = (state-sub old-st)]
                  [new-sub = (state-sub new-st)]
                  [<-return (extract-new new-sub old-sub)]))]
          [newly-added = (canonicalize newly-added-uncanonical (state-sub old-st))]
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
                      (lambda (x) (cons (append newly-added rest) x))))])])]))


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
  (car (run-st st (check-as-inf-type-disj/st type?* t))))


;;; check-as-inf-type-disj: set[inf-type-predicate] x term x state -> state
;;;  currently it will use predicate as marker
;;;  precondition: type?* is never #f, st is never #f
;;;   precondition: type?* \subseteq all-inf-type-label
(define/contract (check-as-inf-type-disj/st type?* t_)
  (set? any? . -> . (WithBackgroundOf? (or/c false/c canonicalized-state?)))
  (assert-or-warn (subset? type?* all-inf-type-label) 
    "check-as-inf-type-disj cannot handle these type constraints ~a" type?*)
  ;;; TODO: fixing the case when type?* is actually empty
  ;;;     if it is empty, then we state that t is of finite type
  ;;; (assert-or-warn (not (set-empty? type?*) ) 
  ;;;   "check-as-inf-type-disj cannot handle when type?* is empty")
  
  (define inf-type?* type?*)
  (do 
    [_ <- (if (set-empty? inf-type?*) failed-current-st (pure-st '()))]
    [t <- (walk*/st t_)]
    [<-end 
      (match t
        [(? var?)
            (do [st       <- get-st]
                [htable            = (state-typercd st)]
                [before-type-info  = (hash-ref htable t all-inf-type-label)]
                [intersected-types = (set-intersect before-type-info inf-type?*)]
                [<-end 
                  (cond
                    [(set-empty? intersected-types)   
                        failed-current-st]
                    [(equal? (set pair?) intersected-types)
                        (do [t1 = (var/fresh 't1)]
                            [t2 = (var/fresh 't2)]
                            [current-st <- get-st]
                            [_ <- (set-st
                                    (state-typercd-update current-st 
                                      (λ (htable) (hash-remove htable t))))]
                            [<-end (unify/st t (cons t1 t2))])]
                    [#t 
                        (set-st
                          (state-typercd-update st 
                            (λ (x) (hash-set x t intersected-types))))])])]
        [v 
          (do 
            [st <- get-st]
            [new-st = (and (ormap (lambda (x?) (x? v)) (set->list inf-type?*)) st)]
            [<-end  (if new-st (set-st new-st) failed-current-st)])])]))


;;; check-as-inf-type :: inf-type-label  x term x (state or #f) -> (state or #f)
;;;  precondition: type? \in all-inf-type-label 
;;;  if type-label = #f, then we will just return st
(define/contract (check-as-inf-type type? t st) 
  (any? any? ?state? . -> . ?state?)
  (if (and type? st)
    (check-as-inf-type-disj (set type?) t st)
    st)
)
