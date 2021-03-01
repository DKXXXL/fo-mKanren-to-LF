#lang racket
(provide
  (struct-out var)
  initial-var
  
  (struct-out state)
  (struct-out state-type)
  (struct-out failed-state)
  pair-of?

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
  unify/state
  unify/sub
  walk*
  term?
  reify
  reify/initial-var
  neg-unify
  neg-unify/state
  wrap-state-stream
  check-as-inf-type-disj
  check-as-inf-type-disj/state
  ;;; check-as-inf-type

  do
  run-st
  get-st
  set-st
  pure-st
  modify-st
  failed-current-st
  add-to-sta
  add-to-tha
  query-stj
  query-thj

  any?
  ?state?
  debug-dump-w/level
  debug-dump
  raise-and-warn
  assert-or-warn
  assert
  valid-type-constraints-check
  <-pfg
  push-lflet
  )

;;; bear with it now.... let me search if there is
;;;  extensible record later

(require struct-update)
(require racket/contract)
(require errortrace)
(require "proof-term.rkt")
(require "mk-fo-def.rkt")

(instrumenting-enabled #t)




;;; (define var/fresh
;;;   (let ((index 0))
;;;     (lambda (name) (set! index (+ 1 index))
;;;       (var name index))
;;;       ))

;; States
(define initial-var (var #f 0))
(define empty-sub '())

(define (equation? x) (pair? x))

;;; Now it should support tproj term subject to substitution
(define (walk t sub)
  (match t
    [(var _ _) 
      (let ((xt (assf (lambda (x) (equal? t x)) sub)))
        (if xt (walk (cdr xt) sub) t))]
    [(tproj v (cons cxr rest))
      #:when (member cxr '(car cdr))
      (let ([xt (assf (lambda (x) (equal? t x)) sub)]
            [tcxr (match cxr 
                    ['car tcar] 
                    ['cdr tcdr] 
                    [o/w (raise-and-warn "Unexpected projection ~a" t)])]
            )
        (if xt 
          (walk (cdr xt) sub) 
          (tcxr (walk (tproj_ v rest) sub))))]
    [_ t]
  )
)



;;; monadic style
(define/contract (walk/state t)
  (any? . -> . (WithBackgroundOf? (=== state-type?)))
  ;;; any? . -> . (pair-of? )
  (match t
    [(var _ _) 
      (do
        [st          <- get-st]
        [sub         = (state-sub st)]
        [sta         = (state-type-sta st)]
        [stj         = (state-type-stj st)]
        [t=t1        = (assf (lambda (x) (equal? t x)) sub)]
        [<-end 
          (if t=t1
              (do 
                [t1   = (cdr t=t1)]
                [a:t=t1 = (pfmap-ref sta (== t t1))]
                [stj:t=t1 = (pfmap-ref stj (== t t1))]
                [a:t1=t = (LFeq-symm a:t=t1)]
                [stj:t1=t = (LFeq-symm stj:t=t1)]
                [(cons tend t:tend=t1) <- (walk/state t1)]
                [stj:tend=t1 <- (query-stj (== tend t1))]
                [a:tend=t   = (LFeq-trans stj:tend=t1 a:t1=t)]
                [stj:tend=t = (LFeq-trans stj:tend=t1 stj:t1=t)]
                [_ <- (add-to-stj (== tend t) stj:tend=t)]
                [<-return (cons tend a:tend=t)])
              (pure-st (cons t (LFeq-refl t))))])]
    ;;; currently no proof term for tproj
    ;;;  as it is part of internal of relative complements
    ;;;   maybe the better way to prove relative complements is to use 
    ;;;   proof elaboration
    [(tproj v (cons cxr rest))
      #:when (member cxr '(car cdr))
        (do 
          [st   <- get-st]
          [sub  = (state-sub st)]
          [xt   = (assf (lambda (x) (equal? t x)) sub)]
          [tcxr = (match cxr 
                      ['car tcar] 
                      ['cdr tcdr] 
                      [o/w (raise-and-warn "Unexpected projection ~a" t)])]
          [<-end 
            (if xt 
              (walk/state (cdr xt))
              (do 
                [(cons term pf) <- (walk/state (tproj_ v rest))]
                [<-return (cons (tcxr term) pf)]))])]
    [_ (pure-st (cons t (LFeq-refl t)))]
  )
)
;;; BUGFIX: might need to double check this
;;;    as we introduce a new type of 'substitutable' tproj
(define (occurs? x t sub)
  (cond ((pair? t) (or (occurs? x (walk (car t) sub) sub)
                       (occurs? x (walk (cdr t) sub) sub)))
        ((var? t)  (var=? x t))
        (else      #f)))

(define (extend-sub x t sub)
  (and (not (occurs? x t sub)) `((,x . ,t) . ,sub)))

(define (extend-sub/state x t)
  (any? any? . -> . (WithBackgroundOf? (=== state-type?)))
  (do 
    [st     <- get-st]
    [sub    = (state-sub st)]
    [sta    = (state-type-sta st)]
    [newsub = `((,x . ,t) . ,sub)]
    [newkey = (== x t)]
    [newsta = (fresh-param (term) 
                  (pfmap-set newkey term))]
    (<-end 
      (if (occurs? x t sub)
        (set-st (failed-state))
        (modify-st 
          (lambda (st) (state-type-sta-set 
                          (state-sub-set st newsub) newsta)))))
  )
)
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


;;; ;;; same as extend-sub, except the input has to be idempotent, 
;;; ;;;   and its output is also idempotent 
;;; (define (extend-idempotent-sub x t sub)
;;;   ;;; TODO: to implement in the future, currently just use the non-idempotent version
;;;   (extend-sub x t sub)
;;; )

;;; ;;; var x [(var . term)] -> [(var . term)]
;;; ;;;  precondition: subst is already idempotent, 
;;; ;;;   i.e. the range of subst doesn't intersect its domain 
;;; ;;;  specification: it will substitute just as subst, except for x, it won't change
;;; (define (shadow-idempotent-sub x subst)
;;;   (filter (lambda (pair) (not (equal? (car pair) x))) subst)
;;; )


(define (pair-of? x? y?)
  (lambda (t)
    (and (pair? t) (x? (car t)) (y? cdr t))))
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

(define WB WithBackground)

;;; can we multi-stage it? I mean partially evaluate monadic style
;;; change the following into macro
(define (get ty) (WB ty (λ (bg) (cons bg bg))))
(define (set ty) (λ (term) (WB ty (λ (_) (cons term '())))))
(define (pure ty) (λ (term) (WB ty (λ (bg) (cons bg  term)))) )
(define (run ty)  
  (λ(wb st)
    (match-let* 
      ([(WithBackground ty? bg->front) wb]
       [_ (assert-or-warn (ty? st) "Wrong WithBackground Invocation\n")])
      (bg->front st))))
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
    [st <- get-st]
    [to-bottom <- (query-stj (Bottom))]
    [st-pf-info = (struct-copy state-type st)]
    [failed-st  = 
      (failed-state 
        (state-type-sta st) 
        (state-type-stj st)
        (state-type-tha st)
        (state-type-thj st)
        to-bottom)]
    [_ <- (set-st failed-st)]
    [<-return #f]
  ) 
)

;;; 
(define/contract (>>= fwb domap)
  (WithBackground? (any? . -> . WithBackground?) . -> . WithBackground?)
  (WithBackground
    (let*
      ([isNone? failed-state?] ;; BUGFIX: adopt to generic later
       [fwbdo (WithBackground-bg->front fwb)])
        (λ (bg)
            (if (isNone? bg)
              (cons bg #f)
              (match-let* 
                  ([(cons bg1 fr1) (fwbdo bg)]
                  [(WithBackground _ swbdo) (domap fr1)]
                  [bg2+fr2 (swbdo bg1)])
                bg2+fr2))))))

(define (>> a b) (>>= a (λ (_) b)))

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

(define-syntax do
  (syntax-rules (<- <-end <-return =)
    ((_ [ x = y ] sth ...) 
      (match-let ([x y]) (do sth ...)))
    ((_ [ x <- y ] sth ...) 
      (>>= y (match-lambda [x (do sth ...)])))
    ((_ [ <-end y ]) 
      y)
    ((_ [ <-return y ]) 
      (pure-st y))
  ))


;;; TODO: if all of the elements in type set are for the finite, 
;;;   then inequality might cause trouble  
;;;   for example, (exists x y z.) they are all different, they are all booleans

(define empty-pfmap (hash))
(define pfmap-ref hash-ref)
(define pfmap-set hash-set)



(define (query-x key x-getter)
  (do [st <- get-st]
      [<-return (pfmap-ref (x-getter st) key)]))

(define (add-to-x x-updator typekey t)
    (do [st <- get-st]
        [new-st = (x-updator st (λ (h) (pfmap-set h typekey t)))]
        [<-return t]))

(define (query-sta key) (query-x key state-type-sta))
(define (query-stj key) (query-x key state-type-stj))
(define (query-tha key) (query-x key state-type-tha))
(define (query-thj key) (query-x key state-type-thj))

(define (add-to-sta typekey t) (add-to-x state-type-sta-update typekey t))
(define (add-to-stj typekey t) (add-to-x state-type-stj-update typekey t))
(define (add-to-tha typekey t) (add-to-x state-type-tha-update typekey t))
(define (add-to-thj typekey t) (add-to-x state-type-thj-update typekey t))

(define (type-info-query v unfound)
  (do 
    [st <- get-st]
    [typercd = (state-typercd st)]
    [<-return (hash-ref typercd v unfound)]))

(define (type-info-set k v)
  (do 
    [st <- get-st]
    [typercd = (state-typercd st)]
    [new-st  = (hash-set typercd k v)]
    [_       <- (set-st new-st)]
    [<-return '()]))

;;; sub -- list of substution 
;;; diseq -- list of list of subsitution 
;;;     -- interpreted as conjunction of disjunction of inequality 
;;; assymbol/asstring/asnumber are all a list of variables
;;;   to indicate disjoint sets
;;;   typercd : a dictionary index -> set of type-encoding 
;;;     "as disjunction of possible types"
;;; stj : the proof term of state type, using tha
;;; sta : the assumption of state type
;;; thj : the proof term of the goals been through, using sta
;;; tha : the assumption of (through-goal) type
;;; invariant key(stj) == key(sta), key(thj) \supseteq key(tha)
(struct state-type (sta stj tha thj) #:prefab)
(struct failed-state (bot-from-tha) #:prefab) ;; indicating bottom type
(struct state (sub scope pfterm diseq typercd) #:prefab)
(define empty-state (state empty-sub (list initial-var) single-hole '() (hash)))
(define-struct-updaters state)
(define-struct-updaters state-type)
(define-struct-updaters failed-state)

;;; lift <-pf/h-inc into state
(define-syntax <-pfg
  (syntax-rules ()
    ((_ st term) 
      (and st
           (state-pfterm-update st 
              (lambda (pft) (pft . <-pf/h-inc . term)))) )     

    ((_ st (hole holes ...) body) 
      (and st
           (state-pfterm-update st 
              (lambda (pft) (pft . <-pf/h-inc . (hole holes ...) body)))) )
  ))

(define (WithBackgroundOf? u?) 
  (λ (k)
    (and (WithBackground? k) (u? (WithBackground-bgType k)))))


(define (=== k) (λ (x) (equal? x k)))
;;; ;;; TODO: uncomment above
;;; (define-syntax <-pfg
;;;   (syntax-rules ()
;;;     ((_ st term) 
;;;       (let ([st_ st]) st_) )     

;;;     ((_ st (hole holes ...) body) 
;;;       (let ([st_ st]) st_) )
;;;   ))

;;; ANF-style push-let
(define-syntax push-lflet
  (syntax-rules (:)
    ((_ st term : Type) 
      (fresh-param (new)
        (let
          ([new-st (st . <-pfg . (_) (lf-let* ([new term : Type]) _))])
          `(,new-st . ,new))))))

;;; we consider #f is the failed state, also one of the state
(define (?state? obj) (or (equal? obj #f) (state? obj)))

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

;;; better composition syntax
(define-syntax ○
  (syntax-rules ()
    [(_ t) t]
    [(_ x y ...) (x . compose . (○ y ...))] ;; x ○ y ○ ... 
  ))

(define-syntax compose
  (syntax-rules ()
    [(_ a b) (λ (t) (a (b t)))]))

;;; returning state, t:u=v proof-term together
;;; note the invariant
;;;   precondition: tha is already maintained its invariance
;;;   tha is controlled by the outer goal
;;;   the reason is that, for example, (== (cons x y) (cons z c))
;;;     then we should only have "(== (cons x y) (cons z c))" inside tha
;;;     without any of the term (== x z) and (== y c)
;;;     because specification is that tha is all the goal it been through
;;; the generated u=v pf term only uses sta as assumption
(define/contract (unify/st/proof u v a:u=v)
  (any? any? proof-term? . -> . (WithBackgroundOf? (=== state-type?)))
  (do 
    [(cons u0 t:u0=u) <- (walk/state u)]
    [(cons v0 t:v0=v) <- (walk/state v)]
    ;;; [a:u=v <- (fresh-param (eqt) (add-to-tha (== u v) eqt))]
    ;;; add u=v into tha
    [t:u0=v0->t:u=v =
      (λ (t:u0=v0)
        (let* ([t:u=u0 (LFeq-symm t:u0=u)]
               [t:u=v0 (LFeq-trans t:u=u0 t:u0=v0)]
               [t:u=v  (LFeq-trans t:u=v0 t:v0=v)])
          t:u=v))] ;; construct a lambda that construct u=v using a:u0=v0
    [t:u=v->t:u0=v0 =
      (λ (t:u=v)
        (let* ([t:v=v0 (LFeq-symm t:v0=v)]
               [t:u=v0 (LFeq-trans t:u=v t:v=v0)]
               [t:u0=v0  (LFeq-trans t:u0=u t:u=v0)])
          t:u0=v0))] ;; construct a lambda that construct u=v using a:u0=v0
    (<-end 
      (cond 
        [(and (var? u0) 
              (var? v0) 
              (var=? u0 v0))  
            ;;; no sta has been added, thus sta, stj won't change
            ;;; but u=v will be added to thj
            (do 
              [t:u=v    = (t:u0=v0->t:u=v (LFeq-refl u0))]
              [t:u0=v0  = (LFeq-refl u0)]
              [_ <- (add-to-stj (== u0 v0) t:u0=v0)]
              [_ <- (add-to-thj (== u v)   t:u=v)]
              [<-return t:u=v]
              )]
        [(var? u0) 
            ;;; (u0 == v0) has been added to sta, stj 
            ;;; and u=v will be added to thj            
            (do
              [_ <- (extend-sub/state u0 v0)] ;; now we have u0=v0 inside assumption
              [st  <- get-st]
              [newsta = (state-type-sta st)]
              [a:u0=v0 = (pfmap-ref newsta (== u0 v0))]
              [t:u=v   = (t:u0=v0->t:u=v a:u0=v0)]
              [t:u0=v0 = (t:u=v->t:u0=v0 a:u=v)]
              [_ <- (add-to-stj (== u0 v0) t:u0=v0)]
              [_ <- (add-to-thj (== u v)   t:u=v)]
              [<-return t:u=v])]
        [(var? v0)     
            ;;; (v0 == u0) has been added to sta, stj 
            ;;; and u=v will be added to thj        
            (do
              [_ <- (extend-sub/state v0 u0)] ;; now we have u0=v0 inside assumption
              [st  <- get-st]
              [newsta = (state-type-sta st)]
              [a:v0=u0 = (pfmap-ref newsta (== v0 u0))]
              [a:u0=v0 = (LFeq-symm a:v0=u0)]
              [t:u=v   = (t:u0=v0->t:u=v a:u0=v0)]
              [t:u0=v0 = (t:u=v->t:u0=v0 a:u=v)]
              [t:v0=u0 = (LFeq-symm t:u0=v0)]
              [_ <- (add-to-stj (== v0 u0) t:v0=u0)]
              [_ <- (add-to-thj (== u v)   t:u=v)]
              [<-return t:u=v])]
        [(and (pair? u0) 
              (pair? v0))  
              ;;; sta, stj unchanged
              ;;; adding u=v into thj
            (do 
              [(cons u01 u02) = u0]
              [(cons v01 v02) = v0]
              [a:u0=v0 = (t:u=v->t:u0=v0 a:u=v)]
              [a:u01=v01+a:u02=v02 = (LFeq-pis a:u0=v0)]
              [t:u01=v01 <- (unify/st/proof u01 v01 (LFpair-pi-1 a:u01=v01+a:u02=v02))]
              [t:u02=v02 <- (unify/st/proof u02 v02 (LFpair-pi-2 a:u01=v01+a:u02=v02))]
              [t:u0=v0   =  (LFeq-pair t:u01=v01 t:u02=v02)] ;; construct equality using
              [t:u=v     =  (t:u0=v0->t:u=v t:u0=v0)]
              [_ <- (add-to-thj t:u=v)]
              [<-return t:u=v])]
        [(eqv? u0 v0) 
            ;;; only add thj
            (do
              [t:u=v = (t:u0=v0->t:u=v (LFeq-refl u0))]
              [_ <- (add-to-thj (== u v) t:u=v)]
              [<-return t:u=v])] ;; the proof is trivially LFrefl
        [#t 
        ;;;   we will have u=v inside tha, thj
        ;;;     u0=v0 inside sta, stj
        ;;;   we will also have a bottom inside stj, but not bottom in thj
            (do
              [tha:u=v     =  a:u=v]
              [sta:u0=v0   <- (fresh-param (term) (add-to-tha (== u0 v0) term))]
              ;;; add to thj
              [thj:u=v     <- (t:u0=v0->t:u=v sta:u0=v0)]
              [stj:u0=v0   <- (t:u=v->t:u0=v0 tha:u=v)]
              [to-bottom   =  (LFassert ((== u0 v0) . impl . (Bottom)))]
              ;;; add bottom to thj
              ;;; [_          <- (add-to-thj (Bottom) (LFapply to-bottom sta:u0=v0))]
              ;;; add bottom to stj
              [_          <- (add-to-stj (Bottom) (LFapply to-bottom stj:u0=v0))]
              ;;; get into failed-state
              [_ <- (set-st (failed-state))]
              [<-return '()]
            )] 
        ;; unification failed. we return bottom state
        ;;; here in the future we will also need to justifies using axiom 
      )
    
    )
  )

)

;;; (define (unify u v st)
;;;   (let ((sub (unify/sub u v (state-sub st))))
;;;     (and sub (cons (state sub (state-trace st)) #f))))

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


(define/contract (unify/state u v a:u=v)
  (any? any? proof-term? . -> . (WithBackgroundOf? (=== state-type?)))
  (define/contract (inequality-recheck conj-disj-pair)
    (list? . -> . (WithBackgroundOf? (=== state-type?)))
    (for/fold 
      ([acc       (pure-st #f)])
      ([each-disj conj-disj-pair])
      ((neg-unify*/state each-disj) . >> . acc)
    ))
  

  (define/contract (typecst-recheck var-type-pair)
    (list? . -> . (WithBackgroundOf? (=== state-type?)))
    (for/fold 
      ([acc (pure-st '())])
      ([each var-type-pair])
      (match-let* 
        ([(cons v cst) each])
        ((if (set? cst)
             (check-as-inf-type-disj/state v cst)
             (pure-st '())) 
         . >> . acc))))

  (do
    [old-st     <- get-st]
    [t:u=v         <- (unify/st/proof u v a:u=v)]
    [unified-st <- get-st]
    [unified-st-typecst = (state-typercd unified-st)]
    [unified-st-ineq    = (state-diseq  unified-st)]
    [rechecking-st      = (state-typercd (state-diseq-set unified-st '()) (hash))]
    [_ <- (set-st rechecking-st)]
    ;;; now we need to recheck 
    ;;;     all the inequalities and 
    ;;;     all the type-cst
    ;;;     about the new vars
    [new-subst     = (extract-new (state-sub unified-st) (state-sub old-st))]
    [new-vars      = (map car new-subst)]
    ;;; get related type-cst from 
    [related-type-csts = 
      (map (λ (v) (cons v (hash-ref unified-st-typecst v 'UNFOUND))) new-vars)]
    ;;; TODO: remove those extracted type-cst (why?)
    [_ <- (typecst-recheck related-type-csts)]
    ;;; get all inequalities and re-check
    [_ <- (inequality-recheck unified-st-ineq)]
    [<-return t:u=v]
  )
)

(define/contract (unify u v st)
  (any? any? state? . -> . any?)
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
                                         )
        ;;;  TODO: short-circuit the possible #f appearing inside foldl

        (and checked-type-state
          (wrap-state-stream (inequality-recheck checked-type-state) )))
  
  )))

;; Reification
;;; (define/contract (walk* tm sub)
;;;   (any? list? . -> . any?)
;;;   (let ((tm (walk tm sub)))
;;;     (match tm
;;;       [(cons a b) (cons (walk* a sub) (walk* b sub))]
;;;       [(tproj x cxr) (tproj_ (walk x sub) cxr)]
;;;       [_ tm]
;;;     )))

;;; walk with struct respecting
;;;  will replace each var inside a structure with what sub points to
;;; (define/contract (walk-struct-once tm sub)
;;;   (any? list? . -> . any?)
;;;     (match tm
;;;       [(cons a b) (cons (walk-struct-once a sub) (walk-struct-once b sub))]
;;;       [(tproj x cxr) (walk tm sub)]
;;;       [(var _ _) (walk tm sub)]
;;;       [_ tm]
;;;     ))

;;; walk with struct respecting
;;;  will replace each var inside a structure with what sub points to
(define/contract (walk-struct-once tm sub)
  (any? list? . -> . any?)
    (match tm
      [(cons a b) (cons (walk-struct-once a sub) (walk-struct-once b sub))]
      [(tproj x cxr) (walk tm sub)]
      [(var _ _) (walk tm sub)]
      [_ tm]
    ))

;;; monadic style
(define/contract (walk-struct-once/state tm)
  (any? state? . -> . (WithBackgroundOf? (=== state-type?)))
    (match tm
      [(cons a b) 
        (do
          [(cons a0 t:a0=a) <- (walk-struct-once/state a)]
          [(cons b0 t:b0=b) <- (walk-struct-once/state b)]
          [eqt = (LFeq-pair t:a0=a t:b0=b)]
          [<-return (cons (cons a0 b0) eqt)])]
      [(tproj x cxr) (walk/state tm)]
      [(var _ _) (walk/state tm)]
      [_ (pure-st (cons tm (LFeq-refl tm)))]
    ))

;;; walk* -- walk-struct-once until fixpoint
;;;  unhalt only if there is cycle in sub
(define/contract (walk* tm sub)
  (any? list? . -> . any?)
  (let* ([tm- (walk-struct-once tm sub)]
        ;;;  [k (debug-dump "\n walk* ~a -> ~a" tm tm-)]
         )
    (if (equal? tm- tm) tm (walk* tm- sub))))

;;; monadic style
(define/contract (walk*/state tm)
  (any? state? . -> . (WithBackgroundOf? (=== state-type?)))
  (do [tm- <- (walk-struct-once/state tm)]
      (<-end 
        (if (equal? tm- tm)
          (pure-st tm)
          (walk*/state tm-)))))

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
  (debug-dump "\n reify with state: ~a" st)
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


(define (neg-unify/state u v a:u=/=v)
  (any? any? proof-term? . -> . (WithBackgroundOf? (=== state-type?)))
  (neg-unify*/state (list (cons u v)) a:u=/=v)
)

;;; monadic style
;;;   the second is a big disjunction
;;; precondition: (type a:Vu=/=v) is the disjunction of inequalities
(define (neg-unify*/state list-u-v a:Vu=/=v)
  (list? proof-term? . -> . (WithBackgroundOf? (=== state-type?)))
  (define all-disj-inequ-type 
    (for/fold
      ([acc-goal (Bottom)])
      ([each-u-v-pair list-u-v])
      (match-let* 
        ([(cons u v) each-u-v-pair])
        (disj (=/= u v) acc-goal))))
  (match list-u-v
    ['() #f]
    [(cons (cons u v) rest)
      (do 
        [old-st <- get-st]
        [a:u=v  =  (fresh-param (t) t)]
        [(cons new-st t:u=v) = (run-st (unify/state u v a:u=v) old-st)]
        [newly-added         = (extract-new (state-sub new-st) (state-sub old-st))]
        [<-end 
          (match newly-added
            [#f  
                ;;; u=/=v is satisfied in new-st (a failed state),
                ;;;  thus we have u0=/=v0 as 
                ;;;   where we should have a u = v -> bottom
                ;;;       or maybe just a bottom proof term from tha, sta
                ;;;   then we need to add the proof into thj, which is a simple assert
                ;;; together with Vu=/=v (the big disjunction)
                ;;; no change on sta, stj
                (do                 
                  [(cons u0 thj:u0=u) <- (walk/state u)]
                  [(cons v0 thj:v0=v) <- (walk/state v)]
                  [thj:u=v->u0=v0     =  
                      (λ (t:u=v)
                        (let* ([t:v=v0 (LFeq-symm thj:v0=v)]
                              [t:u=v0 (LFeq-trans t:u=v t:v=v0)]
                              [t:u0=v0  (LFeq-trans thj:u0=u t:u=v0)])
                          t:u0=v0))]
                  ;;; [to-bottom   =  (LFassert ((== u0 v0) . impl . (Bottom)))]
                  [new-st-thj     = (state-type-thj new-st)]
                  [new-st-sta     = (state-type-sta new-st)]
                  [bot            = (pfmap-ref new-st-thj (Bottom))]
                  [the-parameter  = (pfmap-ref new-st-sta (== u0 v0))]
                  [u0=v0->bot     = (LFassert ((== u0 v0) . impl . (Bottom)))]
                  ;;; TODO: check free var in u0=v0->bot is bounded by old-state-sta
                  [t:u=v->bot       = (fresh-param (t) (LFlambda t (== u v) (LFapply u0=v0->bot (thj:u=v->u0=v0 t))))]
                  [axiom-neg      = (LFaxiom (impl (impl (== u v) (Bottom) (=/= u v))))]
                  [t:u=/=v        = (LFapply axiom-neg t:u=v->bot)]
                  [t:Vu=/=v       = (LFapply (LFassert ( (=/= u v) . impl . all-disj-inequ-type )) t:u=/=v)]
                  [_              <- (add-to-thj (=/= u v) t:u=/=v)]
                  [_              <- (add-to-thj all-disj-inequ-type t:Vu=/=v)]
                  [<-return t:Vu=/=v]
                )]
            ['()  
                ;;; u=/=v is never satisfied, we proceed to check the rest
                ;;;  if rest is satisfied, we can construct thj
                ;;;   because it is easy to see that u=v can be proved
                ;;;  in fact it is alreaady proved in new-st
                ;;; no change on sta stj
                (do 
                  [_              <- (set-st new-st)]
                  [(disj _ rest-inequ)  = all-disj-inequ-type]
                  [proof-by-contra = (LFassert ((== u v) . impl . ((=/= u v) . impl . (Bottom))))]
                  [thj:u==v       <- (query-thj (== u v))]
                  [not-u=/=v      = (LFapply proof-by-contra thj:u==v)]
                  [exclude-impossible = 
                      (LFassert (((=/= u v) . impl . (Bottom)) . 
                                  impl . ( all-disj-inequ-type . impl . rest-inequ)))]
                  [a:rest-inequ   = (LFapply (LFapply exclude-impossible not-u=/=v) a:Vu=/=v)] 
                  [<-end (neg-unify*/state rest a:rest-inequ)]
                )]
            [(cons _ _)
                ;;; u=/=v is satisfied with newly given constraints
                ;;; at this stage we have proof term for
                ;;;   u==v iff Λ (ui == vi)
                ;;; whose contrapositive is the proof we want
                (do 
                  [newsubs    = newly-added]
                  
                  [new-st-sta = (state-type-sta new-st)]
                  [new-st-tha = (state-type-tha new-st)]
                  [new-st-stj = (state-type-stj new-st)]
                  [new-st-thj = (state-type-thj new-st)]
                  [l-new-eqs = (map (λ (p) (== (car p) (cdr p))) newsubs)]
                  [n-l-new-eqs = (complement l-new-eqs)]
                  [r-equ     = (== u v)]
                  [n-r-equ   = (=/= u v)]
                  [about-rest = (foldl disj (Bottom)
                                  (map (λ (t) (=/= (car t) (cdr t))) newsubs))]
                  [target-type-for-stj = (foldl disj (Bottom)
                                  (map (λ (t) (=/= (car t) (cdr t))) newsubs))]
                  [target-type-for-thj = (foldl disj (Bottom)
                                  (map (λ (t) (=/= (car t) (cdr t))) list-u-v))]
                  ;;; we extract proof for l-new-eqs <-> r-equ
                  [l-params  = (map (λ (eq) (pfmap-ref new-st-sta eq)) l-new-eqs)]
                  [l-proofs  = (map (λ (eq) (pfmap-ref new-st-stj eq)) l-new-eqs)]
                  [r-param   = (pfmap-ref new-st-tha r-equ)]
                  [r-proof    = (pfmap-ref new-st-thj r-equ)]
                  [l<->r-type = (equiv (foldl conj l-new-eqs (Top)) r-equ)]
                  [l<->r      = (LFeqv-product l-params (list r-param) l-proofs (list r-proof))]
                  [n-l<->r-type = (equiv n-l-new-eqs n-r-equ)]
                  [l<->r->n-l<->r = (LFassert (l<->r-type . impl . n-l<->r-type))]
                  [n-l<->r    = (LFapply* l<->r->n-l<->r l<->r)]
                  [n-l2<->r2  = (LFapply* (LFassert ((equiv n-l-new-eqs n-r-equ) . impl . (equiv (disj n-l-new-eqs about-rest) (disj n-r-equ about-rest)))) n-l<->r)]
                  ;;; now we modify state
                  [updating-sta-pair = (append newly-added rest)]
                  [updating-sta-goal = (foldl disj (Bottom) (map (λ (t) (=/= (car t) (cdr t)))) updating-sta-pair)]
                  [updating-tha-pair = list-u-v]
                  [updating-tha-goal = (foldl disj (Bottom) (map (λ (t) (=/= (car t) (cdr t)))) updating-tha-pair)]
                  [updated-st = (state-diseq-update old-st (lambda (x) (cons (append newly-added rest) x)))]
                  [_          <- (set-st updated-st)]
                  ;;; now we add tha, sta about updated-st 
                  [sta-l          <- (fresh-param (term) (add-to-sta updating-sta-goal))]
                  [tha-r          <- (fresh-param (term) (add-to-tha updating-tha-goal))]
                  [n-r     = (LFapply* (LFpair-pi-1 n-l2<->r2) sta-l)]
                  [n-l     = (LFapply* (LFpair-pi-2 n-l2<->r2) tha-r)]
                  [_    <- (add-to-stj target-type-for-stj n-l)]
                  [_    <- (add-to-thj target-type-for-thj n-r)]
                  [<-return n-r]
                )
            ]
          )
        ]
      )
    ]
  )
)



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
  (set? any? ?state? . -> . ?state?)
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
                    [(? (lambda (the-set) (equal? the-set (set pair?))))
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

(define/contract (term-not-finite-type x)
  (any? . -> . Goal?)
  (conj* (=/= x '()) (=/= x #t) (=/= x #f)))


(define/contract (has-type-resp-equ-axiom-goal x0 x ty?*)
    (any? any? set? . -> . Goal?)
    ((x0 . == . x) 
      . impl . 
      ((type-constraint x0 ty?*) . impl . (type-constraint x ty?*))))


(define/contract (has-type-intersect-axiom-goal x ty1?* ty2?*)
    (any? set? set? . -> . Goal?)
    ((type-constraint x ty1?*)
      . impl . 
      ((type-constraint x ty2?*) . impl . (type-constraint x (set-intersect ty1?* ty2?*)))))


(define/contract (has-type-subset-axiom-goal x ty1?* ty2?*)
    (any? set? set? . -> . Goal?)
    (assert-or-warn (subset? ty1?* ty2?*) "Not subtype inclusion! \n")
    ((type-constraint x ty1?*) . impl . (type-constraint x ty2?*)))


(define/contract (has-empty-type-bottom x)
    (any? set? set? . -> . Goal?)
    ((type-constraint x (set)) . impl . (Bottom)))



;;; precondition: (term-not-finite-type x) is in tha
(define/contract (check-as-inf-type-disj/state type?* x a:has-type)
  (set? any? . -> . (WithBackgroundOf? (=== state-type?)))
  (define type-constraint-goal (type-constraint x type?*))

  ;;; we will need to add t:has-type into thj
  ;;;    also add t:has-type to stj/sta
  ;;;     if we encounter 
  (do 
    [(cons x0 t:x0=x)  <- (walk/state x)]
    [t:x=x0       = (LFeq-symm t:x0=x)]
    [<-end 
      (match x0 
        [(var _ _ )
            (do 
              [x0TypeRcded <- (type-info-query x0 'NotSet)]
              [x0TypeOrg =
                (if (equal? x0TypeRcded 'NotSet)
                  all-inf-type-label
                  x0TypeRcded)]
              [inf-type-axiom = (LFaxiom ( (term-not-finite-type x) . -> . (type-constraint x all-inf-type-label) ))]
              [not-finite-x <- (query-tha (term-not-finite-type x))]
              [inf-type-x   = (LFapply inf-type-axiom not-finite-x)]
              
              [inf-type-x0  = (LFapply (has-type-resp-equ-axiom-goal t:x=x0 inf-type-x))]
              [prev-stj:has-type-Rcded <- 
                (if (equal? x0TypeRcded 'NotSet)
                    inf-type-x0
                    (query-stj (type-constraint x0 x0TypeOrg)))]
              [x0Type    = (set-intersect x0TypeOrg type?*)]

              ;;; add to sta/tha
              [sta:has-type <- (fresh-param (term) (add-to-sta (type-constraint x0 x0Type) term))]
              [tha:has-type <- (fresh-param (term) (add-to-tha (type-constraint x  type?*) term))]
              ;;; add to stj/thj
              [stj:x0-has-type?* = 
                (LFapply* (LFassert (has-type-resp-equ-axiom-goal x x0 type?*)) t:x=x0 tha:has-type)]
              [stj:x0-has-x0Type =
                (LFapply* (LFassert (has-type-intersect-axiom-goal x0 type?* x0TypeOrg)) stj:x0-has-type?* prev-stj:has-type-Rcded)]
              [_ <- (add-to-stj (type-constraint x0 x0Type) stj:x0-has-x0Type)]
              [thj:x-has-x0Type = 
                (LFapply* (LFassert (has-type-resp-equ-axiom-goal x0 x x0Type)) t:x0=x sta:has-type)]
              [thj:x-has-type?* =
                (LFapply* (LFassert (has-type-subset-axiom-goal x x0Type type?*)) thj:x-has-x0Type)]
              [_ <- (add-to-thj (type-constraint x  type?*) thj:x-has-type?*)]
              ;;; Now deal with type information in the state
              [_ <- (type-info-set x0 x0Type)]
              [<-end 
                (if (set-empty? x0Type)
                    ;;; we are in bottom state
                    (do 
                      [stj:bottom = (LFapply* (LFassert (has-empty-type-bottom x0)) stj:x0-has-x0Type)]
                      [thj:bottom = (LFapply* (LFassert (has-empty-type-bottom x))  thj:x-has-x0Type)]
                      [_ <- (add-to-stj (Bottom) stj:bottom)]
                      [_ <- (add-to-thj (Bottom) thj:bottom)]
                      [<-return thj:x-has-type?*]
                    )
                    (pure-st thj:x-has-type?*))
              ]
            )]
        [v 
          (do 
            [check-all-type-cst = (ormap (lambda (x?) (x? v)) (set->list type?*))]
            [<-end
              (if check-all-type-cst
                (do 
                  [thj:checked-x0    = (LFassert (type-constraint x0 type?*))]
                  [thj:checked-x     = (LFapply* (LFassert (has-type-resp-equ-axiom-goal x0 x type?*)) t:x0=x thj:checked-x0)]
                  [_ <- (add-to-thj (type-constraint x type?*) thj:checked-x)]
                  [<-return thj:checked-x])
                
                (do 
                ;;; add to stj a bottom type
                  [checked-x0   = (LFassert ((type-constraint x0 type?*) . -> . (Bottom)))]
                  ;;; [sta:hastype <- (fresh (term) (add-to-sta (type-constraint x0 type?*) term))]
                  ;;; [tha:hastype <- (fresh (term) (add-to-tha (type-constraint x type?*) term))]
                  ;;; [_ <- (add-to-thj (Bottom) (LFapply* checked-x0 sta:has-type))]
                  [thj:x=x0          = (LFeq-symm t:x0=x)]
                  [stj:x0=x          <- (query-stj (== x0 x))]
                  [stj:x=x0          = (LFeq-symm stj:x0=x)]
                  [tha:checked-x     = a:has-type]
                  [stj:checked-x0    = (LFapply* (LFassert (has-type-resp-equ-axiom-goal x x0 (set))) stj:x0=x tha:checked-x)]
                  [stj:bottom        = (LFapply* checked-x0 stj:checked-x0)]
                  [_ <- (add-to-stj (Bottom) stj:bottom)]
                  [<-end (failed-state)]
                  ;;; [thj:checked-x     = (LFapply* (LFassert (has-type-resp-equ-axiom-goal x0 x type?*)) thj:x0=x thj:checked-x0)]
                  ;;; [_ <- (add-to-thj (type-constraint x type?*) thj:checked-x)]
                  )
              )
            ]
          )
        ]
      
      )
    ]
  )
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

;;; (define (map-matured-stream f stream)
;;;   (match stream
;;;     [#f #f]
;;;     [(cons h t) (cons (f h) (map-matured-stream f t))]
;;;   )
;;; )

;;; (define (fold-matured-stream binary initial-state stream)
;;;   (match stream
;;;     [#f initial-state]
;;;     [(cons h t) (fold-matured-stream binary (binary h initial-state) t)]
;;;   )
;;; )

;;; (define (append-matured-stream a b)
;;;   (match a 
;;;     [#f b]
;;;     [(cons h t) (cons h (append-matured-stream t b))]
;;;   )
;;; )

;;; ;;; lift check-as-inf-type onto stream
;;; ;;; check-as-inf-type-on-each :: type-label  x term x matured-stream[st] -> matured-stream[st]
;;; ;;;  when type-label = #f, we think of it as don't do any check, thus return original stream
;;; (define (check-as-inf-type-on-each type? t sts)
;;;   (if (equal? type? #f)
;;;     sts
;;;     (fold-matured-stream 
;;;         append-matured-stream
;;;         #f 
;;;         (map-matured-stream (lambda (st) (check-as-inf-type type? t st)) sts))
;;;   )
;;; )
