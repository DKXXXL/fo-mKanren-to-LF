#lang racket
(provide
  (struct-out var)
  initial-var
  var/fresh
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
  unitize-metavar
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

;;; set the following to 'ON then we will have debug info
(define debug-output-info 'OFF)


;; Logic variables
(struct var (name index) ;;;#:prefab
  #:transparent
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

(define (debug-info-initialization)
  (define debug-info-threshold 
    (if (equal? debug-output-info 'ON) -100 1))
  (define (get-debug-info-threshold)
    debug-info-threshold)

  (define (set-debug-info-threshold! l)
    (set! debug-info-threshold l))
  
  (values get-debug-info-threshold set-debug-info-threshold!)
)

(define-values 
  (get-debug-info-threshold set-debug-info-threshold!)
  (debug-info-initialization))


(define-syntax debug-dump-w/level
  (syntax-rules ()
    ((_ l x ...) 
      (if (>= l (get-debug-info-threshold)) 
        (printf x ...)
        'Threshold-Too-High))
          ))

(define-syntax debug-dump
  (syntax-rules ()
    ((_ x ...) 
      (debug-dump-w/level 0 x ...))))

(define-syntax raise-and-warn
  (syntax-rules ()
    ((_ x ...) 
      (begin (debug-dump-w/level 100 x ...) (/ 1 0)))))

(define-syntax assert-or-warn
  (syntax-rules ()
    ((_ COND x ...) 
      (if COND
        #t
        (begin (debug-dump-w/level 100 x ...) (/ 1 0)  )))))

(define-syntax assert
  (syntax-rules ()
    ((_ COND) 
      (assert-or-warn COND "Assertion Violated!"))))


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

(struct tproj (v cxr)
  ;;; #:prefab 
  #:transparent
  #:guard (lambda (v cxr type-name)
                    (cond
                      [(and (var? v) (pair? cxr)) 
                       (values v cxr)]
                      [else (error type-name
                                   "bad v: ~e"
                                   v)]))
)


(define (tcar t) 
  (match t 
    [(cons a b) a]
    [(tproj x y) (tproj x (cons 'car y))]
    [(var _ _) (tproj t (list 'car))]
    [_ (raise-and-warn "tcar: Unexpected Value ~a" t)]
  ))

(define (tcdr t) 
  (match t 
    [(cons a b) b]
    [(tproj x y) (tproj x (cons 'cdr y))]
    [(var _ _) (tproj t (list 'cdr))]
    [_ (raise-and-warn "tcdr: Unexpected Value ~a" t)]
  ))

(define (term? x) (or (var? x) (tproj? x)))

;;; normalize a tproj term so that tproj-v is always a var 
(define (tproj_ term cxr)
  
  ;;; (define (m x) (match x ['car tcar] ['cdr tcdr]))
  ;;; (define (compose f g) (lambda (x) (f (g x))))
  ;;; (define mcxr (map m cxr))
  ;;; (define )
  (if (var? term) 
    (if (null? cxr)
      term
      (tproj term cxr))
    (match cxr
      [(cons 'car rest) (tcar (tproj_ term rest))]
      [(cons 'cdr rest) (tcdr (tproj_ term rest))]
      ['() term] 
    ))
)

;;; (define var/fresh
;;;   (let ((index 0))
;;;     (lambda (name) (set! index (+ 1 index))
;;;       (var name index))
;;;       ))

;; States
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
        [t=t1        = (assf (lambda (x) (equal? t x)) sub)]
        [<-end 
          (if t=t1
              (do 
                [t1   = (cdr t=t1)]
                [a:t=t1 = (pfmap-ref sta eqxt)]
                [a:t1=t = (LFeq-symm a:t=t1)]
                [(cons tend t:tend=t1) <- (walk/state t1)]
                [a:tend=t (LFeq-trans a:tend=t1 a:t1=t)]
                [<-return (cons tend a:tend=t)])
              (pure-st (cons t (LFeq-refl t))))])]
    ;;; currently no proof term for tproj
    ;;;  as it is part of internal of relative complements
    ;;;   maybe the better way to prove relative complements is to use 
    ;;;   proof elaboration
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
    [st     <- get-state]
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

(define (true? v) (equal? v #t))
(define (false? v) (equal? v #f))
;;; (null? '() )

(define type-label-top (set true? false? null? pair? number? string? symbol?))
(define all-inf-type-label (set pair? number? string? symbol?))

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

(define get-st  (get state-type?))
(define set-st  (set state-type?))
(define pure-st (pure state-type?))
(define run-st  (run state-type?))

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
                  [bg2+fr2 (swbdo bg1)]
                  ))
              bg2+fr2)))))

(define/contract (>> a b) (>>= a (λ (_) b)))

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
;;; (do [<-return x]) = (pure-state x)
;;;     usually it is  

(define-syntax do
  (syntax-rules (<- <-end <-return =)
    ((_ [x = y] sth ...) 
      (match-let ([x y]) (do sth ...)))
    ((_ [x <- y] sth ...) 
      (y . >>= . (match-lambda x (do sth ...))))
    ((_ [<-end y]) 
      y)
    ((_ [<-return y]) 
      (pure-state y))
  ))


;;; TODO: if all of the elements in type set are for the finite, 
;;;   then inequality might cause trouble  
;;;   for example, (exists x y z.) they are all different, they are all booleans

(define empty-pfmap (hash))
(define pfmap-ref hash-ref)
(define pfmap-set hash-set)

(define add-to-sta)
(define add-to-stj)
(define add-to-tha)
(define add-to-thj)

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
(struct failed-state (bot-from-sta bot-from-tha) #:prefab) ;; indicating bottom type
(struct state (sub scope pfterm diseq typercd) #:prefab)
(define empty-state (state empty-sub (list initial-var) single-hole '() (hash)))
(define-struct-updaters state)

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
    [t:u0=v0->t:u=v 
      (λ (t:u0=v0)
        (let* ([t:u=u0 (LFeq-symm t:u0=u)]
               [t:u=v0 (LFeq-trans t:u=u0 t:u0=v0)]
               [t:u=v  (LFeq-trans t:u=v0 t:v0=v)])
          t:u=v))] ;; construct a lambda that construct u=v using a:u0=v0
    [t:u=v->t:u0=v0 
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
              [a:u0=v0 (pfmap-ref newsta (== u0 v0))]
              [t:u=v (t:u0=v0->t:u=v a:u0=v0)]
              [t:u0=v0 (t:u=v->t:u0=v0 a:u=v)]
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
              [a:v0=u0 (pfmap-ref newsta (== v0 u0))]
              [a:u0=v0 (LFeq-symm a:v0=u0)]
              [t:u=v (t:u0=v0->t:u=v a:u0=v0)]
              [t:u0=v0 (t:u=v->t:u0=v0 a:u=v)]
              [t:v0=u0 (LFeq-symm t:u0=v0)]
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
              [a:u01=v01+a:u02=v02 (LFeq-pis a:u0=v0)]
              [t:u01=v01 <- (unify/st/proof u01 v01 (LFpair-pi-1 a:u01=v01+a:u02=v02))]
              [t:u02=v02 <- (unify/st/proof u02 v02 (LFpair-pi-2 a:u01=v01+a:u02=v02))]
              [t:u0=v0   =  (LFeq-pair t:u01=v01 t:u02=v02)] ;; construct equality using
              [t:u=v     =  (t:u0=v0->t:u=v t:u0=v0)]
              [_ <- (add-to-thj t:u=v)]
              [<-return t:u=v])]
        [(eqv? u0 v0) 
            ;;; only add thj
            (do
              [t:u=v (t:u0=v0->t:u=v (LFeq-refl u0))]
              [_ <- (add-to-thj t:u=v)]
              [<-return t:u=v])] ;; the proof is trivially LFrefl
        [o/w 
            (set-st (failed-state (void)))] 
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


(define/contract (unify/state u v a:u=v)
  (any? any? proof-term? . -> . (WithBackgroundOf? (=== state-type?)))
  (do
    [t:u=v         <- (unify/st/proof u v a:u=v)]
    [unified-state <- get-st]

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
          [eqt (LFeq-pair t:a0=a t:b0=b)]
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


;;; monadic style
;;;   the second is a big disjunction
;;; precondition: (type a:Vu=/=v) is the disjunction of inequalities
(define (neg-unify*/state list-u-v a:Vu=/=v)
  (list? proof-term? . -> . (WithBackgroundOf? (=== state-type?)))
  (match list-u-v
    ['() #f]
    [(cons (cons u v) rest)
      (do 
        [old-st <- get-st]
        [a:u=v  =  (fresh-param (t) t)]
        [(cons new-st t:u=v) = (run-st (unify/state u v a:u=v) old-st)]
        [newly-added         = (extract-new (state-sub newst) (state-sub oldst))]
        [<-end 
          (match newly-added
            [#f  
                ;;; u=/=v is satisfied in new-st (a failed state),
                ;;;   where we should have a u = v -> bottom
                ;;;  or maybe just a bottom proof term from tha, sta
                ;;;    we need to add the proof into thj
                ;;; together with Vu=/=v (the big disjunction)
                ;;; no change on sta, stj
                (set-st old-st)]
            ['()  
                ;;; u=/=v is never satisfied, we proceed to check the rest
                ;;;  if rest is satisfied, we can construct thj
                ;;; no change on sta stj
                (neg-unify*/state rest)]
            [(cons _ _)
                ;;; u=/=v is satisfied with newly given constraints

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
