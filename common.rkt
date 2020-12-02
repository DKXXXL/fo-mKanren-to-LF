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
  state-direction-set
  state-diseq-set
  state-diseq-update
  state-scope-update
  state-scope-set
  state-typercd-cst-add
  state-typercd-set
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
  )

;;; bear with it now.... let me search if there is
;;;  extensible record later
(require struct-update)
(require racket/contract)

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
  (define debug-info-threshold 1)
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

(struct tproj (v cxr) #:prefab)


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
(define all-inf-type-label (list pair? number? string? symbol?))


;;; TODO: if all of the elements in type set are for the finite, 
;;;   then inequality might cause trouble  
;;;   for example, (exists x y z.) they are all different, they are all booleans

;;; sub -- list of substution 
;;; diseq -- list of list of subsitution 
;;;     -- interpreted as conjunction of disjunction of inequality 
;;; assymbol/asstring/asnumber are all a list of variables
;;;   to indicate disjoint sets
;;;   typercd : a dictionary index -> set of type-encoding 
;;;     "as disjunction of possible types"
;;;   
(struct state (sub scope trace direction diseq typercd) #:prefab)
(define empty-state (state empty-sub (list initial-var) '() '() '() (hash)))
(define-struct-updaters state)

;;; we consider #f is the failed state, also one of the state
(define (?state? obj) (or (equal? obj #f) (state? obj)))

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

;;; state x var x (set of) typeinfo -> state
(define/contract (state-typercd-cst-add st v type-info)
  (state? var? set? . -> . state?)

  (define typerc (state-typercd st))
  (define type-info (if (set? type-info) type-info (set type-info)))
  (define org (hash-ref typerc v #f))
  (define new-type-info 
    (if org 
    (hash-set typerc v (set-intersect org type-info))
    (hash-set typerc v type-info)))
  (state-typercd-set st typerc)
)

(define (stream? x)
  (match x
    [#f #t]
    [(cons h t) (stream? t)]
  )
)

(define (any? _) #t)

(define/contract (unify u v st)
  (any? any? state? . -> . stream?)
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
              [check-as-inf-type-disj*-c (lambda (type?* t st) (if (and type?* st) (check-as-inf-type-disj type?* t st) st))]
              [checked-type-state (foldl check-as-inf-type-disj*-c
                                         erased-type-state 
                                         new-vars-types new-vars)]
                                         )
        ;;;  TODO: short-circuit the possible #f appearing inside foldl

        (and checked-type-state
          (wrap-state-stream (inequality-recheck checked-type-state) )))
  
  )))

;; Reification
(define/contract (walk* tm sub)
  (any? list? . -> . any?)
  (let ((tm (walk tm sub)))
    (match tm
      [(cons a b) (cons (walk* a sub) (walk* b sub))]
      [(tproj x cxr) (tproj_ (walk* x sub) cxr)]
      [_ tm]
    )))
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


(define (is-singleton-type x) 
  (define k (hash-ref singleton-type-map x 'False)) 
  (if (equal? k 'False) #f #t)
  )
(define (not-singleton-type x) (not (is-singleton-type x)))

;;; check-as-inf-type-disj: List[inf-type-predicate] x term x state -> state
;;;  currently it will use predicate as marker
;;;  precondition: type?* is never #f, st is never #f
;;;   precondition: type?* \subseteq all-inf-type-label
(define/contract (check-as-inf-type-disj type?* t st)
  (any? any? ?state? . -> . ?state?)
  (define inf-type?* (filter not-singleton-type type?*))

  (define infinite-type-checked-state ;;; type : state
    (and st
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
                    ['() #f]
                    ;; this part is very weird... as we can see most fresh is not really existential
                    ;;;   quantifier because they don't specify scope!!
                    ;;;  here it is even more complicated ... what is the scope of a b?
                    ;;;    if we don't know the scope, will it cause problem when generating trace?
                    [(list pair?_)
                      #:when (equal? pair?_ pair?)
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

          [v (and (ormap (lambda (x?) (x? v)) inf-type?*) st)]) ))
    ;;; return the following
    infinite-type-checked-state
)

;;; check-as-inf-type :: inf-type-label  x term x (state or #f) -> (state or #f)
;;;  precondition: type? \in all-inf-type-label 
;;;  if type-label = #f, then we will just return st
(define/contract (check-as-inf-type type? t st) 
  (any? any? ?state? . -> . ?state?)
  (if (and type? st)
    (check-as-inf-type-disj (list type?) t st)
    st)
)

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
