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
  check-asnumber
  check-asstring
  check-assymbol
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
;;; sub -- list of substution 
;;; diseq -- list of list of subsitution 
;;;     -- interpreted as conjunction of disjunction of inequality 
;;; assymbol/asstring/asnumber are all a list of variables
(struct state (sub trace direction diseq assymbol asstring asnumber) #:prefab)
(define empty-state (state empty-sub '() '() '() '() '() '()))
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
  (let* ([sub (unify/sub u v (state-sub st))])
    (and sub
      (let* ([unified-state (state-sub-set st sub)]
             [all-diseq (state-diseq unified-state)]
             [all-symbol (state-assymbol unified-state)]
             [all-number (state-asnumber unified-state)]
             [all-string (state-asstring unified-state)]
             [state-to-check (state (state-sub unified-state) '() '() '() '() '() '())]
             )

        ;;;  TODO: short-circuit the possible #f appearing inside foldl
        (let*
        ((state-to-check (foldl neg-unify* state-to-check all-diseq))
         (state-to-check (and state-to-check
                            (foldl check-assymbol state-to-check all-symbol)))
         (state-to-check (and state-to-check
                            (foldl check-asnumber state-to-check all-number)))
         (state-to-check (and state-to-check
                            (foldl check-asstring state-to-check all-string))))
            (wrap-state-stream state-to-check))))
  ))

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
        (state-diseq-update st (lambda (x) (cons (append newly-added rest) x)))])       
        )
      ]
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

;;; check-assymbol: term x state -> state
;;; 
(define (check-assymbol t st)
  (match (walk* t (state-sub st))
    [(? symbol?) st]
    [(var _ index) (state-assymbol-update st (lambda (x) (cons index x)))]
    [_ #f]
  )
)

(define (check-asnumber t st)
  (match (walk* t (state-sub st))
    [(? number?) st]
    [(var _ index) (state-asnumber-update st (lambda (x) (cons index x)) )]
    [_ #f]
  )
)

(define (check-asstring t st)
  (match (walk* t (state-sub st))
    [(? string?) st]
    [(var _ index) (state-asstring-update st (lambda (x) (cons index x)))]
    [_ #f]
  )
)