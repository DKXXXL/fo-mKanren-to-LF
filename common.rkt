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
  reify/initial-var)

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
  (void)
)

(struct state (sub trace direction) #:prefab)
(define empty-state (state empty-sub '() '()))
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

(define (unify u v st)
  (let ((sub (unify/sub u v (state-sub st))))
    (and sub (cons (state-sub-set st sub) #f))))

;; Reification
(define (walk* tm sub)
  (let ((tm (walk tm sub)))
    (if (pair? tm)
        `(,(walk* (car tm) sub) .  ,(walk* (cdr tm) sub))
        tm)))
(define (reified-index index)
  (string->symbol
    (string-append "_." (number->string index))))
(define (reify tm st)
  (define index -1)
  (walk* tm (let loop ((tm tm) (sub (state-sub st)))
              (define t (walk tm sub))
              (cond ((pair? t) (loop (cdr t) (loop (car t) sub)))
                    ((var? t)  (set! index (+ 1 index))
                               (extend-sub t (reified-index index) sub))
                    (else      sub)))))
(define (reify/initial-var st)
  (reify initial-var st))


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



;;; ;;; ho-sub :: [(var, Term)] -> (var -> Term)
;;; ;;;   precondition: there is no cyclic reference in subst
;;; (define (ho-sub subst) (lambda (v) (walk v subst)))
;;; ;;;  the second way to define is clearer
;;; ;;;   and we will do occur check
;;; (define (ho-subst-singleton x t) (lambda (v) (if (equal? x v) t v)))

;;; ;;; now we alias type ho-subst = (var -> Term)
;;; (define (compose hs1 hs2) (lambda (v) (hs1 (hs2 v))))
;;; ;;; this version of extend might not be satisfactory
;;; (define (extend-ho-sub x t ho-sub)
;;;   (compose ho-sub (ho-subst-singleton x t)))

;;; ;;; return a subst that works exactly like hs
;;; ;;;   except that won't do anything on x
;;; (define (shadow x hs)
;;;   (lambda (v)
;;;     (if (equal? x v) v (hs v))))

;;; ;;;  interestingly (shadow x hs) =/= (extend-ho-sub x x hs)
