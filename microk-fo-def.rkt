#lang errortrace racket
(provide 
  (all-defined-out)
  (all-from-out "debug-info.rkt"))


;;; bear with it now.... let me search if there is
;;;  extensible record later
(require struct-update)
(require racket/contract)
(require errortrace)
(require "debug-info.rkt")

(instrumenting-enabled #t)


(define-syntax define/contract/optional
  (syntax-rules ()
    ((_ paras contract X ...) 
      (define paras X ...)  ;; turn off
      ;;; (define/contract paras contract X ...) ;; turn on
    )))



;; Logic variables
(struct var (name index) ;;;#:prefab
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a#~a" (var-name val) (var-index val)))]
)

;;; making part of tproj as var, 
(struct tp-var var ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "π~a" 
      (pretty-print-tproj (tproj_ (var-name val) (var-index val)))))]
  #:guard (lambda (v cxr type-name)
                    (cond
                      [(and (var? v) (not (tp-var? v)) (pair? cxr)) 
                       (values v cxr)]
                      [else (error type-name
                                   "bad v: ~e"
                                   v)]))
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


(define-syntax assert-or-warn
  (syntax-rules ()
    ((_ COND x ...) 
      (if COND
        #t
        (begin (debug-dump-w/level 100 x ...) (/ 1 0)  )))))

(define-syntax assert
  (syntax-rules ()
    ((_ COND) 
      (assert-or-warn COND "Assertion Violated! ~a" 'COND))))



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

(define-syntax fresh-var
  (syntax-rules ()
    ((_ x)
     (let ((x (var/fresh 'x))) x))))




(struct tproj (v cxr)
  ;;; #:prefab 
  #:transparent
  #:guard (lambda (v cxr type-name)
                    (cond
                      [(and (var? v) (not (tp-var? v)) (pair? cxr)) 
                       (values v cxr)]
                      [else (error type-name
                                   "bad v: ~e"
                                   v)]))
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
       (fprintf output-port (pretty-print-tproj val)))]
)


(define/contract (pretty-print-tproj tp)
  (tproj? . -> . string?)
  (define/contract (path-pretty x)
    (list? . -> . string?)
    (for/fold
      ([acc ""])
      ([each x])
      (string-append 
        acc
        (match each ['car "._0"] ['cdr "._1"]))))
  (let* 
    ([path (tproj-cxr tp)])
    (format "~a~a" (tproj-v tp) (path-pretty (reverse path)))))


(define (tcar t) 
  (match t 
    [(cons a b) a]
    [(tproj x y) (tproj x (cons 'car y))]
    [(tp-var x y) (tcar (tproj x y))]
    [(var _ _) (tproj t (list 'car))]
    [_ (raise-and-warn "tcar: Unexpected Value ~a" t)]
  ))

(define (tcdr t) 
  (match t 
    [(cons a b) b]
    [(tproj x y) (tproj x (cons 'cdr y))]
    [(tp-var x y) (tcdr (tproj x y))]
    [(var _ _) (tproj t (list 'cdr))]
    [_ (raise-and-warn "tcdr: Unexpected Value ~a" t)]
  ))

(define (term? x) (or (var? x) (tproj? x)))



;;; normalize a tproj term so that tproj-v is always a var 
;;;  tproj (list a b c) (cdr cdr) = c
;;;  tproj (cons a b) cdr cdr = (tproj b cdr) // var
;;;  tcar (tproj b cdr) = b.cdr.car
;;;  tcar (cons a b) = a
(define (tproj_ term cxr)
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


;; States
(define empty-sub '())

;;; sub -- list of assignments
;;; diseq -- list of list of disassignments
;;;     -- interpreted as conjunction of disjunction of inequality 
;;;   typercd : a dictionary index -> set of type-encoding 
;;;     "as disjunction of possible types"
;;;   
(struct state (sub scope diseq typercd) #:prefab)
(define empty-state (state empty-sub (list initial-var) '() (hash)))
(define-struct-updaters state)


;;; we consider #f is the failed state, also one of the state
(define (?state? obj) (or (equal? obj #f) (state? obj)))




;;; the parent type of all goals
;;;  and "Goal?" is helpful 
(struct Goal () 
  #:transparent)

(struct relate Goal (thunk description)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "{user-relation ~a}" (relate-description val)))]
)
(struct == Goal    (t1 t2)
  #:transparent               
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a =ᴸ ~a" (==-t1 val) (==-t2 val)))]
     ;;; L stands for Lisp Elements
)

;;; stands for existential quantifier
;;;   indicating the scope of varname, 
(struct ex Goal    (varname g) 
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∃~a. ~a" (ex-varname val) (ex-g val)))]
  #:guard (lambda (varname g type-name)
                    (cond
                      [(Goal? g) 
                       (values varname g)]
                      [else (error type-name
                                   "Should be Goal: ~e"
                                   g)]))
)


(struct =/= Goal (t1 t2)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ≠ᴸ ~a" (=/=-t1 val) (=/=-t2 val)))]
)

;;; universal quantifier,
;;;   domain decides the domain the varname quantifies on
(struct forall Goal (varname domain g)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∀~a {~a}. ~a" (forall-varname val) (forall-domain val)  (forall-g val)))]
  #:guard (lambda (varname domain g type-name)
                    (cond
                      [(and (var? varname) (Goal? g) (Goal? domain)) 
                       (values varname domain g)]
                      [else (error type-name
                                   "Should be Goal: ~e"
                                   g)]))
)

(struct symbolo Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "symbol ~a" (symbolo-t val)))]
)

(struct not-symbolo Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-symbol ~a" (not-symbolo-t val)))]
)


(struct numbero Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "number ~a" (numbero-t val)))]
)

(struct not-numbero Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-number ~a" (not-numbero-t val)))]
)


(struct stringo Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "string ~a" (stringo-t val)))]
)

(struct not-stringo Goal (t)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "not-string ~a" (not-stringo-t val)))]
)

;;; typeinfo is a set of type-symbol
;;; indicating t is union of these type
;;; Note: this goal is not part of exposed interface 
;;;   only inner mechanism use it
;;;   Users will use (not-)symbolo, (not-)numbero, .. so on
(struct type-constraint Goal (t typeinfo)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "type-constraint ~a ~a" (type-constraint-t val) (type-constraint-typeinfo val)))]
  #:guard (lambda (t typeinfo type-name)
                    (cond
                      [(set? typeinfo) 
                       (values t typeinfo)]
                      [else (error type-name
                                   "bad typeinfo: ~e"
                                   typeinfo)]))
)




(struct Top Goal ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "T" ))]
)


(struct Bottom Goal ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "⊥" ))]
)


;; Defunctionalized microKanren goals definition


(struct disj Goal   (g1 g2) 
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a ∨ ~a)" (disj-g1 val) (disj-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)

;;; ;;; disj-1 will invoke mplus-1
;;; (struct disj-1 disj   () 
;;;   #:transparent
;;;   #:methods gen:custom-write
;;;   [(define (write-proc val output-port output-mode)
;;;      (fprintf output-port "(~a ∨ ~a)" (disj-g1 val) (disj-g2 val)))]
;;;   #:guard (lambda (g1 g2 type-name)
;;;                     (cond
;;;                       [(andmap Goal? (list g1 g2)) 
;;;                        (values g1 g2)]
;;;                       [else (error type-name
;;;                                    "All should be Goal: ~e"
;;;                                    (list g1 g2))]))
;;; )


(struct conj  Goal (g1 g2)  
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a ∧ ~a)" (conj-g1 val) (conj-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)

;;; constructive implication, 
;;; its proof term is exactly the lambda
;;;  what's special about this is that
;;;   the system will try to extract the decidable component of antec
;;;     to either falsify or integrated into state
(struct cimpl  Goal (g1 g2)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a => ~a)" (cimpl-g1 val) (cimpl-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)

;;; constructive implication as well
;;;   what's different is that it will not deal with the antec
;;;     and directly consider every antec as part of assumption
;;;     (no semantic solving on assumption at all)
(struct cimpl-syn  cimpl ()  
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "(~a ⟶ ~a)" (cimpl-g1 val) (cimpl-g2 val)))]
  #:guard (lambda (g1 g2 type-name)
                    (cond
                      [(andmap Goal? (list g1 g2)) 
                       (values g1 g2)]
                      [else (error type-name
                                   "All should be Goal: ~e"
                                   (list g1 g2))]))
)


;; TODO (greg): consider using sets
;;; The following are a incomplete interfaces for assumption-base
;;;   in case in the future we want to modify the implementation
;;;   of assumption base 
(define (assumption-base? k) (list? k))
(define (empty-assumption-base? k) (equal? k '()))
(define empty-assumption-base '())

;;; Stream definition



;;; The following are defunctionalized stream structure

;;; stream-struct is the parent of all streams
(struct stream-struct () #:prefab)

(struct bind  stream-struct (assmpt s g)   
  #:transparent
  #:guard (lambda (assmpt s g type-name)
                    (cond
                      [(and (assumption-base? assmpt) 
                            (Stream? s) 
                            (Goal? g))
                       (values assmpt s g)]
                      [else (error type-name)]))
)

(struct mplus stream-struct (s1 s2) 
  #:transparent
  #:guard (lambda (s1 s2 type-name)
                    (cond
                      [(and (Stream? s1) 
                            (Stream? s2))
                       (values s1 s2)]
                      [else (error type-name
                              "Should both be Stream: ~e"
                              (list s1 s2) )]))
)

;;; ;;; mplus-1 differs from mplus in that, turning off currently
;;; ;;;     it will only endup at most one stream (as the result of disjunction)
;;; (struct mplus-1 mplus () 
;;;   #:transparent
;;;   #:guard (lambda (s1 s2 type-name)
;;;                     (cond
;;;                       [(and (Stream? s1) 
;;;                             (Stream? s2))
;;;                        (values s1 s2)]
;;;                       [else (error type-name
;;;                               "Should both be Stream: ~e"
;;;                               (list s1 s2) )]))
;;; )

(define-syntax mplus*
  (syntax-rules ()
    ((_ x) x)
    ((_ x y ...) 
      (mplus x (mplus* y ...)))))

;;; (pause st g) will fill the generated proof term into st
;;; it has the same specification as (start st g)
;;; (pause st g) has same specification as (start st g)

(struct pause stream-struct (assmpt state goal) #:prefab)


;;; f :: state -> stream of states
;;; mapped-stream f (cons a s) = mplus (f a) (mapped-stream f s)
;;;   in a lazy fashion
(struct mapped-stream stream-struct (f stream) #:prefab)


;;; semantically there is or in the "state"
;;;   this will lift the "or"s into stream
;;;   at the current stage, mark is used for pointing to
;;;     the disj component
;;; finally a stream of state where only conjunction is inside each state
;;;  a /\ (b \/ c) /\ (d \/ e) 
;;;  1 -> a /\ c /\ e; 2 -> a /\ b /\ e ...
(struct to-dnf stream-struct (state address) #:prefab)


;;; a stream of syntactical solving
(struct syn-solve stream-struct (assmpt init-assmpt st g) #:prefab)


;;; this will force the v in st to be a stream of ground term
;;; basically used for proof-term-generation for
;;;    existential quantifier
;;;  say we have state (v =/= 1) /\ (numbero v)
;;; this will enumerate v to be each ground value except for $v = 1$ and number
(struct force-v-ground stream-struct (v st) #:prefab)


;;; the special stream only used for forall
;;;   all the possibe results of first-attempt-s
;;;   will be complemented and intersect with the domain of the bind-g
;;;   bind-g will have to be a forall goal
(struct bind-forall  stream-struct (assmpt scope state domain-var g)          #:prefab)


;;; (lazily) detect stream or not
;;;   because we have #f as part of stream structure so
;;;   we cannot easily use stream-struct?
(define (Stream? s)
  (or (stream-struct? s)
    (match s
      [#f #t]
      [(cons k r) (Stream? r)]
      [o/w #f]
    )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; recursion scheme/endo-functor/homomorphism
;;;   whatever you want to call them, just a way to remove boilerplate code


;;; Denote Goal-map type as
;;;      (goal -> goal) -> (goal -> goal) -> goal -> goal
;;; extensible function on pattern matching
;;;  pretentious "map" just means it maps goal to goal
;;;   named as functor but actually just a homomorphism --
;;;     respects all the Goal? structure that is working on Goal?
;;;   This is inspired by TVM's IRFunctor, 
;;;     which I believe is also inspired by something else
;;; goal-base-map : (goal -> goal) -> (goal -> goal) -> goal -> goal
;;;  rec-parent will call the one on the past overloading functor

;;;   extended-f will use the whole composed functor
;;;  this functor will do nothing but recurse on the tree
(define (goal-base-map rec-parent rec-root g)
  ;;; (define rec extended-f)
  (let* ([rec rec-root])
    (match g
      [(disj   a b)   (disj  (rec a) (rec b))]
      [(conj   a b)   (conj  (rec a) (rec b))]
      [(cimpl  a b)   (cimpl (rec a) (rec b))]
      [(ex     v g)   (ex     v         (rec g))]
      [(forall v b g) (forall v (rec b) (rec g))]
      [_              (rec-parent g)])))  ;; otherwise do nothing

;;; Denote Goal-map type as
;;;      (goal -> goal) -> (goal -> goal) -> goal -> goal
;;;   named as functor but actually just a homomorphism --
;;;     respects all the Goal? structure that is not only working on Goal?

(define (goal-term-base-map rec-parent rec g)
  ;;; (define rec extended-f)
  (match g
    [(== x y)        (== (rec x) (rec y))]
    [(=/= x y)       (=/= (rec x) (rec y))]
    
    [(symbolo x)     (symbolo (rec x))]
    [(not-symbolo x) (not-symbolo (rec x))]
    [(numbero x)     (numbero (rec x))]
    [(not-numbero x) (not-numbero (rec x))]
    [(stringo x)     (stringo (rec x))]
    [(not-stringo x) (not-stringo (rec x))]
    [(type-constraint x types) (type-constraint (rec x) types)]
    [(disj a b)     (disj (rec a) (rec b))]
    [(conj a b)     (conj (rec a) (rec b))]
    [(ex v g)       (ex v (rec g))]
    [(forall v b g) (forall v (rec b) (rec g))]
    [(relate thunk descript)  (relate thunk (rec descript))] 
    [_ (rec-parent g)] ;; otherwise do nothing
  )
)


;;; homomorphism on state
(define (state-base-endo-functor rec-parent rec g)
  (match g
    [(state a scope d t)
      (state (rec a) scope (rec d) (rec t))]
    [_ (rec-parent g)]
  )
)

(define (hash-key-value-map rec-parent rec g)
  (match g 
    [(? hash?)
      (make-immutable-hash (rec (hash->list g)))]
    [_ (rec-parent g)]))

(define (identity-endo-functor rec-parent rec g) g)

(define (goal-identity g) g)


;;; this one basically can help me solve the expression problem
;;; this is the procedure that will compose a bunch of functor into
;;;     one homomorphism
;;; For example:  I can extend state as I want now  
;;; [(goal -> goal) -> (goal -> goal) -> goal -> goal] -> (goal -> goal) 
(define (compose-maps maps)
  (define (compose-maps-with-extf maps rec-root)
    (match maps
      [(cons fst then)
        (let* ([rec-parent (compose-maps-with-extf then rec-root)])
          (lambda (g) (fst rec-parent rec-root g))
        )]
      ['() (lambda (x) x)]
    )
  )
  (define (resultf g)
    ((compose-maps-with-extf maps resultf) g) )
  resultf
)
;;; Example Usage: 
;;; not-symbolo will be translated into (numbero v stringo v pairo v boolo)
;;; (define remove-neg-by-decidability
;;;   (define (match-single rec-parent rec-root g)
;;;     (match g
;;;       [(not-symbolo x) (disj (pairo x) (boolo x) (numbero x) (stringo x))]
;;;       [(not-numbero x) (disj (pairo x) (boolo x) (symbolo x) (stringo x))]
;;;       [(not-stringo x) (disj (pairo x) (boolo x) (numbero x) (symbolo x))]
;;;       [_ (rec-parent g)]
;;;     )
;;;   )
;;;   (compose-maps (list match-single goal-base-map))
;;; )
;;; (define remove-neg-by-decidability-and-remove-cimple
;;;   (define (match-single rec-parent rec-root g)
;;;     (match g
;;;       [(not-symbolo x) (disj (pairo x) (boolo x) (numbero x) (stringo x))]
;;;       [(not-numbero x) (disj (pairo x) (boolo x) (symbolo x) (stringo x))]
;;;       [(not-stringo x) (disj (pairo x) (boolo x) (numbero x) (symbolo x))]
;;;       [_ (rec-parent g)]
;;;     )
;;;   )
;;;   (define (remove-cimpl rec-parent rec-root g)
;;;     (match g
;;;       [(cimpl x) (disj (pairo x) (boolo x) (numbero x) (stringo x))]
;;;       [(stop ..) (ex)]
;;;       [_ (rec-parent g)]
;;;     )
;;;   )
;;;   (compose-maps (list remove-cimpl match-single goal-base-map))
;;; )

;;; cimpl -> ... /\ remove-neg-by-decidability



;;; homomorphism on pair, will respect pair construct
;;;  will also respect tproj
;;;   Recall tproj is used for intermediate representation
;;;   -- during relative complements we need pair-less point-ful representation
(define (pair-base-map rec-parent extended-f g)
  (define rec extended-f)
  (match g
    ['() '()]
    [(cons a b) (cons (rec a) (rec b))]
    [(tproj tm cxr) (tproj_ (rec tm) cxr)] ;; respect tproj
    [_ (rec-parent g)]
  )
)


;;; the goal is decidable 
;;;     iff goal is without any relate/any constructive implication
;;;     TODO: make it more relaxed
(define (decidable-goal? g)
  ;;; (Goal? . -> . boolean?)
  (define res #t)
  ;;; side-effect for folding
  ;;;   still using visitor pattern/homomorphism
  (define (each-case rec-parent rec g)
    (match g
      [(relate _ _) (begin (set! res #f) g)]
      ;; TODO (greg): if `a` is decidable, the entire implication may still be decidable
      ;;; [(cimpl a b) (begin (set! res #f) g)] ; don't even allow implication to be inside g
      [(forall _ b g_) 
          ;;; (rec (cimpl b g_)) ; equivalent semantic
          (begin (set! res #f) g) ; more conservative
          ] 
      [_ (rec-parent g)]
    )
  )
  (define f (compose-maps (list each-case goal-base-map identity-endo-functor)))
  (f g)
  res
)

