#lang racket
(provide
  (all-from-out "proof-term.rkt")
  (all-from-out "microk-fo.rkt")
  step
  mature
  mature/directed
  mature?
  empty-state/fuel
  proof-term-construct
  proof-check
  )

;;; (require struct-update)
(require "microk-fo.rkt")
(require "proof-term.rkt")


;;; one implementation idea is to use trace information 
;;;  to remove disjunction in the goal
;;;   but won't work as there are contruction in thunk

;;; the second idea is to insrument the state with 
;;;   "input-trace", 
;;;   let's name it as direction

;;; bad engineering -- adhoc polymorphism is totally
;;;   expanded into duplicate code
;;;  most of the below are duplicates



(define (empty-state/fuel direction)
  (state-direction-set empty-state direction)
)

;;; (struct state/direction state (direction) #:prefab)
;;; (define-struct-updaters state/direction)
;;;  the above two comments is a long story -- basically an attempt to
;;;   make the whole thing extensible


(define (mature/directed s)
  (if (mature? s) s (mature/directed (step-directed s))))

;;; only if everything is written in open-recursion style
;;;  currently raw recursion (boiler-plate) will need to be 
;;;  repeated again
;;;   expression problem all over again
(define (start-directed st g)
  (match g
    ((disj g1 g2)
      ;;; match st-dfilter to find if  
      (let 
        ((fuel (state-direction st)))
        (if (equal? fuel '()) 
            ;;; no more determinstic
            (step-directed (mplus (pause (trace-left st) g1)
                                  (pause (trace-right st) g2)))
            (match fuel
              [`(left . ,remain)  (pause (state-direction-set (trace-left st) remain) g1)]
              [`(right . ,remain) (pause (state-direction-set (trace-right st) remain) g2)]
            )
        )
      ))
    ((conj g1 g2)
     (step-directed (bind (pause st g1) g2)))
    ((relate thunk _)
     (pause st (thunk)))
    ((== t1 t2) (unify t1 t2 st))
    ((ex _ gn) (start-directed st gn)))
    )

(define (step-directed s)
  (match s
    ((mplus s1 s2)
     (let ((s1 (if (mature? s1) s1 (step-directed s1))))
       (cond ((not s1) s2)
             ((pair? s1)
              (cons (car s1)
                    (mplus s2 (cdr s1))))
             (else (mplus s2 s1)))))
    ((bind scope s g)
     (let ((s (if (mature? s) s (step-directed s))))
       (cond ((not s) #f)
             ((pair? s)
              (step-directed (mplus (pause (state-scope-set (car s) scope) g)
                           (bind scope (cdr s) g))))
             (else (bind scope s g)))))
    ((pause st g) (start-directed st g))
    (_            s)))


;;; This is the function that construct LF-term with
;;;    given a trace and a goal
;;;  Q. the trace might be re-arrange? I am not sure
;;; proof-term-construct-wt :: 
;;;   Trace x FinalState x Goal -> Trace x LF-proof-term
;;;  the correct way to write this piece of code 
;;;   is to use state-monad on "Trace"
;;;   but we refactor it later
;;; TODO: a bug when (run*/trace (x y) (== x y))
;;;   currently it returns some weird meta-variable into the 
;;;     term. which is of course incorrect
;;;   I suggest make the given subst compose with s default subst
;;;   that will subst all the meta-variable into unit
;;;    (basically saying every unspecified element will be considered as unit)
(define (proof-term-construct-wt trace st goal)
  (let ([ptc (lambda (trace goal) (proof-term-construct-wt trace st goal))]
        [walk*/unitize (lambda (x y) (unitize-metavar (walk* x y)))])
    (match goal
      [(conj g1 g2)
        (match-let* 
          ([(cons rmt1 lterm) (ptc trace g1)]
           [(cons rmt2 rterm) (ptc rmt1 g2)])
          (cons rmt2 (LFpair lterm rterm))
        )
      ] 
      [(relate thunk description)
        ;;; I won't do anything here, 
        ;;; Greg says something should be done here
        ;;;   TODO: put substitution information here
        ;;;     appendo a bc abc=>
        ;;;    printed as append [a:= subst(a)] [subst(bc)] [subst(abc)] 
        ;;; (ptc trace (thunk))
        (match-let* 
          ([(cons rmt1 bodyterm) (ptc trace (thunk))]
           [subst-description (cons (car description) (walk*/unitize (cdr description) (state-sub st)))])
          (cons rmt1 (LFpack bodyterm subst-description))
        )
        
      ]
      [(ex varname g)
        (match-let* (
          [index (walk*/unitize varname (state-sub st))]
          [(cons rmt body) (ptc trace g)])
          (cons rmt (LFsigma index body goal))
        )
      ]
      [(== t1 t2)
        (let* ([t1_ (walk*/unitize t1 (state-sub st))]
               [t2_ (walk*/unitize t2 (state-sub st))])
          (if (equal? t1_ t2_)
            (cons trace (LFrefl t1_))
            (raise "Equality estabilished Failure")))
      ]
      [(disj g1 g2)
        (match trace 
          [`(left . ,rmt) 
              (match-let* ([(cons rmt2 term) (ptc rmt g1)]) 
                (cons rmt2 (LFinjl term goal)))]
          [`(right . ,rmt) 
              (match-let* ([(cons rmt2 term) (ptc rmt g2)]) 
                (cons rmt2 (LFinjr term goal)))]
          [_ (raise "Trace Not Enough or Format Incorrect ")]
        )
      ]
    )
  )
)

(define (proof-term-construct trace state goal)
  (cdr (proof-term-construct-wt trace state goal))
)

;;; proof-check :: LFterm x goal -> Bool
;;;   currently it will ignore the type information that is auxilary
;;;     inside LFterm; also the description of the relate (user-customized relation)
;;;   interestingly, it will check equality :)
(define (proof-check term type)
  (match `(,term . ,type)
    ;;; watch out binding name
    [(cons (LFsigma exval bodyt _) (ex exvar bodyT))
      (let* ([subst (list `(,exvar . ,exval))]
             [bodyT-indexed (walk*/goal bodyT subst)])
        (proof-check bodyt bodyT-indexed)     
        )]
    ;;; dead recursion on others
    [(cons (LFpair lt rt) (conj lT rT))
      (and (proof-check lt lT) (proof-check rt rT))]
    [(cons (LFinjl lt _) (disj lT rT))
      (proof-check lt lT)]
    [(cons (LFinjr rt _) (disj lT rT))
      (proof-check rt rT)]
    [(cons (LFrefl x) (== lt rt))
      (and (equal? x lt) (equal? x rt))]
    [(cons (LFpack subterm _) (relate thunk _))
      (proof-check subterm (thunk))
    ]
    [_ #f]
        
  )
)