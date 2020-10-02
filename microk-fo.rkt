#lang racket
(provide
  (all-from-out "common.rkt")
  (struct-out disj)
  (struct-out conj)
  (struct-out relate)
  (struct-out ==)
  (struct-out ex)
  (struct-out mplus)
  (struct-out bind)
  (struct-out pause)
  step
  mature
  mature?
  walk*/goal)

(require "common.rkt")

;; first-order microKanren
;;; goals
(struct disj   (g1 g2) 
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ∨ ~a" (disj-g1 val) (disj-g2 val)))]
)

(struct conj   (g1 g2)  
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ∧ ~a" (conj-g1 val) (conj-g2 val)))]
)
(struct relate (thunk description)      ;;;#:prefab
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a" (relate-description val)))]
)
(struct ==     (t1 t2)               
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a =ᴸ ~a" (==-t1 val) (==-t2 val)))]
     ;;; L stands for Lisp Elements
)
(struct ex     (varname g) 
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∃~a. ~a" (ex-varname val) (ex-g val)))]
)
;;; meta-data ex, actually will be ignored at this stage
;;;   indicating the scope of varname, 
;;;   but only as a hint

;;; we need implement the first version of complement,
;;;   so the complement version of each operation need to be defined
(struct =/= (t1 t2)
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "~a ≠ᴸ ~a" (==-t1 val) (==-t2 val)))]
)

(struct forall (varname g)
  #:methods gen:custom-write
  [(define (write-proc val output-port output-mode)
     (fprintf output-port "∀~a. ~a" (ex-varname val) (ex-g val)))]
)

;;; streams
(struct bind   (bind-s bind-g)          #:prefab)
(struct mplus  (mplus-s1 mplus-s2)      #:prefab)
(struct pause  (pause-state pause-goal) #:prefab)

(define (mature? s) (or (not s) (pair? s)))
(define (mature s)
  (if (mature? s) s (mature (step s))))

(define (start st g)
  (match g
    ((disj g1 g2)
     (step (mplus (pause (trace-left st) g1)
                  (pause (trace-right st) g2))))
    ((conj g1 g2)
     (step (bind (pause st g1) g2)))
    ((relate thunk _)
     (pause st (thunk)))
    ((== t1 t2) (unify t1 t2 st))
    ((=/= t1 t2) (neg-unify t1 t2 st))
    ((ex _ gn) (start st gn))
    ))

(define (step s)
  (match s
    ((mplus s1 s2)
     (let ((s1 (if (mature? s1) s1 (step s1))))
       (cond ((not s1) s2)
             ((pair? s1)
              (cons (car s1)
                    (mplus s2 (cdr s1))))
             (else (mplus s2 s1)))))
    ((bind s g)
     (let ((s (if (mature? s) s (step s))))
       (cond ((not s) #f)
             ((pair? s)
              (step (mplus (pause (car s) g)
                           (bind (cdr s) g))))
             (else (bind s g)))))
    ((pause st g) (start st g))
    (_            s)))


;;; walk*/goals :: Goal x subst -> Goal
;;;  precondition: subst has to be idempotent
(define (walk*/goal goal subst)
  (let* ([rec (lambda (g) (walk*/goal g subst))])
    (match goal
    ;;; non trivial parts
    ;;;   deal with terms
      ((== t1 t2) 
        (== (walk* t1 subst) (walk* t2 subst)))
    ;;; ex needs shadow the exvar
      ((ex exvar gn) 
        (ex exvar (walk*/goal gn (shadow-idempotent-sub exvar subst))))
    ;;; dead recursion on others
      ((disj g1 g2)
        (disj (rec g1) (rec g2)))
      ((conj g1 g2)
        (conj (rec g1) (rec g2)))
      ((relate thunk _)
        (relate (lambda () (rec (thunk)))))
    )
  )
)

;;; trivially negate the goal
;;;   not really useful, because on the run, the negate is used
;;;   on a subsitution map together with some other things
;;;  I currently don't know how to implement
;;;  and I think something like forall-bound is needed, but it currenty
;;;   isn't defined here, and the dual is ugly for it as well
(define (complement g)
  (let ([c complement])
    (match g
      [(disj g1 g2) (conj (c g1) (c g2))]
      [(conj g1 g2) (disj (c g1) (c g2))]
      [(relate _ _) (raise "User-Relation not supported.")]
      [(== t1 t2) (=/= t1 t2)]
      [(ex a gn) (forall a (c gn))]
      [(forall a gn) (ex a (c gn))]
    )
  )
)

