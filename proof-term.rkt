#lang racket
(provide
  (struct-out LFsigma)
  (struct-out LFsigma-pi-1)
  (struct-out LFsigma-pi-2)
  (struct-out LFpair)
  (struct-out LFpair-pi-1)
  (struct-out LFpair-pi-2)
  (struct-out LFinjl)
  (struct-out LFinjr)
  (struct-out LFprim-rel)
  (struct-out LFpack)
  (struct-out proof-term)
  (struct-out LFaxiom)
  (struct-out LFproof)
  (struct-out LFlambda)
  (struct-out LFeq-refl)
  (struct-out LFeq-symm)
  (struct-out LFeq-trans)
  (struct-out LFeq-pair)
  (struct-out LFeq-pis)
  (struct-out LFassert)
  (struct-out LFapply)
  (struct-out LispU)
  (struct-out pt/h)
  pth-compose
  single-hole
  curried-pf/h
  <-pf/h-inc
  fresh-param
  lf-let*
  )

(require "mk-fo-def.rkt")

;;; this file is defining structure for proof terms
;;;  vanilla miniKanren only has 
;;;     dependent pair(sigma), normal pair(left right), sum type(injl, injr)
;;;     refl (propositional equality type)
;;;  wholeType == goal!
;;;  construct CH correspondence for miniKanren goals

;;; proof terms

(struct proof-term () #:prefab)


;;; introduction rule
(struct LFsigma proof-term (ex body wholeType)  #:prefab)
;;; elimination rule
(struct LFsigma-pi-1 proof-term (term) #:prefab)
(struct LFsigma-pi-2 proof-term (term) #:prefab)
;;;   #:methods gen:custom-write
;;;   [(define (write-proc val output-port output-mode)
;;;      (fprintf output-port "{~a ~a}" (LFsigma-ex val) (LFsigma-body val)))]
;;; 
;;; it suppose to have bindingType, i.e. (LFsigma ex bindingType body)
;;;  but I think we are working on dynamic typed staff
;;;  (fresh (x) (disj (== x 5) (== x "1"))) is acceptable
;;; maybe we only need to specify that we are quantifying around set (5, "1", cons ..) or 
;;;   prop (== ... , disj, conj ...), 
;;; another issue is that wholeType is necessary here, because term 
;;; (5, refl) : (ex x, x == 5)
;;; (5, refl) : (ex x, 5 == 5)

;;; we introduce another proof term
;;;   called (ex-for var binding-domain goal) 
;;;   it has closed semantic to (forall v domain goal)
;;;   difference is that, binding-domain has to be non-empty (of goals)
;;;   It is mainly used for justifying (ex) goal, because once (ex) goal
;;;     is done, we actually get a state as a result, a state is actually a set of 
;;;     value each variable can take restricted value from the state, but not ground/concrete value
;;;   var is a single variable, corresponds the current (ex v goal)
;;; this can be considered as a proof term combined of lambdas, lets 
;;;     note that the introduced free variables are attached to the binding-domain
;;;     so semantically we don't ask for "arbitrary free variable", but just ask for the existence of
;;; one value for the "free variable" in the binding domain
;;;  and to check the correctness of this proof term, we only need to, during proof-check (elaboration)
;;;   to verify that there are concrete/grounded value that satisfies binding-domain

;;; notice: this proof term can inhabit in existential, and also inhabited in universal
;;;       quantifier
(struct LFfor proof-term (var binding-domain goal) #:prefab)

;;; inhabited in the existential
(struct ex-for LFfor () #:prefab)
;;; inhabited in the universal
(struct uni-for LFfor () #:prefab)
;;; thus now for universal/existenail quantifer, there are two possible proof terms
;;;   LFsigma/LFlambda and LFfor

(struct LFlet proof-term (v bind bindT body) #:prefab)


;;; introduction rule
(struct LFpair proof-term  (left right) #:prefab)
;;; I think induction tells you that here wholeType is unnecessary
;;; elimination rule
(struct LFpair-pi-1 proof-term (term) #:prefab)
(struct LFpair-pi-2 proof-term (term) #:prefab)

;;; introduction rule
(struct LFinjl proof-term (left wholeType) #:prefab)
(struct LFinjr proof-term (right wholeType) #:prefab)



;;; the wholeType is actually the wholeProp

;;; so we have a lot of primitive Relation (and dualizable)
;;;   for each of them introduce a (almost no information) proof term
;;;   is weird
(struct LFprim-rel proof-term (goalType) #:prefab)
;;; this is a place holder for each of them
;;;   TODO: we will have to discuss how to deal with 
;;;     them respectively

;;; introduction/elimination for relate
(struct LFpack proof-term (subterm description) #:prefab)
(struct LFunpack proof-term (term pack-description) #:prefab)

;;; (struct var (index) #:prefab) ;;; object variable, only used for lambda term
;;; (struct const (term type) #:prefab) ;;; all the lisp terms should be here

(struct LispU () #:prefab)
;;; for constructive implication type
;;; and maybe universal quantifier type
;;;   for the case 
;;;  it is not really "type", more like sum type of several type
;;;     (more like a set)
;;;  But constructivity requires us to consider proposition as types
(struct LFlambda proof-term (params types body) #:prefab)
(struct LFapply proof-term (func args) #:prefab)

(define-syntax LFapply*
  (syntax-rules ()
    ((_ l x) (LFapply l x))
    ((_ l x y ...) 
      (LFapply* (LFapply l x) y ...))
    ))


(struct LFparam proof-term (index name) #:prefab)
;;; 
;;; this indicates free vars in the proof term
;;;   just place holder and requires fill-in
(struct LFopenvar LFparam (index name) #:prefab)

;;; its paras is a parameter-list (of Goal), and body will have
;;; we use (paras => body) to indicate open term's type
(struct LFopenterm proof-term (paras body) #:prefab)

;;; the l=>r and r=>l are both open terms
;;;   the type is exactly (eqv lr.paras rl.paras)
;;;   some other enforcements are that lr.bodyType = (conj* rl.paras); rl 
(struct LFeqvOpenterm proof-term (lr rl) #:prefab)


;;; equality proof term
(struct LFeq-refl  proof-term (x) #:prefab)
(struct LFeq-symm  proof-term (t) #:prefab)
(struct LFeq-trans proof-term (t1 t2) #:prefab)
;;; a = b, c = d then (a,c) = (b,d)
(struct LFeq-pair proof-term (t1 t2) #:prefab)
;;; if (a,c) = (b,d) then (a=b)/\(c=d)
(struct LFeq-pis proof-term (t1 t2) #:prefab)

;;; we staged the following operation into data structure


;;; when A => u' = u, A -> v' = v, A <-> B
;;; then we have (A /\ u' = v') <-> (B /\ u = v)
;;; (struct LFeqv-product proof-term (t:l<=>r t:l=>u0=u t:l=>v0=v) #:prefab)

;;; on cartesian monodial category
(struct LFeqv-product proof-term (l-params r-params l-proofs r-proofs) #:prefab)


(define newLFparam
  ((lambda ()
    (define idx 0)
    (lambda (name)
      (let* (
          [ridx idx]
          [k (set! idx (+ 1 idx))])
        (LFparam idx name)))
  )))

;;; name several new LFparam and scope them
(define-syntax fresh-param
  (syntax-rules ()
    ((_ (x ...) g0 gs ...)
     (let ((x (newLFparam 'x)) ...) (begin g0 gs ...) ))
  ))


(define-syntax lf-let*
  (syntax-rules (:)
    ((_ () g0)
     g0)

    ((_ ((x y : T) xs ...) g0 )
     (LFlet x y T (lf-let* (xs ...) g0) ))
  ))


;;; (struct LFtrue () #:prefab)

;;; There are two universe -- one is lisp elements universe
;;;  the other is the universe of propositions
;;;   and each proposition is inhabited iff it is true
;;;  to inhabit a proposition, a proof term is required
(struct LFProofterm proof-term (goalType) #:prefab)

;;; for axiom schema
(struct LFaxiom LFProofterm () #:prefab)

;;; a term of an arbitrary type
;;; during type checking, we will check if the type is inhabit
;;;  usually to encode something absurd like (1 == 2 -> Bottom)
(struct LFassert LFProofterm () #:prefab)

;;; usually just a (assumption) parameter
(struct LFproof LFProofterm (term) #:prefab)

;;; the above consists the BNF definition of LF-lambda-term
;;; also exactly the definition of proof tree, except the wholeType
;;;     which are the meta-data

;;; The following data structure is to construct LF-term when searching
;;;   might not be useful now 

;;; proof-terms with holes!
;;;  basically incomplete proof terms
;;;  hole as meta-variable
(struct hole (index) #:prefab)

;;; every partial proof tree can be considered as a 
;;;   function from proof-terms to 


;;;   proof-tree/hole is function from proof-terms to a complete proof-term
;;;   but proof-tree/hole must be curried
;;; hole-num is used for detect invariance
(struct pt/h (f hole-num) 
  #:transparent
  #:property prop:procedure
             (struct-field-index f)
)


;;; ;;; Partial-Proof-Tree(PPT) := proof-tree/hole x [hole] x pair 

;;; ;;;   reflection is for debugging purpose
;;; (struct ppt (pt holes) #:prefab)
;;; ;;; this is direct style, but at the end we only need something 
;;; ;;;   to represent a tree with a hole
;;; ;;;   the following traversal will be expensive... maybe
;;; ;;;   use (prooftree -> prooftree) as a tree with one hole
;;; ;;;   will be much less expensive
;;; ;;;   but a tree with several holes inside requires some
;;; ;;;   kind of algebraid design and interface to maintain the
;;; ;;;    invariance... let's postpone it TODO!


;;; ;;; (ppt1 . compose . ppt2)(x) = ppt1(ppt2(x))
(define/contract (pth-compose ppt1 ppt2)
  (pt/h? pt/h? . -> . pt/h?)

  (let* ([hole-num1 (pt/h-hole-num ppt1)]
         [hole-num2 (pt/h-hole-num ppt2)])
    (pt/h 
      (lambda (x)
        (let*
          ([ppt2- (ppt2 x)])
          (if (pt/h? ppt2-)
            (pth-compose ppt1 ppt2-)
            (ppt1 ppt2-)))) 
        (+ hole-num1 hole-num2 -1)))
    )

(define single-hole (pt/h (lambda (x) x) 1))

;;; (define/contract (fill-in ppt pt)
;;;   (ppt? any? . -> . any?)

;;; )

;;; ;;; (ppt1 . compose . ppt2)(x) = ppt1(ppt2(x))
;;; ;;; so ppt2 is the first to be filled in with x, and then
;;; ;;;   ppt2 will be fill in the first hole of ppt1
;;; (define/contract (compose ppt1 ppt2)
;;;   (ppt? ppt? . -> . ppt?)
;;;   (let*
;;;     ([pt/h1 (ppt-pt ppt1)]
;;;      [pt/h2 (ppt-pt ppt2)]
;;;      [holes1 (ppt-hole ppt1)]
;;;      [holes2 (ppt-hole ppt2)]
;;;      [holes (append holes2 (cdr holes1))]
;;;      )
;;;     (ppt (apply-in-order pt/h1 pt/h2) holes)
;;;   )
;;; )


;;; sugar for creating proof-term-w/hole(s)
;;; (curried-pf/h (a b c) body) will directly curry 
;;;   this function and ask for filling on a b c in order
;;;  (return a pt/h obj)
(define-syntax curried-pf/h
  (syntax-rules ()
    ((_  (hole) body)
      (pt/h (lambda (hole) body) 1))

    ((_ (hole holes ... ) body) 
      (pt/h 
        (lambda (hole) (curried-pf/h (holes ...) body)) 
        (length '(hole holes ... ))))
  ))

;;; A small sugar for creating proof-term
;;; Usage 
;;;  (single-hole . <-pf/h-inc . LFtrue) will directly return a LFtrue
;;;  (single-hole . <-pf/h-inc . (_) (LFinjl _ True)) will give you back (LFinj _ True)
;;;   . <-pf/h-inc . (_) (LFinjl _ True) will give you  (LFinjl (LFinjl _ True) True)
(define-syntax <-pf/h-inc
  (syntax-rules ()
    ((_ org term) 
      (org term) )     

    ((_ org (hole holes ...) body) 
      (let* [(new-pth (curried-pf/h (hole holes ...) body))]
        (pth-compose org new-pth) ))
  ))