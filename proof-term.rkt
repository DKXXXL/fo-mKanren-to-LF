#lang racket
(provide
  (struct-out LFsigma)
  (struct-out LFpair)
  (struct-out LFinjl)
  (struct-out LFinjr)
  (struct-out LFrefl)
  (struct-out LFpack)
  pt/h
  pth-compose
  single-hole
  curried-pf/h
  <-pf/h-inc
  )



;;; this file is defining structure for proof terms
;;;  vanilla miniKanren only has 
;;;     dependent pair(sigma), normal pair(left right), sum type(injl, injr)
;;;     refl (propositional equality type)
;;;  wholeType == goal!
;;;  construct CH correspondence for miniKanren goals

;;; proof terms

(struct proof-term () #:prefab)

;;; introduction rule
(struct LFsigma (ex body wholeType)  #:prefab)
;;; elimination rule
(struct LFsigma-pi-1 (term) #:prefab)
(struct LFsigma-pi-2 (term) #:prefab)
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


;;; introduction rule
(struct LFpair  (left right) #:prefab)
;;; I think induction tells you that here wholeType is unnecessary
;;; elimination rule
(struct LFpair-pi-1 (term) #:prefab)
(struct LFpair-pi-2 (term) #:prefab)

;;; introduction rule
(struct LFinjl  (left wholeType) #:prefab)
(struct LFinjr  (right wholeType) #:prefab)

;;; No elimination rule for coproduct?

;;; the wholeType is actually the wholeProp
(struct LFrefl    (x) #:prefab)
;;; wholeType here is trivial, (== x x)

(struct LFpack (subterm description) #:prefab)

;;; (struct var (index) #:prefab) ;;; object variable, only used for lambda term
;;; (struct const (term type) #:prefab) ;;; all the lisp terms should be here


;;; for constructive implication type
;;; ? and maybe universal quantifier type
;;;  it is not really "type", more like sum type of several type
;;;     (more like a set)
;;;  But constructivity requires us to consider proposition as types
(struct LFlambda (params types body) #:prefab)
(struct LFapply (func args) #:prefab)
(struct LFparam (index name) #:prefab)

(struct LFtrue () #:prefab)

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
(struct pt/h (f) #:prefab)


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
  (pt/h 
    (lambda (x)
      (let*
        ([ppt2- (ppt2 x)])
        (if (pt/h? ppt2-)
          (apply-in-order ppt1 ppt2-)
          (ppt1 ppt2-))))))

(define single-hole (pt/h (lambda (x) x)))

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
    ((_  (hole) body)) 
      (pt/h (lambda (hole) body))

    ((_ (hole holes ... ) body) 
      (pt/h (lambda (hole) (curried-pf/h (holes ...) body))))
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