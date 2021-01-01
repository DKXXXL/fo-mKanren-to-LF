#lang racket
(provide
  (struct-out LFsigma)
  (struct-out LFpair)
  (struct-out LFinjl)
  (struct-out LFinjr)
  (struct-out LFrefl)
  (struct-out LFpack)
  )



;;; this file is defining structure for proof terms
;;;  vanilla miniKanren only has 
;;;     dependent pair(sigma), normal pair(left right), sum type(injl, injr)
;;;     refl (propositional equality type)
;;;  wholeType == goal!
;;;  construct CH correspondence for miniKanren goals

;;; proof terms

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
(struct LFlambda (params body) #:prefab)
(struct LFapply (func args) #:prefab)
(struct LFparam (index name) #:prefab)

;;; the above consists the BNF definition of LF-lambda-term
;;; also exactly the definition of proof tree, except the wholeType
;;;     which are the meta-data

;;; The following data structure is to construct LF-term when searching
;;;   might not be useful now 

;;; proof-terms with holes!
;;;  basically incomplete proof terms
;;;  hole as meta-variable
(struct hole (index) #:prefab)


;;; Partial-Proof-Tree(PPT) := [indicesOfHoles] x proof-tree
(struct ppt (holes pt) #:prefab)
;;; this is direct style, but at the end we only need something 
;;;   to represent a tree with a hole
;;;   the following traversal will be expensive... maybe
;;;   use (prooftree -> prooftree) as a tree with one hole
;;;   will be much less expensive
;;;   but a tree with several holes inside requires some
;;;   kind of algebraid design and interface to maintain the
;;;    invariance... let's postpone it TODO!


(define (subst ppt index term)
  (match ppt
    [(hole tindex) (if (equal? index tindex) term ppt)]
    ;;; other cases are direct recursion
  )
)

;;; fill-in-partial-tree : partial-proof-tree x partial-proof-tree -> partial-proof-tree 
;;;  it will fill in the first hole of 'withHole
;;; note that the 'withHole should have at least one hole
(define (fill-in-partial-tree stuffing withHole)
  (void)
)

