;;; this file is defining structure for proof terms
;;;  vanilla miniKanren only has 
;;;     dependent pair(sigma), normal pair(left right), sum type(injl, injr)
;;;     refl (propositional equality type)
;;;  wholeType == goal!
;;;  construct CH correspondence for miniKanren goals

(struct LFsigma (ex body wholeType)  #:prefab) 
;;; it suppose to have bindingType, i.e. (LFsigma ex bindingType body)
;;;  but I think we are working on dynamic typed staff
;;;  (fresh (x) (disj (== x 5) (== x "1"))) is acceptable
;;; maybe we only need to specify that we are quantifying around set (5, "1", cons ..) or 
;;;   prop (== ... , disj, conj ...), 
;;; another issue is that wholeType is necessary here, because term 
;;; (5, refl) : (ex x, x == 5)
;;; (5, refl) : (ex x, 5 == 5)

(struct LFpair  (left right) #:prefab)
;;; I think induction tells you that here wholeType is unnecessary

(struct LFinjl  (left wholeType) #:prefab)
(struct LFinjr  (right wholeType) #:prefab)
;;; the wholeType is actually the wholeProp
(struct refl    (x) #:prefab)
;;; wholeType here is trivial, (== x x)

;;; (struct var (index) #:prefab) ;;; object variable, only used for lambda term
(struct const (term type) #prefab) ;;; all the lisp terms should be here

;;; the above consists the BNF definition of LF-lambda-term

;;; proof-terms with holes!
;;;  basically incomplete proof terms
;;;  hole as meta-variable
(struct hole (index) #:prefab)


;;; Partial-Proof-Tree(PPT) := 
(struct partial-proof-tree ())