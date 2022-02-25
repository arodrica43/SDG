{-# OPTIONS --cubical --safe #-}

module SDG.CommAlgebra.DirProd where

    open import Cubical.Algebra.Semigroup
    open import Cubical.Algebra.Monoid
    open import Cubical.Algebra.Group
    open import Cubical.Algebra.AbGroup
    open import Cubical.Algebra.Ring
    open import Cubical.Algebra.CommRing
    open import Cubical.Algebra.Module
    open import Cubical.Algebra.Algebra
    open import Cubical.Algebra.CommAlgebra
    open import Cubical.Foundations.Everything

    
    open import SDG.Ring.DirProd renaming (_⊗_ to _×R_)
    open import SDG.CommRing.DirProd renaming (_⊗_ to _×_)


    private
        variable
            ℓ : Level
            k : CommRing ℓ

    module _ (R S : CommAlgebra k ℓ) where
            private
                asCRingR = CommAlgebra→CommRing R
                asCRingS = CommAlgebra→CommRing S
                asRingR = CommRing→Ring asCRingR
                asRingS = CommRing→Ring asCRingS
                0R = CommAlgebraStr.0a (snd R)
                0S = CommAlgebraStr.0a (snd S)
                _+R_ = CommAlgebraStr._+_ (snd R)
                _+S_ = CommAlgebraStr._+_ (snd S)
                -R_ = CommAlgebraStr.-_ (snd R)
                -S_ = CommAlgebraStr.-_ (snd S)
                _⋆R_ = CommAlgebraStr._⋆_ (snd R)
                _⋆S_ = CommAlgebraStr._⋆_ (snd S)
                asLModR = Algebra→Module (CommAlgebra→Algebra R)
                asLModS = Algebra→Module (CommAlgebra→Algebra S)     

            asLModuleR×S : LeftModule (CommRing→Ring k) ℓ
            asLModuleR×S = (asTypeR×S asRingR asRingS) , (leftmodulestr 
                                                            (0r asRingR asRingS) 
                                                            (asRingR + asRingS) 
                                                            ((- asRingR) asRingS) 
                                                            (λ a x → (a ⋆R fst x) , (a ⋆S snd x)) 
                                                            (ismodule 
                                                                (AbGroupStr.isAbGroup (snd (asAbGroupR×S asRingR asRingS))) 
                                                                (λ r s x i → (LeftModuleStr.⋆-assoc (snd asLModR) 
                                                                                    r s (fst x) i) , 
                                                                             LeftModuleStr.⋆-assoc (snd asLModS)
                                                                                    r s (snd x) i) 
                                                                (λ r s x i → LeftModuleStr.⋆-ldist (snd asLModR) 
                                                                                    r s (fst x) i , 
                                                                             LeftModuleStr.⋆-ldist (snd asLModS) 
                                                                                    r s (snd x) i) 
                                                                (λ r x y i → (LeftModuleStr.⋆-rdist (snd asLModR) 
                                                                                    r (fst x) (fst y) i) , 
                                                                             (LeftModuleStr.⋆-rdist (snd asLModS) 
                                                                                    r (snd x) (snd y) i)) 
                                                                λ x i → (LeftModuleStr.⋆-lid (snd asLModR) (fst x) i) , 
                                                                         LeftModuleStr.⋆-lid (snd asLModS) (snd x) i))
            
            asAlgebraR×S : Algebra (CommRing→Ring k) ℓ
            asAlgebraR×S = (asTypeR×S asRingR asRingS) , algebrastr 
                                                            (0r asRingR asRingS) 
                                                            (1r asRingR asRingS) 
                                                            (asRingR + asRingS) 
                                                            (asRingR · asRingS) 
                                                            ((- asRingR) asRingS) 
                                                            (λ a x → (a ⋆R fst x) , (a ⋆S (snd x))) 
                                                            (isalgebra 
                                                                (LeftModuleStr.isLeftModule (snd asLModuleR×S)) 
                                                                (RingStr.·IsMonoid (snd (asRingR×S asRingR asRingS))) 
                                                                (RingStr.dist (snd (asRingR×S asRingR asRingS))) 
                                                                (λ r x y i → (AlgebraStr.⋆-lassoc (snd (CommAlgebra→Algebra R)) r (fst x) (fst y) i) , 
                                                                              AlgebraStr.⋆-lassoc (snd (CommAlgebra→Algebra S)) r (snd x) (snd y) i) 
                                                                λ r x y i → AlgebraStr.⋆-rassoc (snd (CommAlgebra→Algebra R)) r (fst x) (fst y) i , 
                                                                            AlgebraStr.⋆-rassoc (snd (CommAlgebra→Algebra S)) r (snd x) (snd y) i)
        
            asCommAlgR×S : CommAlgebra k ℓ
            asCommAlgR×S = asTypeR×S asRingR asRingS , 
                        commalgebrastr (0r asRingR asRingS) 
                                        (1r asRingR asRingS) 
                                        (asRingR + asRingS) 
                                        (asRingR · asRingS) 
                                        ((- asRingR) asRingS) 
                                        (λ a x → (a ⋆R fst x) , (a ⋆S (snd x))) 
                                        (iscommalgebra 
                                            (AlgebraStr.isAlgebra (snd asAlgebraR×S)) 
                                            λ x y i → (CommAlgebraStr.·-comm (snd R) (fst x) (fst y) i) , 
                                                       CommAlgebraStr.·-comm (snd S) (snd x) (snd y) i)
                                      
    _⊗_ : CommAlgebra k ℓ → CommAlgebra k ℓ → CommAlgebra k ℓ
    R ⊗ S = asCommAlgR×S R S         