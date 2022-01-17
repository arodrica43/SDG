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
             _⋆R_ = CommAlgebraStr._⋆_ (snd R)
             _⋆S_ = CommAlgebraStr._⋆_ (snd S)

    --     asRing-CRingR×S : Ring ℓ
    --     asRing-CRingR×S = ((fst R) , snd asRingR) × ((fst S) , (snd asRingS)) 
        
         asCommAlgR×S : CommAlgebra k ℓ
         asCommAlgR×S = asTypeR×S asRingR asRingS , 
                        commalgebrastr (0r asRingR asRingS) 
                                       (1r asRingR asRingS) 
                                       (asRingR + asRingS) 
                                       (asRingR · asRingS) 
                                       ((- asRingR) asRingS) 
                                       (λ a x → (a ⋆R fst x) , (a ⋆S (snd x))) 
                                       (iscommalgebra (isalgebra (ismodule 
                                                                    (AbGroupStr.isAbGroup (snd (asAbGroupR×S asRingR asRingS))) 
                                                                    (λ r s x i → (LeftModuleStr.⋆-assoc 
                                                                                    {!   !} 
                                                                                    {!   !} 
                                                                                    {!   !}
                                                                                    {!   !} 
                                                                                    {!   !}) , {!   !})
                                                                    {!   !} 
                                                                    {!   !} 
                                                                    {!   !}) 
                                                                 {!   !} 
                                                                 {!   !} 
                                                                 {!   !} 
                                                                 {!   !}) 
                                       λ x y i → {!   !})
         
         --(asTypeR×S asRingR asRingS) , commringstr (0r asRingR asRingS) 
    --                                                               (1r asRingR asRingS) 
    --                                                               (asRingR + asRingS) 
    --                                                               (asRingR · asRingS) 
    --                                                               ((- asRingR) asRingS) 
    --                                                               (iscommring (isRingR×S asRingR asRingS) 
    --                                                                 λ x y i → IsCommRing.·Comm (CommRingStr.isCommRing (snd R)) (fst x) (fst y) i , 
    --                                                                           IsCommRing.·Comm (CommRingStr.isCommRing (snd S)) (snd x) (snd y) i)

    -- _⊗_ : CommRing ℓ → CommRing ℓ → CommRing ℓ
    -- R ⊗ S = asCommRingR×S R S    