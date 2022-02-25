{-# OPTIONS --cubical --safe #-}

module SDG.CommRing.DirProd where

    open import Cubical.Algebra.Semigroup
    open import Cubical.Algebra.Monoid
    open import Cubical.Algebra.Group
    open import Cubical.Algebra.AbGroup
    open import Cubical.Algebra.Ring
    open import Cubical.Algebra.CommRing
    open import Cubical.Foundations.Everything

    open import SDG.Ring.DirProd renaming (_⊗_ to _×_)


    private
        variable
            ℓ : Level

    module _ (R S : CommRing ℓ) where
        private
            asRingR = CommRing→Ring R
            asRingS = CommRing→Ring S
            

        asRing-CRingR×S : Ring ℓ
        asRing-CRingR×S = ((fst R) , snd asRingR) × ((fst S) , (snd asRingS)) 
        
        asCommRingR×S : CommRing ℓ
        asCommRingR×S = (asTypeR×S asRingR asRingS) , commringstr (0r asRingR asRingS) 
                                                                  (1r asRingR asRingS) 
                                                                  (asRingR + asRingS) 
                                                                  (asRingR · asRingS) 
                                                                  ((- asRingR) asRingS) 
                                                                  (iscommring (isRingR×S asRingR asRingS) 
                                                                    λ x y i → IsCommRing.·Comm (CommRingStr.isCommRing (snd R)) (fst x) (fst y) i , 
                                                                              IsCommRing.·Comm (CommRingStr.isCommRing (snd S)) (snd x) (snd y) i)

    _⊗_ : CommRing ℓ → CommRing ℓ → CommRing ℓ
    R ⊗ S = asCommRingR×S R S   