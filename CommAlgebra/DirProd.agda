{-# OPTIONS --cubical #-}

module SDG.CommAlgebra.DirProd where

    open import Cubical.Foundations.Everything
    open import Cubical.Algebra.Ring
    open import SDG.Ring.DirProd 

    variable
        ℓ : Level
    postulate
        R S : Ring ℓ

    R⊗S : Ring ℓ
    R⊗S = R ⊗ S
