{-# OPTIONS --cubical --safe #-}

module SDG.Nilpotent where

    open import Cubical.Algebra.CommRing
    open import Cubical.Algebra.CommAlgebra
    open import Cubical.Algebra.CommAlgebra.FPAlgebra
    open import Cubical.Algebra.CommAlgebra.Instances.FreeCommAlgebra
    open import Cubical.Foundations.Everything
    open import Cubical.Data.Nat
    open import Cubical.Data.FinData
    
    open import SDG.CommRing.DirProd
    open import SDG.Base

    open import Cubical.Algebra.Ring.BigOps

    private
        variable
            ℓ : Level

    module _ (k : CommRing ℓ) where
        private
            k-as-ring = CommRing→Ring k
            0k : fst k
            0k = CommRingStr.0r (snd k)
        open Product k-as-ring
        open Foundations 
        isNilpRing : CommRing ℓ → Type ℓ
        isNilpRing A = Σ ℕ λ n → (v : FinVec (fst k) n) → ∏ (λ i → v i)  ≡ 0k

        NilpRing : Type (ℓ-suc ℓ)
        NilpRing = Σ (CommRing ℓ) λ A → isNilpRing A 

        isNilpAlg : CommAlgebra k ℓ → Type ℓ
        isNilpAlg A = isNilpRing (CommAlgebra→CommRing A)

        NilpAlg : Type (ℓ-suc ℓ)
        NilpAlg = Σ (CommAlgebra k ℓ) λ A → isNilpAlg A 

        FPNilpAlg : Type (ℓ-suc ℓ)
        FPNilpAlg = Σ FPAlg λ A → {! A ≡ ()  !}