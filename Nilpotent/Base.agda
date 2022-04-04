{-# OPTIONS --cubical --safe #-}

module SDG.Nilpotent.Base where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.CommAlgebra.Instances.Pointwise
  open import Cubical.Data.Sigma
  open import Cubical.Data.FinData
  open import Cubical.Data.Nat
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing.Ideal
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.Ring.BigOps
  open import Cubical.Algebra.CommRing.RadicalIdeal
  open import Cubical.Foundations.Powerset
  open import Cubical.HITs.PropositionalTruncation
  open import SDG.Base

  module Nilradical (ℝ@(R , str) : CommRing ℓ) where

    open RadicalIdeal
    open CommIdeal ℝ
    open isCommIdeal
    nilradical : CommIdeal
    nilradical = √ ℝ 0Ideal 

  module Ring (ℝ@(R , str) : CommRing ℓ) where

    isNilpotent : R → Type ℓ
    isNilpotent  x = ∃[ n ∈ ℕ ] (ℝ Exponentiation.^ x) n ≡ CommRingStr.0r str
    isNilpOfOrder : R → ℕ → Type ℓ
    isNilpOfOrder x n = (ℝ Exponentiation.^ x) n ≡ CommRingStr.0r str
    isNilpOfOrderProp : R → ℕ → Type ℓ
    isNilpOfOrderProp x n = ∥ isNilpOfOrder x n ∥
    
    isNilpRing : Ring ℓ → Type ℓ
    isNilpRing A = ∃[ n ∈ ℕ ] (∀(v : FinVec (fst A) n) → Product.∏ A (λ i → v i) ≡ RingStr.0r (snd A))

    NilpRing : Type (ℓ-suc ℓ)
    NilpRing = Σ (Ring ℓ) λ A → isNilpRing A 

    isNilpCommRing : CommRing ℓ → Type ℓ
    isNilpCommRing A = isNilpRing (CommRing→Ring A)

    NilpCommRing : Type (ℓ-suc ℓ)
    NilpCommRing = Σ (CommRing ℓ) λ A → isNilpCommRing A 

  module Algebra (ℝ@(R , str) : CommRing ℓ) where
   
    open Ring ℝ

    isNilpCommAlgebra : CommAlgebra ℝ ℓ → Type ℓ
    isNilpCommAlgebra A = isNilpCommRing (CommAlgebra→CommRing A) 

    NilpCommAlgebra : Type (ℓ-suc ℓ)
    NilpCommAlgebra = Σ (CommAlgebra ℝ ℓ) λ A → isNilpCommAlgebra A 


  module WeilAlgebra (ℝ@(R , str) : CommRing ℓ) where

    open Algebra ℝ
    open Foundations ℝ
    private
      _⊕_ = pointwiseAlgebra
    isWeilAlgebra : CommAlgebra ℝ ℓ → Type (ℓ-suc ℓ)
    isWeilAlgebra A = ∃ NilpCommAlgebra λ N → Iso ⟨ A ⟩ ⟨ R ⊕ (fst N) ⟩
    WeilAlgebra : Type (ℓ-suc ℓ)
    WeilAlgebra = Σ (CommAlgebra ℝ ℓ) λ A → isWeilAlgebra A
    FPWeilAlgebra : Type (ℓ-suc ℓ)
    FPWeilAlgebra = Σ (FPAlgebra) λ A → isWeilAlgebra (fst A)
    FPWeilAlgebra→WeilAlgebra : FPWeilAlgebra → WeilAlgebra
    FPWeilAlgebra→WeilAlgebra W = (FPAlg→CommAlgebra (fst W)) , snd W
  module Properties (ℝ@(R , str) : CommRing ℓ) where

    open Nilradical ℝ
    open Ring ℝ
    
    nilpInNilrad : (x : R) → x ∈ (fst nilradical) ≡ isNilpotent x
    nilpInNilrad x = refl 


  module Instances (ℝ@(R , str) : CommRing ℓ) where

    open Foundations
    standard : (n : ℕ) → FinVec ℕ n → CommAlgebra ℝ ℓ
    standard n r = makeFPAlgebra {m = n} n (N r)
      where
        N : {n : ℕ} → FinVec ℕ n → Fin n → ⟨ freeAlgebra n ⟩ -- nilpotent orthotope  
        N r = exp-var-vec ℝ r               -- ∀ i : Fin n → gives ξᵢ^(r i)

    R[ε] = standard 1 λ x → 2

    