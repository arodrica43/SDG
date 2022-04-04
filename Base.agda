{-# OPTIONS --cubical --safe #-}

module SDG.Base where

  open import Cubical.Foundations.Everything renaming (const to cons)
  open import Cubical.Data.FinData
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.Instances.FreeCommAlgebra 
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
  open import Cubical.Algebra.Ring.BigOps
  open import Cubical.Data.Fin.LehmerCode

  variable
    ℓ : Level

  module Foundations (ℝ@(R , str) : CommRing ℓ) where

    open Exponentiation ℝ public
    open CommRingStr str public
    open RingTheory (CommRing→Ring ℝ)
    open Construction ℝ renaming (_·_ to _·A_ ; _+_ to _+A_)

    A = freeAlgebra {ℓ} {ℝ} 0    
    R→A : R → ⟨ A ⟩
    R→A x = const x

    ξ : {n : ℕ} → Fin n → fst (freeAlgebra {ℓ} {ℝ} n)
    ξ i = var i
    exp-var : {n : ℕ} → Fin n → ℕ → fst (freeAlgebra {ℓ} {ℝ} n)
    exp-var i zero = 1a
    exp-var i (suc n) = (ξ i) ·A (exp-var i n)
    exp-var-vec : {n : ℕ} → FinVec ℕ n →  FinVec (fst (freeAlgebra {ℓ} {ℝ} n)) n
    exp-var-vec r = λ i → exp-var i (r i)
    constant :  {n : ℕ} → R → fst (freeAlgebra {ℓ} {ℝ} n)
    constant a = const a
    monomial : {n : ℕ} → R → Fin n → ℕ → fst (freeAlgebra {ℓ} {ℝ} n)
    monomial a i n = (constant a) ·A (exp-var i n)

    open Sum (CommRing→Ring ℝ)
    polynomialAt : {n : ℕ} → FinVec R n → R → R
    polynomialAt v a = ∑ (λ i → ((snd ℝ) CommRingStr.· (v i)) (a ^ toℕ i))

    series_TruncAt : (n : ℕ) → (ℕ → R) → R → R
    series n TruncAt a x = ∑ {n} serie
      where
        serie : (n : Fin _) → R
        serie n = (str CommRingStr.+ (a (toℕ n))) (x ^ toℕ n)
   
    FPAlgebra : Type (ℓ-suc ℓ)
    FPAlgebra = Σ (CommAlgebra ℝ ℓ) λ A → isFPAlgebra A

    FPAlg→CommAlgebra : FPAlgebra → CommAlgebra ℝ ℓ
    FPAlg→CommAlgebra X = fst X
    
    embedℕinRing : ℕ → R
    embedℕinRing zero = 0r
    embedℕinRing (suc n) = (embedℕinRing n) + 1r


  