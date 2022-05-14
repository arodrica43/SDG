{-# OPTIONS --cubical #-}

module SDG.KockLawvere.Base where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.FinData
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommRing.QuotientRing
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra renaming (_[_] to _⟦_⟧)
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
  open import Cubical.Data.Sigma
  open import Cubical.Algebra.Ring.BigOps
  open import Cubical.HITs.SetQuotients renaming (_/_ to _//_)
  open import Cubical.Data.Fin.LehmerCode 
  open import SDG.Base
  open import SDG.Nilpotent.Base
  open import SDG.Infinitesimal.Base


  module Axiom (ℝ@(R , str) : CommRing ℓ) where

    open Foundations ℝ
    open Spectrum ℝ
    open WeilAlgebra ℝ
    postulate
      KL : (W : WeilAlgebra) → isIso (canMap {fst W})

    invMap :  (W : WeilAlgebra) → (Spec (fst W) → ⟨ A ⟩) → ⟨ fst W ⟩
    invMap W = fst (KL W)

  module Derivative (ℝ@(R , str) : CommRing ℓ) where
    open Axiom ℝ
    open Foundations ℝ
    d/dx : (n : ℕ)(f : R → R) → R → R
    d/dx n f a = (embedℕinRing (factorial n)) · {!   !}