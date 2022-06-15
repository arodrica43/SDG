
{-# OPTIONS --cubical --safe #-}

module SDG.Infinitesimals.Instances where

  open import Cubical.Foundations.Everything

  open import Cubical.Data.Nat
  open import Cubical.Data.FinData
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Relation.Nullary
  open import Cubical.Algebra.CommRingSolver.Utility
  
  open import SDG.Base
  open import SDG.WeilAlgebra.Instances

  module 1Disk (ℝ@(R , str) : CommRing ℓ) where
  
    -- / The disk of order n is the zero locus of the generator of the quotient algebra A[ξ]/(ξ^n), which is isomorphic to 
    -- / Spec(X) := CommAlgebraHom X A (where A is ℝ as algebra)

    open 1DFreeCommAlgebraUtils ℝ
    open AlgebraUtils ℝ
  
    infDskOfOrder : (A : CommAlgebra ℝ ℓ)(n : ℕ) → Type ℓ
    infDskOfOrder A n = zeroLocus 1 (var-power n) A 

    infDskOfOrder∞ : (A : CommAlgebra ℝ ℓ) → Type ℓ
    infDskOfOrder∞ A = Σ[ n ∈  ℕ ] infDskOfOrder A n

    0d : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder A n
    0d A n = makeZeroLocusTerm 1 (var-power n) A (λ _ → 0a) λ i → 
              evPoly A (gen (suc n)) (λ _ → 0a)             ≡⟨ evPolyChar A (suc n) (λ _ → 0a) ⟩ 
              exp A 0a (suc n)                                        ≡⟨ refl ⟩ 
              ((snd A) CommAlgebraStr.· 0a) (exp A 0a n)                  ≡⟨ RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A)) (exp A 0a n) ⟩ 
              0a                                                        ∎
           
      where
        open CommAlgebraStr (snd A)

    incl : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder A n → infDskOfOrder∞ A
    incl A n d = n , d

    retr : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder∞ A → infDskOfOrder A n
    retr A n (m , d) with discreteℕ m n
    ... | yes p = transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc (p i))) A) d
    ... | no ¬p = 0d A n

    isRetrRetr : (k : ℕ)(A : CommAlgebra ℝ ℓ) → (d : infDskOfOrder A k) → (retr A k ∘ (incl A k)) d ≡ d
    isRetrRetr k A d with discreteℕ k k 
    ... | yes p = transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc (p i))) A) d     ≡⟨ cong (λ a → transport a d) 
                                                                                                    (λ i → cong (λ a → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc a)) A) 
                                                                                                                (isSetℕ k k p refl i)) ⟩ 
                  transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc k)) A) d         ≡⟨ transportRefl d ⟩ 
                  d                                                                         ∎
    ... | no ¬p = byAbsurdity (¬p refl)    

    open 1DFundamentalWeilAlgebras ℝ
    evPolyInfinitesimal : (n : ℕ) → (A : CommAlgebra ℝ ℓ) → ⟨ W n ⟩ → FinVec (infDskOfOrder A n) 1 → ⟨ A ⟩
    evPolyInfinitesimal n A P values = (fst (inducedHomFP 1 (var-power n) A (values zero))) P  -- fst (freeInducedHom A values) P


 