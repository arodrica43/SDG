{-# OPTIONS --cubical #-}

module SDG.KockLawvere.Base where

  open import Cubical.Foundations.Everything renaming (const to consts)
  open import Cubical.Data.FinData
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra renaming (_[_] to _⟦_⟧)
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_ ; 
                                          +-assoc to +-assocℕ ; +-comm to +-commℕ ;
                                          ·-assoc to ·-assocℕ ; ·-comm to ·-commℕ)
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
      KL1 : isIso canMap1
      KL : (n : ℕ) → isIso (canMap n)
      FKL : (n : ℕ) → isIso (fcanMap n)

    invMap :  (n : ℕ) → (Spec (W n) → ⟨ A ⟩) → ⟨ A[ξ] ⟩
    invMap n = fst (KL n)
    invMap1 :  (Spec (W 1) → ⟨ A ⟩) → ⟨ A[ξ] ⟩
    invMap1 = fst KL1
    finvMap : (n : ℕ) → (Spec (W n) → ⟨ A ⟩) → ⟨ W n ⟩
    finvMap n = fst (FKL n)

  module Derivative (ℝ@(R , str) : CommRing ℓ) where
    open Foundations ℝ
    open Construction ℝ
    d/dξ : ⟨ A[ξ] ⟩ → ⟨ A[ξ] ⟩
    d/dξ (const c) = 0a
    d/dξ (var i) = 1a
    d/dξ (p + q) = (d/dξ p) + (d/dξ q)
    d/dξ (- p) = - (d/dξ p)
    d/dξ (p · q) = ((d/dξ p) · q) + (p · (d/dξ q))
    d/dξ (+-assoc p q r i) = +-assoc (d/dξ p) ((d/dξ q)) ((d/dξ r)) i
    d/dξ (+-rid p i) = +-rid (d/dξ p) i
    d/dξ (+-rinv p i) = +-rinv (d/dξ p) i
    d/dξ (+-comm p q i) = +-comm (d/dξ p) (d/dξ q) i
    d/dξ (·-assoc p q r i) = (((d/dξ p · (q · r)) + (p · ((d/dξ q · r) + (q · d/dξ r)))) ≡⟨ cong (λ a → a + (p · ((d/dξ q · r) + (q · d/dξ r)))) (·-assoc (d/dξ p) q r) ⟩ 
                              (((d/dξ p · q ) · r) + (p · ((d/dξ q · r) + (q · d/dξ r)))) ≡⟨ cong (λ a → ((d/dξ p · q ) · r) + a) (·-comm p ((d/dξ q · r) + (q · d/dξ r))) ⟩ 
                              (((d/dξ p · q ) · r) + (((d/dξ q · r) + (q · d/dξ r)) · p)) ≡⟨ cong (λ a → ((d/dξ p · q ) · r) + a) (ldist (d/dξ q · r) (q · d/dξ r) p) ⟩ 
                              (((d/dξ p · q ) · r) + (((d/dξ q · r) · p) + ((q · d/dξ r) · p))) ≡⟨ +-assoc ((d/dξ p · q) · r) ((d/dξ q · r) · p) ((q · d/dξ r) · p) ⟩ 
                              ((((d/dξ p · q ) · r) + ((d/dξ q · r) · p)) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + a) + ((q · d/dξ r) · p)) (sym (·-assoc (d/dξ q) r p)) ⟩ 
                              ((((d/dξ p · q ) · r) + (d/dξ q · (r · p))) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + (d/dξ q · a)) + ((q · d/dξ r) · p)) (·-comm r p) ⟩ 
                              ((((d/dξ p · q ) · r) + (d/dξ q · (p · r))) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + a) + ((q · d/dξ r) · p)) (·-assoc (d/dξ q) p r) ⟩
                              ((((d/dξ p · q ) · r) + ((d/dξ q · p) · r)) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → a + ((q · d/dξ r) · p)) (sym (ldist (d/dξ p · q) (d/dξ q · p) r)) ⟩ 
                              ((((d/dξ p · q ) + (d/dξ q · p)) · r) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) + a) · r) + ((q · d/dξ r) · p)) (·-comm (d/dξ q) p) ⟩ 
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + a) (sym (·-assoc q (d/dξ r) p)) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · (d/dξ r · p))) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · a)) (·-comm (d/dξ r) p) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · (p · d/dξ r))) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + a) (·-assoc q p (d/dξ r)) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + ((q · p) · d/dξ r)) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + (a · d/dξ r)) (·-comm q p) ⟩
                              ((((d/dξ p · q) + (p · d/dξ q)) · r) + ((p · q) · d/dξ r)) ∎) i
    d/dξ (·-lid p i) = (((0a · p) + (1a · d/dξ p)) ≡⟨ cong (λ a → a + (1a · (d/dξ p))) (RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) p) ⟩ 
                        (0a + (1a · d/dξ p)) ≡⟨ (+-comm 0a (1a · d/dξ p)) ∙ (+-rid (1a · d/dξ p)) ⟩ 
                        (1a · d/dξ p) ≡⟨ ·-lid (d/dξ p) ⟩ 
                        d/dξ p ∎) i
    d/dξ (·-comm p q i) = ((d/dξ p · q) + (p · d/dξ q) ≡⟨ +-comm (d/dξ p · q) (p · d/dξ q) ⟩ 
                           (p · d/dξ q) + (d/dξ p · q) ≡⟨ cong (λ a → a + (d/dξ p · q)) (·-comm p (d/dξ q)) ⟩ 
                           (d/dξ q · p) + (d/dξ p · q) ≡⟨ cong (λ a → (d/dξ q · p) + a) (·-comm (d/dξ p) q) ⟩ 
                           (d/dξ q · p) + (q · d/dξ p) ∎) i
    d/dξ (ldist p q r i) = ((((d/dξ p + d/dξ q) · r) + ((p + q) · d/dξ r)) ≡⟨ cong (λ a → a + ((p + q) · d/dξ r)) (ldist (d/dξ p) (d/dξ q) r) ⟩ 
                            (((d/dξ p · r) + (d/dξ q · r)) + ((p + q) · d/dξ r)) ≡⟨ cong (λ a → ((d/dξ p · r) + (d/dξ q · r)) + a) (ldist p q (d/dξ r)) ⟩ 
                            (((d/dξ p · r) + (d/dξ q · r)) + ((p · d/dξ r) + (q · d/dξ r))) ≡⟨ +-assoc ((d/dξ p · r) + (d/dξ q · r)) (p · d/dξ r) (q · d/dξ r) ⟩ 
                            ((((d/dξ p · r) + (d/dξ q · r)) + (p · d/dξ r)) + (q · d/dξ r)) ≡⟨ cong (λ a → a + (q · d/dξ r)) (sym (+-assoc (d/dξ p · r) (d/dξ q · r) (p · d/dξ r))) ⟩ 
                            (((d/dξ p · r) + ((d/dξ q · r) + (p · d/dξ r))) + (q · d/dξ r)) ≡⟨ cong (λ a → ((d/dξ p · r) + a) + (q · d/dξ r)) (+-comm (d/dξ q · r) (p · d/dξ r)) ⟩ 
                            (((d/dξ p · r) + ((p · d/dξ r) + (d/dξ q · r))) + (q · d/dξ r)) ≡⟨ cong (λ a → a + (q · d/dξ r)) (+-assoc (d/dξ p · r) (p · d/dξ r) (d/dξ q · r)) ⟩ 
                            ((((d/dξ p · r) + (p · d/dξ r)) + (d/dξ q · r)) + (q · d/dξ r)) ≡⟨ sym (+-assoc ((d/dξ p · r) + (p · d/dξ r)) (d/dξ q · r) (q · d/dξ r)) ⟩ 
                            (((d/dξ p · r) + (p · d/dξ r)) + ((d/dξ q · r) + (q · d/dξ r))) ∎) i
    d/dξ (+HomConst s t i) = sym (+-rid 0a) i
    d/dξ (·HomConst s t i) = (0a ≡⟨ sym (+-rid 0a) ⟩ 
                              (0a + 0a) ≡⟨ cong (λ a → 0a + a) step1 ⟩ 
                              (0a + ((const s) · 0a)) ≡⟨ cong (λ a → a + ((const s) · 0a)) step2 ⟩ 
                              ((0a · (const t)) + ((const s) · 0a)) ∎) i
      where
        step1 : 0a ≡ (const s · 0a)
        step1 = sym (RingTheory.0RightAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) (const s))
        step2 : 0a ≡ 0a · (const t)
        step2 = sym (RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) (const t))
    d/dξ (0-trunc p q α β i j) = isSetCommAlgebra A[ξ] (d/dξ p) (d/dξ q) (cong d/dξ α) (cong d/dξ β) i j

    open Axiom ℝ

    factCoeff : (n : ℕ)(a : ⟨ A ⟩) → ⟨ A[ξ] ⟩ → ⟨ A ⟩
    factCoeff zero a p = evPoly A p (λ _ → a)
    factCoeff (suc n) a p = factCoeff n a (d/dξ p)

    d/dx : (n : ℕ)(f : ⟨ A ⟩ → ⟨ A ⟩) → ⟨ A ⟩ → ⟨ A ⟩
    d/dx n f a = factCoeff n a 
                          (invMap n (λ d → ((snd A) CommAlgebraStr.+ a) 
                                                                    (zeroLocus₁  1 
                                                                                (var-power n) 
                                                                                ((Iso.fun step1 ) d) 
                                                                                zero))) 
      where
        step1 : Iso (CommAlgebraHom (W n) A) (zeroLocus 1 (var-power n) A)
        step1 = FPHomIso 1 (var-power n)

    open InfExperimental ℝ
    d/dε : (n : ℕ) → ⟨ W (suc n) ⟩ → ⟨ W n ⟩  
    d/dε n x = ((fst (modRelations 1 (var-power n)) ∘ d/dξ) ∘ (fst (δ (suc n)))) x --((fst (modRelations 1 (var-power n)) ∘ d/dξ) ∘ fst (δ n)) x 
    
    ffactCoeff : (n : ℕ)(a : ⟨ A ⟩) → ⟨ W n ⟩ → ⟨ A ⟩
    ffactCoeff zero a p = evPoly A ((fst (δ zero)) p) (λ _ → a)
    ffactCoeff (suc n) a p = ffactCoeff n a (d/dε n p)
    
    -- Derivative using a traditional KL axiom 
    d/dz : (n : ℕ)(f : ⟨ A ⟩ → ⟨ A ⟩) → ⟨ A ⟩ → ⟨ A ⟩
    d/dz n f x = ffactCoeff n x 
                          (finvMap n (λ d → ((snd A) CommAlgebraStr.+ x) (zeroLocus₁ 1 (var-power n) ((Iso.fun step1 ) d) zero)))
      where
        step1 : Iso (CommAlgebraHom (W n) A) (zeroLocus 1 (var-power n) A)
        step1 = FPHomIso 1 (var-power n)