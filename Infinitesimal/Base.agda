{-# OPTIONS --cubical --safe #-}

module SDG.Infinitesimal.Base where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.Algebra
  open import Cubical.Data.Sigma
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_)
  
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.HITs.PropositionalTruncation
  open import Cubical.Data.Bool
  open import SDG.Base
  open import SDG.Nilpotent.Base


  module Spectrum (ℝ@(R , str) : CommRing ℓ) where
    
    open Foundations ℝ
    
    Spec : CommAlgebra ℝ ℓ → Type ℓ
    Spec X = CommAlgebraHom X A
    SpecFPAlgebra : FPAlgebra → Type ℓ
    SpecFPAlgebra X = Spec (FPAlg→CommAlgebra X)

    -- Spec is a covariant functor
    SpecF : {X Y : CommAlgebra ℝ ℓ} (f : CommAlgebraHom X Y) → (Spec Y → Spec X)  
    SpecF f = λ g → (fst g ∘ fst f) , compIsAlgebraHom (snd g) (snd f)

    -- Spec sends sections to retracts
    SpecSectToRetract : {X Y : CommAlgebra ℝ ℓ} →
            (g : CommAlgebraHom X Y) →
            (f : CommAlgebraHom Y X) →
            section (fst f) (fst g) → 
            hasRetract (SpecF {Y} {X} f)
    SpecSectToRetract {X} {Y} g f hS =  SpecF {X} {Y} g , 
                                        λ a → Σ≡Prop iPAH (funExt (λ z → cong (fst a) (hS z))) 
      where
        open IsAlgebraHom 
        compIsCommAlgebraHom : {A B C : CommAlgebra ℝ ℓ} 
            {g : ⟨ B ⟩ → ⟨ C ⟩} {f : ⟨ A ⟩ → ⟨ B ⟩}
            → IsCommAlgebraHom (B .snd) g (C .snd)
            → IsCommAlgebraHom (A .snd) f (B .snd)
            → IsCommAlgebraHom (A .snd) (g ∘ f) (C .snd)
        compIsCommAlgebraHom = compIsAlgebraHom
        iPAH = isPropIsCommAlgebraHom {ℓ} {ℝ} {ℓ} {X} {A}
    
    canMap : {X : CommAlgebra ℝ ℓ} → fst X → (Spec X → ⟨ A ⟩)
    canMap x d = fst d x

  module Types (ℝ@(R , str) : CommRing ℓ) where

    open WeilAlgebra ℝ
    open Spectrum ℝ
    isInfinitesimal : Type ℓ → Type (ℓ-suc ℓ)
    isInfinitesimal X = ∃ WeilAlgebra λ W → Iso X (Spec (fst W))
    InfinitesimalType : Type (ℓ-suc ℓ)
    InfinitesimalType = Σ (Type ℓ) λ X → isInfinitesimal X

  module Disk (ℝ@(R , str) : CommRing ℓ) where

    open Ring ℝ
    open RingTheory (CommRing→Ring ℝ)
    open Spectrum ℝ
    open Instances ℝ
    open Foundations ℝ
    
    DskOfOrder : (n : ℕ) → Type ℓ
    DskOfOrder n = Σ R (λ d → isNilpOfOrder d n)
    DskOfOrderProp : (n : ℕ) → Type ℓ
    DskOfOrderProp n = Σ R (λ d → isNilpOfOrderProp d n)
    DskOfOrder∞ : Type ℓ
    DskOfOrder∞ = Σ R λ d → isNilpotent d
    Dsk : Type ℓ
    Dsk = Spec R[ε]
    0D : DskOfOrder∞
    0D = 0r , ∣ 1 , (0LeftAnnihilates 1r) ∣

    disksInclusion : (n : ℕ) → DskOfOrder n → DskOfOrder (suc n)
    disksInclusion n d = (fst d) , (cong (λ a → (fst d) · a) (snd d) ∙ (0RightAnnihilates (fst d))) --map (λ a → (cong (λ z → (fst d) · z) {!   !} ∙ {!   !}) ∙ (0LeftAnnihilates ((fst d) ^ n))) ∣ fst d ∣
  
    
    --thm : Iso Dsk (DskOfOrder 2)
    --thm = {!   !}    