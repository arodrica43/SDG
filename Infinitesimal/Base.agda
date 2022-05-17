{-# OPTIONS --cubical --safe --inversion-max-depth=200 #-}

module SDG.Infinitesimal.Base where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.Algebra
  open import Cubical.Data.Sigma
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_ ; _^_ to _^ℕ_ )
  open import Cubical.Data.FinData
  
  open import Cubical.Algebra.Ring
  
  open import Cubical.Algebra.Ring.Kernel
  open import Cubical.Algebra.CommRing.Ideal renaming (IdealsIn to IdealsInRing)
  open import Cubical.Algebra.Ring.Ideal
  open import Cubical.Algebra.CommRing.FGIdeal
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Module
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
  open import Cubical.HITs.SetQuotients
  open import Cubical.HITs.PropositionalTruncation
  open import Cubical.Foundations.Powerset renaming (_∈_ to _∈p_)
  open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
  open import Cubical.Algebra.CommRingSolver.Utility
  open import Cubical.Relation.Nullary
  open import SDG.Base
  open import SDG.Nilpotent.Base


  module Spectrum (ℝ@(R , str) : CommRing ℓ) where
    
    open Foundations ℝ
    open AlgebraHoms
    Spec : CommAlgebra ℝ ℓ → Type ℓ
    Spec X = CommAlgebraHom X A
    SpecFPAlgebra : FPA → Type ℓ
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
        iPAH = isPropIsCommAlgebraHom {ℓ} {ℝ} {ℓ} {ℓ} {X} {A}

    fcanMap : (n : ℕ) → ⟨ W n ⟩ → (CommAlgebraHom (W n) A → ⟨ A ⟩ )
    fcanMap n p d = fst d p
    
    canMap : (n : ℕ) → ⟨ A[ξ] ⟩ → (CommAlgebraHom (W n) A → ⟨ A ⟩ )
    canMap n p d = fst d ((fst (modRelations 1 (var-power n))) p)

    canMap1 : ⟨ A[ξ] ⟩ → (CommAlgebraHom (W 1) A → ⟨ A ⟩ )
    canMap1 p d = fst d ((fst (modRelations 1 (var-power 1))) p)

  module Types (ℝ@(R , str) : CommRing ℓ) where

    open WeilAlgebra ℝ
    open Spectrum ℝ
    isInfinitesimal : Type ℓ → Type (ℓ-suc ℓ)
    isInfinitesimal X = ∃ WeilAlgebra λ W → Iso X (Spec (fst W))
    InfinitesimalType : Type (ℓ-suc ℓ)
    InfinitesimalType = Σ (Type ℓ) λ X → isInfinitesimal X

  module Disks (ℝ@(R , str) : CommRing ℓ) where
    open NilpAlgebra ℝ
    open Foundations ℝ
    
    diskOfOrder : {A : CommAlgebra ℝ ℓ} → (n : ℕ) → Type ℓ
    diskOfOrder {A} n = zeroLocus {ℓ} {ℝ} {1} 1 (λ i → exp-var i (suc n)) A
    diskOfOrder∞ : {A : CommAlgebra ℝ ℓ} → Type ℓ
    diskOfOrder∞ {A} = Σ[ n ∈ ℕ ] zeroLocus {ℓ} {ℝ} {1} 1 (λ i → exp-var i (suc n)) A
    --0d : {A : CommAlgebra ℝ ℓ} → (n : ℕ) → diskOfOrder {A} n
    --0d {A} n = evaluateAtFP 1 (λ i → exp-var i (suc n)) (inducedHomFP 1 (λ i → exp-var i (suc n)) A {!   !})

  module Disk (ℝ@(R , str) : CommRing ℓ) where

    open Ring ℝ
    open RingTheory (CommRing→Ring ℝ)
    open Spectrum ℝ
    open NilpotentInstances ℝ
    open Foundations ℝ
    open CommRingStr str
    DskOfOrder : (n : ℕ) → Type ℓ
    DskOfOrder n = Σ R (λ d → isNilpOfOrder d (suc n))
    DskOfOrderProp : (n : ℕ) → Type ℓ
    DskOfOrderProp n = Σ R (λ d → isNilpOfOrderProp d n)
    DskOfOrder2Prop : Type ℓ
    DskOfOrder2Prop = Σ (fst A) λ x → isNilpOfOrderPropAlg x 2
    DskOfOrder∞ : Type ℓ
    DskOfOrder∞ = Σ R λ d → isNilpotent d
    bigDskOfOrder∞ : Type ℓ
    bigDskOfOrder∞ = Σ R λ d → nilpotency d
    
    Dsk : Type ℓ
    Dsk = Spec R[ε]
    0D : DskOfOrder∞
    0D = 0r , ∣ 1 , (0LeftAnnihilates 1r) ∣
    0d : (n : ℕ) → DskOfOrder n
    0d n = 0r , ((0r ^ suc n) ≡⟨ refl ⟩ (0r · (0r ^ n)) ≡⟨ 0LeftAnnihilates (0r ^ n) ⟩ 0r ∎)
    incl : (n : ℕ) → DskOfOrder n → bigDskOfOrder∞
    incl n d = (fst d) , ((suc n) , snd d )
    retr : (n : ℕ) → bigDskOfOrder∞ → DskOfOrder n
    retr n (d , (m , d^m≡0)) with discreteℕ m (suc n)
    ... | yes p = d , ((d ^ (suc n)) ≡⟨ cong (λ k → d ^ k) (sym p) ⟩ (d ^ m) ≡⟨ d^m≡0 ⟩ 0r ∎)
    ... | no ¬p = 0d n
  
  
    k = 1 
    isRetrRetr : (x : DskOfOrder k) → ((retr k) ∘ (incl k)) x ≡ x
    isRetrRetr (d , d^2≡0) = (retr k ∘ incl k) (d , d^2≡0)  ≡⟨ refl ⟩ 
                                  retr k (d , ((suc k) , d^2≡0))    ≡⟨ refl ⟩ 
                                  d , _                     ≡⟨ Σ≡Prop (λ x → isSetCommRing ℝ (x ^ (suc k)) 0r) refl ⟩
                                  d , d^2≡0 ∎

  module InfExperimental (ℝ@(R , str) : CommRing ℓ) where

    open Experimental ℝ
    open Foundations ℝ

  
    infDskOfOrder : (A : CommAlgebra ℝ ℓ)(n : ℕ) → Type ℓ
    infDskOfOrder A n = zeroLocus {m = 1} 1 (λ _ → gen (suc n)) A

    infDskOfOrder∞ : (A : CommAlgebra ℝ ℓ) → Type ℓ
    infDskOfOrder∞ A = Σ[ n ∈  ℕ ] infDskOfOrder A n

    0d : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder A n
    0d A n = buildInZeroLocus 1 (λ _ → gen (suc n)) (λ _ → 0a) λ i → 
              evPoly A (gen (suc n)) (λ _ → 0a)                         ≡⟨ evPolyChar A (suc n) (λ _ → 0a) ⟩ 
              exp-num {A} 0a (suc n)                                        ≡⟨ refl ⟩ 
              ((snd A) CommAlgebraStr.· 0a) (exp-num 0a n)                  ≡⟨ RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A)) (exp-num 0a n) ⟩ 
              0a                                                        ∎
      where
        open CommAlgebraStr (snd A)

    incl : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder A n → infDskOfOrder∞ A
    incl A n d = n , d

    retr : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder∞ A → infDskOfOrder A n
    retr A n (m , d) with discreteℕ m n
    ... | yes p = transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc (p i))) A) d
    ... | no ¬p = 0d A n
 
    
    module prova (n : ℕ) where
      k = 3
      isRetrRetr : (A : CommAlgebra ℝ ℓ) → (d : infDskOfOrder A k) → (retr A k ∘ (incl A k)) d ≡ d
      isRetrRetr A d = (retr A k ∘ incl A k) d ≡⟨ refl ⟩ 
                      retr A k (k , d) ≡⟨ refl ⟩ 
                      transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc k)) A) d ≡⟨ transportRefl d ⟩ 
                      d ∎
    
    isRetrRetrG : (k : ℕ)(A : CommAlgebra ℝ ℓ) → (d : infDskOfOrder A k) → (retr A k ∘ (incl A k)) d ≡ d
    isRetrRetrG k A d with discreteℕ k k 
    ... | yes p = transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc (p i))) A) d     ≡⟨ cong (λ a → transport a d) 
                                                                                                    (λ i → cong (λ a → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc a)) A) 
                                                                                                                (isSetℕ k k p refl i)) ⟩ 
                  transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc k)) A) d         ≡⟨ transportRefl d ⟩ 
                  d                                                                         ∎
    ... | no ¬p = byAbsurdity (¬p refl)                             

    δ : (k : ℕ) → CommAlgebraHom (W k) A[ξ]
    δ k = Iso.inv (FPHomIso 1 (var-power k)) (0d A[ξ] k) 
