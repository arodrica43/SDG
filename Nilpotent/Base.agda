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
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
    renaming (inducedHom to freeInducedHom)
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

    open Foundations ℝ
    nilpotency : R → Type ℓ
    nilpotency  x = Σ[ n ∈ ℕ ] (ℝ Exponentiation.^ x) n ≡ CommRingStr.0r str
    isNilpotent : R → Type ℓ
    isNilpotent x = ∥ nilpotency x ∥₁
    isNilpOfOrder : R → ℕ → Type ℓ
    isNilpOfOrder x n = (ℝ Exponentiation.^ x) n ≡ CommRingStr.0r str
    isNilpOfOrderProp : R → ℕ → Type ℓ
    isNilpOfOrderProp x n = ∥ isNilpOfOrder x n ∥₁

    isNilpotentAlg : ⟨ A ⟩ → Type ℓ
    isNilpotentAlg x = ∃[ n ∈ ℕ ] x ^a n ≡ CommAlgebraStr.0a (snd A)
    isNilpOfOrderAlg : ⟨ A ⟩ → ℕ → Type ℓ
    isNilpOfOrderAlg x n = x ^a n ≡  CommAlgebraStr.0a (snd A)
    isNilpOfOrderPropAlg : ⟨ A ⟩ → ℕ → Type ℓ
    isNilpOfOrderPropAlg x n = ∥ isNilpOfOrderAlg x n ∥₁
    
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

  module NilpAlgebra (ℝ@(R , str) : CommRing ℓ) where

    open Foundations ℝ

    nilpotency : {A : CommAlgebra ℝ ℓ} → ⟨ A ⟩ → Type ℓ
    nilpotency {A} x = Σ[ n ∈ ℕ ] evPoly {ℓ} {ℝ} {1} A (exp-var zero n) (λ _ → x) ≡ CommAlgebraStr.0a (snd A)
    isNilpOfOrder : {A : CommAlgebra ℝ ℓ} → ⟨ A ⟩ → ℕ → Type ℓ
    isNilpOfOrder {A} x n = evPoly {ℓ} {ℝ} {1} A (exp-var zero n) (λ _ → x) ≡ CommAlgebraStr.0a (snd A)
    


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
    FPWeilAlgebra = Σ (FPA) λ A → isWeilAlgebra (fst A)
    FPWeilAlgebra→WeilAlgebra : FPWeilAlgebra → WeilAlgebra
    FPWeilAlgebra→WeilAlgebra W = (FPAlg→CommAlgebra (fst W)) , snd W
  module Properties (ℝ@(R , str) : CommRing ℓ) where

    open Nilradical ℝ
    open Ring ℝ
    
    nilpInNilrad : (x : R) → x ∈ (fst nilradical) ≡ isNilpotent x
    nilpInNilrad x = refl 


  module NilpotentInstances (ℝ@(R , str) : CommRing ℓ) where

    open Foundations
    standard : (n : ℕ) → FinVec ℕ n → CommAlgebra ℝ ℓ
    standard n r = FPAlgebra n (N r)
      where
        N : {n : ℕ} → FinVec ℕ n → Fin n → ⟨ Polynomials n ⟩ -- nilpotent orthotope  
        N r = exp-var-vec ℝ r               -- ∀ i : Fin n → gives ξᵢ^(r i)

    R[ε] = standard 1 λ x → 2

    
  module Experimental (ℝ@(R , str) : CommRing ℓ) where

    open Foundations ℝ

    p0 : ⟨ Polynomials {ℓ} {ℝ} 1 ⟩
    p0 = exp-var zero 0
    evPolyChar0 : (A : CommAlgebra ℝ ℓ) → (v : FinVec ⟨ A ⟩ 1) → evPoly A p0 v ≡ CommAlgebraStr.1a (snd A)
    evPolyChar0 A v = evPoly A p0 v ≡⟨ cong (λ P → evPoly A P v) helper ⟩ 
                      evPoly {ℓ} {ℝ} {1} A (Construction.1a ℝ) v ≡⟨ CommAlgebraStr.⋆-lid (snd A) (CommAlgebraStr.1a (snd A)) ⟩ 
                      CommAlgebraStr.1a (snd A) ∎
      where
        helper : exp-var {1} zero 0 ≡ Construction.1a ℝ
        helper = refl

    evPolyChar : (A : CommAlgebra ℝ ℓ) →(n : ℕ) → (v : FinVec ⟨ A ⟩ 1) → evPoly A (gen n) v ≡ exp-num {A} (v zero) n
    evPolyChar A zero = evPolyChar0 A
    evPolyChar A (suc n) v = evPoly A (gen (suc n)) v                                                       ≡⟨ cong (λ P → evPoly A P v) helper1 ⟩ 
                             evPoly A ((ξ zero) Construction.· (gen n)) v                                   ≡⟨ IsAlgebraHom.pres· (snd (freeInducedHom A v)) (ξ zero) (gen n) ⟩ 
                             ((snd A) CommAlgebraStr.· evPoly A ( ξ {1} zero) v) (evPoly A (gen n) v)  ≡⟨ refl ⟩ 
                             ((snd A) CommAlgebraStr.· (v zero)) (evPoly A (gen n) v)                                 ≡⟨ cong (λ a → ((snd A) CommAlgebraStr.· (v zero)) a) (evPolyChar A n v) ⟩ 
                             exp-num {A} (v zero) (suc n) ∎
      where
        helper1 : exp-var {1} zero (suc n) ≡ ((ξ zero) Construction.· (gen n))
        helper1 = refl

    -- TO DO ::
    -- 1 ::
    -- Show that every P : Polynomials 1 is a linear combination of a finite number of generators "exp-var zero n" in Polynomials n
    -- Show that evalPoly of P at x is a linear combination (induced by the previous one) of powers of x
    -- 2 ::
    -- Show that every element in W n is a linear combination of the generator powers ε^k
