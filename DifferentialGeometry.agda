{-# OPTIONS --cubical #-}

module SDG.DifferentialGeometry where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.CommRing
  open import SDG.InfinitesimalObjects

  private
    variable
      ℓ : Level

  module _ {k : CommRing ℓ} where
  
    TangentSpace : Type ℓ → Type ℓ
    TangentSpace X = Disk {ℓ} {k} → X

    Tangent-space-of_at_ : (X : Type ℓ) → (x : X) → Type ℓ
    Tangent-space-of X at x = Σ (Disk {ℓ} {k} → X) (λ f → f (0D {ℓ} {k}) ≡ x) -- Tangent vectors are terms of this type

    VecField : (X : Type ℓ) → Type ℓ
    VecField X = (x : X) → Tangent-space-of X at x

    first-DE : {X : Type ℓ} → VecField X → Type ℓ
    first-DE {X = X} F = (x : X) → F x ≡ ((λ d → x) , λ i → x)
 