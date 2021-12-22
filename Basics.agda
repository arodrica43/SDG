{-# OPTIONS --cubical #-}

module SDG.Basics where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Data.Nat

  private
    variable
      ℓ : Level

  module _ {k : CommRing {ℓ}} where
    k-as-type : Type ℓ
    k-as-type = fst k
    
   -- _·ₖ_ = CommRingStr._·_

    0r =  CommRingStr.0r (snd k)
    1r =  CommRingStr.1r (snd k)
    
    _*_ : k-as-type → k-as-type → k-as-type
    x * y = (snd k CommRingStr.· x) y
    
    _^_ : k-as-type → ℕ → k-as-type
    x ^ zero = 1r
    x ^ suc n =  (x ^ n) * x

    D : ℕ → Type ℓ
    D n = Σ k-as-type λ x → x ^ n ≡ 0r
