{-# OPTIONS --cubical #-}
module SDG.ISM.Properties2 where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommRing.Ideal
  open import Cubical.Foundations.Everything
  open import Cubical.Modalities.Modality
  open import Cubical.Homotopy.Connected
  open import Cubical.Data.Unit
  open import Cubical.Data.Nat
  open import Cubical.Data.Sigma
  --open import Cubical.Algebra.CommRing.QuotientRing
  open import Cubical.HITs.TypeQuotients
  open import Cubical.HITs.PropositionalTruncation
  open import SDG.Base
  open import SDG.Nilpotent
  open import SDG.InfinitesimalObjects
  open import SDG.ISM.Base
  open import Cubical.Algebra.RingSolver.Reflection
  
  variable
    ℓ : Level
  
  module _ {k : CommRing ℓ} where
    open Foundations {ℓ} {k}
    open BaseFoundations {ℓ} {k}
    private
        Dsk = D∞ {ℓ} {k}
        ∗ = Unit* {ℓ}
        Dsk-pt = D∞-pt {ℓ} {k}      
    


    -- nilradical : IdealsIn k
    -- nilradical = makeIdeal k (λ x → (∃[ n ∈ ℕ ] x ^ n ≡ 0r) , squash) 
    --                                 (λ x y → ∣ {!   !} , {!   !} ∣)
    --                                 ∣ z ∣ 
    --                                 λ r x → ∣ {! n  !} , {! x  !} ∣
    --     where
    --         z : Σ ℕ (λ n → (CommRingStr.0r (snd k) ^ n) ≡ 0r)
    --         z = 1 , {!   !}
            

    nilrad : fst k → fst k → Type ℓ
    nilrad = λ x y → Σ ℕ (λ n → ((snd k) CommRingStr.- x) y ^ n ≡ 0r)

    lem1 : Iso  (ℑ (fst k)) ((fst k) /ₜ nilrad)
    Iso.fun lem1 x = {!   !}
    Iso.inv lem1 x = η (Cubical.HITs.TypeQuotients.rec {!   !} {!   !} x)
    Iso.rightInv lem1 = {!   !}
    Iso.leftInv lem1 = {!   !} 
      
    
    -- private
    --   η = Modality.η ◯-asModality
    --   ◯ = Modality.◯ ◯-asModality
    --   ◯-Type = Modality.◯-Types ◯-asModality
    -- ℑ-connectedness
    -- ◯-connType : (X : Type ℓ) → Type ℓ
    -- ◯-connType X = isContr (◯ X) 
    -- ◯-connMap : {X Y : Type ℓ} → (f : X → Y) → Type ℓ
    -- ◯-connMap {Y = Y} f = (y : Y) → ◯-connType (fiber f y)   