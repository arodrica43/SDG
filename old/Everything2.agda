{-# OPTIONS --cubical --safe #-}

module SDG.Everything2 where

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.HITs.Nullification
open import Cubical.HITs.SetQuotients renaming (_/_ to _//_)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Modalities.Modality
open import Cubical.Algebra.RingSolver.Reflection
open import SDG.ISM.ModalConnected2 


private
    variable
        ℓ : Level

module _ (Ring@(R , str) : CommRing ℓ) where

    open Exponentiation Ring
    open CommRingStr str
    open RingTheory (CommRing→Ring Ring)
    open RadicalIdeal
    open CommIdeal Ring
    open isCommIdeal

    nilpPath : R → ℕ → Type ℓ
    nilpPath x n = x ^ n ≡ 0r
    isNilpotent : R → Type ℓ
    isNilpotent x = ∃[ n ∈ ℕ ] nilpPath x n
    CommIdeal→Ideal : CommIdeal → IdealsIn Ring
    CommIdeal→Ideal I = makeIdeal Ring (fst I) (+Closed (snd I)) (contains0 (snd I)) (·Closed (snd I))
    nilradical : CommIdeal
    nilradical = √ Ring 0Ideal 
    R/nilr : CommRing ℓ
    R/nilr = Ring / CommIdeal→Ideal nilradical

    -- Type of nilpotents of R (i.e. formal disk)
    Dsk : Type ℓ
    Dsk = Σ R λ x → isNilpotent x
    ι : Dsk → R
    ι = fst
    0D : Dsk
    0D = 0r , ∣ 1 , (0LeftAnnihilates 1r) ∣

    D : (n : ℕ) → Type ℓ
    D n = Σ R λ x → nilpPath x n

    ISM : Modality ℓ
    ISM = NullModality Dsk
    open Modality ISM

    ism : (n : ℕ) → Modality ℓ
    ism n = NullModality (D n)
    pre-η-has-contr-img : {S A : Type ℓ} → (f : S → Null S A) → (x y : S) → f x ≡ f y 
    pre-η-has-contr-img f x y i = ((sym (spoke f x)) ∙ spoke f y) i

-- Development

    thm0 : {S : Type ℓ}(f : R → S)(x : R) → 
            Σ (fst R/nilr → S) λ g → (g ∘ [_]) x ≡ f x
    thm0 f x = (λ z → f x) , refl
    isInNilr : (x : R) → Σ (Type ℓ) (isOfHLevel 1)
    isInNilr = fst nilradical
    lem1 : (x : R) → x ∈ nilradical ≡ isNilpotent x
    lem1 x = refl
    lem2 : (x : R) → fst (isInNilr x) ≡ isNilpotent x
    lem2 x = refl

    restr : {X : Type ℓ}(f : R → X) → (Dsk → X)
    restr f = f ∘ ι
    lem3 : {X : Type ℓ}(f : R → ◯ X)(d : Dsk) → (restr f) d ≡ f 0r
    lem3 f d = pre-η-has-contr-img (restr f) d 0D

    lem4 : (f : Dsk → R)(x : Dsk) → [ f x ] ≡ [ f 0D ]
    lem4 f x = eq/ (f x) (f 0D) (snd x)
  

    lem5 : Iso (fst R/nilr) (Dsk → fst R/nilr)
    Iso.fun lem5 = λ x _ → x
    Iso.inv lem5 f = f 0D
    Iso.rightInv lem5 = λ f → funExt λ x → ((sym (snd (thm0 (λ _ → f 0D) 0r))) ∙ lem f x) ∙ (snd (thm0 (λ z → f x) (ι x)))
        where
            lem : (f : Dsk → fst R/nilr)(x : Dsk) → f 0D ≡ f x -- We are doing loops
            lem f x = {!   !}
    Iso.leftInv lem5 = λ a → refl
    -- thm1 : Iso (◯ R) (◯ (fst R/nilr))
    -- thm1 = ◯-connectedTruncIso lem3
    --     where
    --         lem4 : (y : fst R/nilr) → fiber [_] y
    --         lem4 y = {!   !}
    --         lem3 : ◯-isConnMap {ℓ} {R} {fst R/nilr} {Dsk} {[_]} [_]
    --         lem3 = λ y → (η ((fst (thm0 (λ x → {!   !}) 0r)) y)) , {!   !}
    -- thm1 : isModal (fst R/nilr)
    -- thm1 = record { sec = (λ f → f 0D) , 
    --                       λ b → {!   !} ; 
    --                 secCong = λ x y → (λ p i → p i 0D) , λ b → λ i i₁ x₁ → b i₁ (cong (λ f → f 0D) refl i) } 

    -- thm1 : Iso (fst R/nilr) (Dsk → fst R/nilr)
    -- Iso.fun thm1 = λ x _ → x
    -- Iso.inv thm1 = λ f → f 0D
    -- Iso.rightInv thm1 = λ b → funExt (lem1/1 b)
    --     where
    --         lem1/1 : (b : Dsk → fst R/nilr) → (x : Dsk) → b 0D ≡ b x
    --         lem1/1 b (x , ∣ p ∣) = λ i → eq/ {!   !} {!   !} {!   !} {! i  !}
    --         lem1/1 b (fst₁ , squash snd₁ snd₂ i) = {!   !}
    -- Iso.leftInv thm1 = λ a i → a     