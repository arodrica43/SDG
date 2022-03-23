{-# OPTIONS --cubical --safe #-}

module SDG.Everything where

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

    -- Proposition of being nilpotent
    isNilpotent : R → Type ℓ
    isNilpotent x = ∃[ n ∈ ℕ ] x ^ n ≡ 0r
    -- Type of nilpotents of R (i.e. formal disk)
    Dsk : Type ℓ
    Dsk = Σ R λ x → isNilpotent x
    ι : Dsk → R
    ι = fst
    0D : Dsk
    0D = 0r , ∣ 1 , (0LeftAnnihilates 1r) ∣

    -- Nilradical of Rl
    CommIdeal→Ideal : CommIdeal → IdealsIn Ring
    CommIdeal→Ideal I = makeIdeal Ring (fst I) (+Closed (snd I)) (contains0 (snd I)) (·Closed (snd I))
    nilradical : CommIdeal
    nilradical = √ Ring 0Ideal 
    R/nilr : CommRing ℓ
    R/nilr = Ring / CommIdeal→Ideal nilradical
    isInNilr : (x : R) → Σ (Type ℓ) (isOfHLevel 1)
    isInNilr = fst nilradical
    -- Nilradical is the set of nilpotents definitionally
--     prop1 : (x : R) → fst (isInNilr x) ≡ isNilpotent x
--     prop1 x = refl
--     prop2 : (d : Dsk) →  ι d ∈ nilradical
--     prop2 d = snd d
--     prop3 : (x : R) → x ∈ nilradical → Dsk
--     prop3 x p = x , p
--     prop4 : Iso (Σ R (λ x → x ∈ nilradical)) Dsk
--     Iso.fun prop4 = λ x → fst x , snd x
--     Iso.inv prop4 = λ x → fst x , snd x
--     Iso.rightInv prop4 = λ b → refl
--     Iso.leftInv prop4 = λ a → refl
--     --indeed this types are definitionally equal
--     prop5 : (Σ R (λ x → x ∈ nilradical)) ≡ Dsk
--     prop5 = refl

    thm1 : {S : Type ℓ}(f : R → S)(x : R) → 
            Σ (fst R/nilr → S) λ g → (g ∘ [_]) x ≡ f x
    thm1 f x = (λ z → f x) , refl

    thm1/1 : {S : Type ℓ}(f : Dsk → S)(x : Dsk) → 
            Σ (fst R/nilr → S) λ g → (g ∘ [_]) (ι x) ≡ f x
    thm1/1 f x = thm1  (λ z → f x) (ι x)
   
    -- thm1/1 : {S : Type ℓ}(f : R → S) → 
    --         Σ (fst R/nilr → S) λ g → ((x : R) → (g ∘ [_]) x ≡ f x)
    -- thm1/1 f = {! f  !} , λ x → {!   !}

    -- Infinitesimal shape modality as Nullification at Dsk 
    ISM : Modality ℓ
    ISM = NullModality Dsk
    open Modality ISM

    thm2 : {S : Type ℓ}(f : R → S)(x : R) → 
            Σ (◯ R → S) λ g → (g ∘ η) x ≡ f x
    thm2 f x = (λ z → f x) , refl --(λ z → f x) , refl 

    pre-η-has-contr-img : {S A : Type ℓ} → (f : S → Null S A) → (x y : S) → f x ≡ f y 
    pre-η-has-contr-img f x y i = ((sym (spoke f x)) ∙ spoke f y) i
    prov1 : (x y : R) → (x - y) ∈ nilradical → [ x ] ≡ [ y ]
    prov1 x y sC = eq/ {ℓ} {ℓ} {R} {λ a b → (x - y) ∈ nilradical} x y sC
    prov2 : (x y : R) → (x - y) ∈ nilradical → η (x - y) ≡ η 0r
    prov2 x y sC = pre-η-has-contr-img (η ∘ ι) ((x - y) , sC) 0D
    prov3 : (x : R) →  η x ≡ η 0r → Dsk
    prov3 x p = x , ∣ {!   !} , {! p  !} ∣

--     thm3 : Iso (◯ R) (◯ (fst R/nilr))
--     thm3 = ◯-connectedTruncIso {ℓ} {R} {fst R/nilr} {Dsk} {λ x → _} (isConnectedPrecompose lem1)
--         where 
--             lem2 : (P : fst R/nilr → ◯-Types) → Iso ((b : fst R/nilr) → P b .fst) ((b : R) → P [ b ] .fst)
--             Iso.fun (lem2 P) = λ x b → x [ b ]
--             Iso.inv (lem2 P) = λ x b → {!   !} --Cubical.HITs.SetQuotients.rec {! P  !} (λ z → {!  !}) {! P  !} b
--             Iso.rightInv (lem2 P) = {!   !}
--             Iso.leftInv (lem2 P) = {!   !}
--             lem1 : (P : fst R/nilr → ◯-Types) →
--                         hasSection (λ s → s ∘ λ v → _)
--             lem1 = λ P → isEquiv→hasSection (isoToIsEquiv (lem2 P))



    --/-has-contr-img : (x y : Dsk) → η x ≡ η y 
    --/-has-contr-img x y i = ?

      
--     lem1 : isModal (fst R/nilr)
--     lem1 = record { sec = (λ f → f 0D) , λ b → sol1 b ; 
--                     secCong = {!   !} }
--         where
--             help1 : (b : Dsk → fst R/nilr) (x : Dsk) → (fst (thm1/1 (λ x₁ → b x) x)) [ ι x ] ≡ b x
--             help1 b x = snd (thm1/1 (λ x₁ → b x) x)
--             help2 : (b : Dsk → fst R/nilr) → (fst (thm1/1 (λ x₁ → b 0D) 0D)) [ ι 0D ] ≡ b 0D
--             help2 b = help1 b 0D
--             help2/2 : (x : R) → Σ ℕ (λ n → (x - 0r) ^ n ∈ 0Ideal) ≡ Σ ℕ (λ n → (x - 0r) ^ n ≡ 0r)
--             help2/2 x = refl 
--             help2/1 : (x : R) → Σ ℕ (λ n → x ^ n ∈ 0Ideal) → Σ ℕ (λ n → (x - 0r) ^ n ∈ 0Ideal)
--             help2/1 x iN = (fst iN) , cong (_^ (fst iN)) ((cong (λ a → x + a) 0Selfinverse) ∙ +Rid x) ∙ (snd iN)
--             help3 : (x : Dsk) → [ ι x ] ≡ [ ι 0D ]
--             help3 x = eq/ (ι x) (ι 0D) ∣ help2/1 (ι x) (snd x) ∣
--             help1/1 : (b : Dsk → fst R/nilr) (x : Dsk) → (fst (thm1/1 (λ x₁ → b x) x)) [ ι x ] ≡ (fst (thm1/1 (λ x₁ → b x) x)) [ ι 0D ]
--             help1/1 b x = cong ((fst (thm1/1 (λ x₁ → b x) x))) (help3 x)
--             help4 : (b : Dsk → fst R/nilr) (x : Dsk) → (fst (thm1/1 (λ x₁ → b x) x)) [ ι x ] ≡ (fst (thm1/1 (λ x₁ → b 0D) 0D)) [ ι x ]
--             help4 b x = {!   !}
--             sol1/1 : (b : Dsk → fst R/nilr) (x : Dsk) → b 0D ≡ b x
--             sol1/1 b x = {!   !}
--             sol1 : (b : Dsk → fst R/nilr) → (λ _ → b 0D) ≡ b
--             sol1 b = funExt (sol1/1 b)
    -- -- We can construct a map from ◯ R to S = R/nilr, from the map f = [_]
    -- thm3 : (x : R) → Σ (◯ R → fst R/nilr) λ g → (g ∘ η) x ≡ [ x ]
    -- thm3 x = thm2 {R/nilr} [_] x
    -- -- Reciprocally
    -- thm4 : (x : R) → Σ (fst R/nilr → ◯ R) λ g → g [ x ] ≡ η x 
    -- thm4 x = thm1 {◯ R} η x --thm2 {R/nilr} [_] x

    -- g : (x : R) → (◯ R → R)
    -- g x = fst (thm2 {Ring} (idfun R) x)
    -- h : (x : R) → (fst R/nilr → R)
    -- h x = fst (thm1 (idfun R) x)
    -- fun : (x : R) → ◯ R → fst R/nilr
    -- fun x = [_] ∘ g x
    -- inv : (x : R) → (fst R/nilr → ◯ R)
    -- inv x = η ∘ (h x)
    -- thm5 : (x : R) → Iso (◯ R) (fst (R/nilr))
    -- Iso.fun (thm5 x) = fun x
    -- Iso.inv (thm5 x) = inv x
    -- Iso.rightInv (thm5 x) = λ b → sect b
    --     where
    --         sect : (b : fst (R/nilr)) → [ g x (η x) ] ≡ b
    --         sect b = cong {! f  !} (snd (thm1 [_] x))
    -- Iso.leftInv (thm5 x) = {!   !}
        
                        
    -- lem1 : (x : R) (b : fst R/nilr) → inv x b ≡ η x
    -- lem1 x b = refl
    -- lem2 : (x : R) (b : ◯ R) → fun x b ≡ [ x ]
    -- lem2 x b = refl
    -- lem3 : (x : R) (b : fst R/nilr) → fun x (inv x b) ≡ [ x ]
    -- lem3 x b = cong (fun x) (lem1 x b)


    -- thm5 : (x : R) → Iso (◯ R) (fst (R/nilr))
    -- Iso.fun (thm5 x) = fun x
    -- Iso.inv (thm5 x) = inv x
    -- Iso.rightInv (thm5 x) [ b ] = cong (fun x) (lem1 x [ b ]) ∙ 
    --                               (lem2 x (η b)) ∙ 
    --                               eq/ x b {!   !} --λ [ b ] → (lem3 x b) ∙ {!   !}
    -- Iso.rightInv (thm5 x) (eq/ a b r i) = {!   !}
    -- Iso.rightInv (thm5 x) (squash/ b b₁ p q i i₁) = {!   !}
    -- Iso.leftInv (thm5 x) = {!   !}
    
    
    -- map1 : ◯ R → fst (R/nilr)
    -- map1 ∣ x ∣ = [ x ]
    -- map1 (hub f) = [ 0r ]
    -- map1 (spoke f s i) = cong {!  !} (eq/ [ 0r ] (map1 (f s)) {!   !}) i --cong ∣_∣ (eq/ (map1 (f s)) [ 0r ] {!   !}) i
    -- map1 (≡hub p i) = {!   !}
    -- map1 (≡spoke p s i i₁) = {!   !}

--     map1/1 : fst (R/nilr k) → ℑ (fst k)
--     map1/1 [ x ] = ∣ x ∣
--     map1/1 (eq/ a b r i) = pre-η-has-contr-img (η ∘ ι) {!   !} {!   !} i
--     map1/1 (squash/ x x₁ p q i i₁) = {!   !}


            