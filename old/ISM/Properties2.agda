{-# OPTIONS --cubical #-}
module SDG.ISM.Properties2 where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommRing.Ideal
  open import Cubical.Algebra.CommRing.QuotientRing
  open import Cubical.HITs.SetQuotients
  open import Cubical.Foundations.Everything
  open import Cubical.Modalities.Modality
  open import Cubical.Homotopy.Connected
  open import Cubical.Data.Unit
  open import Cubical.Data.Nat
  open import Cubical.Data.Sigma
  --open import Cubical.Algebra.CommRing.QuotientRing
  open import Cubical.HITs.PropositionalTruncation
  open import SDG.Base
  open import SDG.Nilpotent
  open import SDG.InfinitesimalObjects
  open import SDG.ISM.Base
  open import Cubical.Algebra.RingSolver.Reflection
  open import Cubical.Algebra.CommRing.RadicalIdeal
  open import Cubical.HITs.Nullification
  open import Cubical.Functions.Logic
  open import Cubical.Algebra.CommAlgebra.Properties
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.Instances.FreeCommAlgebra
  open import Cubical.Data.Vec
  open import Cubical.Data.FinData

  open import SDG.Nilradical
  
  module main {ℓ : Level}{k : CommRing ℓ} where
    open Foundations {ℓ} {k}
    open BaseFoundations {ℓ} {k}
    private
        Dsk = D∞ {ℓ} {k}
        ∗ = Unit* {ℓ}
        Dsk-pt = D∞-pt {ℓ} {k}  
        --[_] = [_]/ {ℓ} {k} {CommIdeal→Ideal k (nilradical k)}

    f : Dsk → fst (R/nilr k)
    f d = [ (fst (snd d)) ]
    0f : Dsk → fst (R/nilr k)
    0f d = [ 0r ]

    ι : Dsk → fst k
    ι = fst ∘ snd

    lem1 : (x y : Dsk) → η (ι x) ≡ η (ι y) -- (x : fst k) → Σ ℕ (λ n → x ^ n ≡ 0r)
    lem1 x y = pre-η-has-contr-img (η ∘ ι) x y
    lem2 : (x : Dsk) → η (ι x) ≡ η 0r -- (x : fst k) → Σ ℕ (λ n → x ^ n ≡ 0r)
    lem2 x = lem1 x Dsk-pt
    lem3 : {X : Type ℓ}(f : Dsk → X) (x y : Dsk) → η (f x) ≡ η (f y)
    lem3 f x y = pre-η-has-contr-img (η ∘ f) x y

    infDisp : (fst k) → Dsk → (fst k)
    infDisp x d = ((snd k) CommRingStr.+ x) (ι d)
    lem4 : (x : fst k) → (infDisp x Dsk-pt) ≡ x
    lem4 x = CommRingStr.+Rid (snd k) x
    lem5 : (x : fst k)(a b : Dsk) → η (infDisp x a) ≡ η (infDisp x b)
    lem5 x a b = lem3 (infDisp x) a b
    lem6 : (x : fst k)(a : Dsk) → η (infDisp x a) ≡ η x
    lem6 x a = (lem5 x a Dsk-pt) ∙ cong η (lem4 x)
    lem7 : (x y : fst k) (a : Dsk) → η x ≡ η y → 
            η (infDisp x a) ≡ η (infDisp y a) 
    lem7 x y a sC = (lem6 x a) ∙ sC ∙ sym (lem6 y a)
    lem8 : (x y : fst k) (a b : Dsk) → η x ≡ η y → 
            η (infDisp x a) ≡ η (infDisp y b)
    lem8 x y a b sC = (lem7 x y a sC) ∙ lem5 y a b

    infScal : (fst k) → Dsk → (fst k)
    infScal x d = ((snd k) CommRingStr.· x) (ι d)
    open RingTheory
    lem9 : (x : fst k) → infScal x Dsk-pt ≡ 0r 
    lem9 x = 0RightAnnihilates (CommRing→Ring k) x 
    lem10 : (x : fst k)(a b : Dsk) → η (infScal x a) ≡ η (infScal x b)
    lem10 x a b = lem3 (infScal x) a b
    lem11 : (x : fst k)(a : Dsk) → η (infScal x a) ≡ η 0r
    lem11 x a = (lem10 x a Dsk-pt) ∙ cong η (lem9 x)
    lem12 : (x y : fst k) (a : Dsk) →
            η (infScal x a) ≡ η (infScal y a) 
    lem12 x y a = lem11 x a ∙ sym (lem11 y a)
    lem13 : (x y : fst k) (a b : Dsk) →
            η (infScal x a) ≡ η (infScal y b)
    lem13 x y a b = (lem12 x y a) ∙ lem10 y a b
    
    variable
        n : ℕ
    _at_ = polynomialAt
    infDispl : FinVec (fst k) n → Dsk → (fst k)
    infDispl p d = p at (ι d)
    lem15 : (p : FinVec (fst k) n) → (a b : Dsk) → η (infDispl p a) ≡ η (infDispl p b)
    lem15 p a b = lem3 (infDispl p) a b
    lem16 : (p : FinVec (fst k) n)(a : Dsk) → η (infDispl p a) ≡ η (p at 0r)
    lem16 p a = (lem15 p a Dsk-pt) ∙ cong η refl
    lem17 : (p q : FinVec (fst k) n) (a : Dsk) → η (p at 0r) ≡ η (q at 0r) →
            η (infDispl p a) ≡ η (infDispl q a) 
    lem17 p q a sC = lem16 p a ∙ sC ∙ sym (lem16 q a)
    lem18 : (p q : FinVec (fst k) n) (a b : Dsk) → η (p at 0r) ≡ η (q at 0r) →
            η (infDispl p a) ≡ η (infDispl q b) 
    lem18 p q a b sC = (lem17 p q a sC) ∙ lem15 q a b


--     map1 : ℑ (fst k) → fst (R/nilr k)
--     map1 ∣ x ∣ = [ x ]
--     map1 (hub f) = [ 0r ]
--     map1 (spoke f s i) = cong ∣_∣ (eq/ (map1 (f s)) [ 0r ] {!   !}) i
--     map1 (≡hub p i) = {!   !}
--     map1 (≡spoke p s i i₁) = {!   !}

--     map1/1 : fst (R/nilr k) → ℑ (fst k)
--     map1/1 [ x ] = ∣ x ∣
--     map1/1 (eq/ a b r i) = pre-η-has-contr-img (η ∘ ι) {!   !} {!   !} i
--     map1/1 (squash/ x x₁ p q i i₁) = {!   !}

    


--     open Theory 
--     mapk : fst k → fst (freeAlgebra {ℓ} {k} 0) 
--     mapk x = Construction.const x
--     -- open CommAlgChar
--     -- helper2 : CommAlgebra k ℓ → CommRing ℓ
--     -- helper2 A = fst (Iso.fun (CommAlgIso k) A)
--     k[x] = freeAlgebra {ℓ} {k} 1
--     NDhinfDisp : (n : ℕ) → FinVec Dsk n → fst (freeAlgebra {ℓ} {k} n) → fst k-as-algebra
--     NDhinfDisp n d p = inducedMap k-as-algebra (λ i → mapk (ι (d i))) p
--     hinfDisp : Dsk → fst k[x] → fst k-as-algebra
--     hinfDisp d p = NDhinfDisp 1 (λ x → d) p

--     lem14 : (p : fst k[x]) → hinfDisp Dsk-pt p ≡ inducedMap k-as-algebra (λ i → CommAlgebraStr.0a (snd k-as-algebra)) p
--     lem14 p = refl
   
    --proof_by_ : (P : hProp ℓ) → ℑ ⟨ P ⟩ → ⟨ P ⟩
    --proof P by p = ℑ-rec {!   !} (λ x → x) p --rec (isProp⟨⟩ P) (λ p → p) p

    --lem4 : (x : fst k) → η x ≡ η 0r → Dsk
    --lem4 x iD = {! map2  !}

    -- kills-nilpotents : Iso (ℑ (fst k)) (fst (R/nilr k))
    -- Iso.fun kills-nilpotents = {!   !}
    -- Iso.inv kills-nilpotents = {!   !}
    -- Iso.rightInv kills-nilpotents = {!   !}
    -- Iso.leftInv kills-nilpotents = {!   !}    
    
    

    -- nilradical : IdealsIn  k
    -- nilradical = makeIdeal k (λ x → (∃[ n ∈ ℕ ] x ^ n ≡ CommRingStr.0r (snd k)) , squash) 
    --                                 (λ x y → ∣ {!   !} , {!   !} ∣)
    --                                 ∣ 1 , CommRingStr.·Lid (snd k) 0r ∣ 
    --                                 λ r x → ∣ {!  !} , {!   !} ∣
    --               where
    --                 prov : (x : fst k) → ∃[ n ∈ ℕ ] x ^ n ≡ CommRingStr.0r (snd k) → 
    --                         Σ ℕ (λ n → x ^ n ≡ CommRingStr.0r (snd k))
    --                 prov x iN = {!  !} , {!   !}



    -- nilrad : fst k → fst k → Type ℓ
    -- nilrad = λ x y → Σ ℕ (λ n → ((snd k) CommRingStr.- x) y ^ n ≡ 0r)

    -- lem1 : Iso  (ℑ (fst k)) ((fst k) /ₜ nilrad)
    -- Iso.fun lem1 x = {!   !}
    -- Iso.inv lem1 x = η (Cubical.HITs.TypeQuotients.rec {!   !} {!   !} x)
    -- Iso.rightInv lem1 = {!   !}
    -- Iso.leftInv lem1 = {!   !} 
      
    
    -- private
    --   η = Modality.η ◯-asModality
    --   ◯ = Modality.◯ ◯-asModality
    --   ◯-Type = Modality.◯-Types ◯-asModality
    -- ℑ-connectedness
    -- ◯-connType : (X : Type ℓ) → Type ℓ
    -- ◯-connType X = isContr (◯ X) 
    -- ◯-connMap : {X Y : Type ℓ} → (f : X → Y) → Type ℓ
    -- ◯-connMap {Y = Y} f = (y : Y) → ◯-connType (fiber f y)            