{-# OPTIONS --cubical #-}

module SDG.ISM.Base where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.RingSolver.Reflection
  open import Cubical.Modalities.Modality
  open import Cubical.Foundations.Equiv.PathSplit
  
  open import Cubical.HITs.Localization renaming (rec to Lrec)
  open import Cubical.HITs.Nullification renaming (elim to elim-Null ; rec to Nrec)
  open import Cubical.Data.Unit
  open import Cubical.Data.Empty
  open import SDG.InfinitesimalObjects
  open import SDG.Base
  open import SDG.Nilpotent
  open import SDG.ISM.ModalConnected2
  open import Cubical.Functions.Embedding


  module BaseFoundations {ℓ : Level} {k : CommRing ℓ} where
    open Foundations
    private
      Dsk = D∞ {ℓ} {k}
      --Dsk = Σ (d : R) | Σ (n : ℕ) d ... d ≡ 0 |
      --D n = Σ (d : R) d ... d ≡ 0 
      --D n = Σ (d : R) d ^ (n + 1)...
      ∗ = Unit* {ℓ}
      Dsk-pt = D∞-pt {ℓ} {k}
      
    -- Implement ISM as nullification at D∞
    ISM : Modality ℓ
    ISM = NullModality Dsk
    η = Modality.η ISM
    ℑ = Modality.◯ ISM
    ℑ-rec = Modality.◯-rec ISM
    ℑ-Type = Modality.◯-Types ISM

    -- The maps from Dsk to modal types are exacly the constant maps
    ℑDsk-iso0 : {A : Type ℓ} → Iso (ℑ A) (Dsk → ℑ A)
    ℑDsk-iso0 {A} = toIso (const {A = ℑ A} {B = Dsk}) isNull-Null 
    ℑDsk-iso0/1 : (A : ℑ-Type) → Iso (fst A) (Dsk → (fst A))
    ℑDsk-iso0/1 A = toIso (const {A = fst A} {B = Dsk}) (snd A)
    ℑDsk-iso1 : Iso (ℑ Dsk) (Dsk → ℑ Dsk)
    ℑDsk-iso1 = toIso (const {A = ℑ Dsk} {B = Dsk}) (Modality.◯-isModal ISM) 
    
    -- the image of every map (S → Null S A) is contractible in Null S A,
    -- so the image of every map (Dsk → ℑ A) is contractible in ℑ A,
    -- so the image of η-Dsk : Dsk → ℑ Dsk  is contractible in ℑ Dsk,
    -- so ∀ (x y : ℑ Dsk) η (x) ≡ η (y).
    pre-η-has-contr-img : {S A : Type ℓ} → (f : S → Null S A) → (x y : S) → f x ≡ f y 
    pre-η-has-contr-img f x y i = ((sym (spoke f x)) ∙ spoke f y) i
    η-has-contr-img : (x y : Dsk) → η x ≡ η y 
    η-has-contr-img x y i = pre-η-has-contr-img η x y i
      
    -- Higher version of the previous implementation
    pre-η-has-contr-img2 : {S : Type ℓ} {x y : Null S S} → (p : S → x ≡ y) → (s r : S) → p s ≡ p r
    pre-η-has-contr-img2 p s r = sym (≡spoke p s) ∙ (≡spoke p r)
    η-p : (x y s : Dsk) → η x ≡ η y 
    η-p = λ x y s i → η-has-contr-img x y i
    η-has-contr-img2 : {S : Type ℓ} {x y : Dsk} → (p : Dsk → η x ≡ η y) → (s r : Dsk) 
                              → η-p x y s ≡ η-p x y r
    η-has-contr-img2 {x = x} {y = y} p s r = pre-η-has-contr-img2 (λ x₁ i → η-has-contr-img x y i) s r
    
    -- Properties of ∗
    ∗-isModal : Modality.isModal ISM ∗
    ∗-isModal = record { sec = (λ _ → tt*) , λ b i x → tt* ; 
                         secCong = λ x y → (λ z i → tt*) , λ b i i₁ x₁ → tt* }
    ∗-iso-ℑ∗ : Iso ∗ (ℑ ∗)
    ∗-iso-ℑ∗ = Modality.isModalToIso ISM ∗-isModal
 
    -- Dsk behaves as ∗ when we map in modal types :: (∗ → ℑ Dsk) ≃ (Dsk → ℑ Dsk) -- change by
    ℑDsk-iso2 : Iso (∗ → ℑ Dsk) (ℑ Dsk)
    ℑDsk-iso2 =  iso (λ x → x tt*) (λ x x₁ → x) (λ b i → b) λ a i x → a tt*
    ℑDsk-iso3 : Iso (∗ → ℑ Dsk) (Dsk → ℑ Dsk)
    ℑDsk-iso3 = iso 
                    (λ x x₁ → Iso.fun ℑDsk-iso2 x) 
                    (λ x x₁ → Iso.inv ℑDsk-iso1 x) 
                    (λ b i x → spoke b x i) 
                    λ a i x → spoke (Iso.fun ℑDsk-iso1 (a tt*)) Dsk-pt i
    
    ℑDsk-iso2/1 : isEquiv (λ x _ → x tt*)
    ℑDsk-iso2/1 = isoToIsEquiv ℑDsk-iso3
    ℑDsk-iso2/2 : hasSection (λ x _ → x tt*)
    ℑDsk-iso2/2 = isEquiv→hasSection ℑDsk-iso2/1
    ℑDsk-iso2/3 : (P : ∗ → Modality.◯-Types ISM) → hasSection (λ x _ → x tt*)
    ℑDsk-iso2/3 P = isEquiv→hasSection ℑDsk-iso2/1

    private
      ℑU = Modality.◯-Types ISM

    ℑDsk-iso2' : (X : ℑU) → Iso (∗ → (fst X)) (fst X)
    ℑDsk-iso2' X =  iso (λ x → x tt*) (λ x x₁ → x) (λ b i → b) λ a i x → a tt*
    ℑDsk-iso3' :  (X : ℑU) → Iso (∗ → (fst X)) (Dsk → (fst X))
    ℑDsk-iso3' X = compIso (ℑDsk-iso2' X) (ℑDsk-iso0/1 X)
    
    ℑDsk-iso2/1' :  (X : ℑU) →  isEquiv (λ x _ → x tt*)
    ℑDsk-iso2/1' X = isoToIsEquiv (ℑDsk-iso3' X)
    ℑDsk-iso2/2' :  (X : ∗ → ℑU) → hasSection (λ x _ → x tt*)
    ℑDsk-iso2/2' X = isEquiv→hasSection (ℑDsk-iso2/1' (X tt*))

    thm1 : ◯-isConnMap {ℓ} {Dsk} {∗} {Dsk} {λ _ → tt*} λ x → tt*
    thm1 = isConnectedPrecompose ℑDsk-iso2/2'

    thm2 : Iso (ℑ Dsk) (ℑ ∗)
    thm2 = ◯-connectedTruncIso thm1  

    -- Main theorem ---
    thm3 : Iso (ℑ Dsk) ∗
    thm3 = compIso thm2 (invIso (∗-iso-ℑ∗))  
    -------------------

    thm4 : isContr ∗
    thm4 = tt* , (λ y i → tt*)
    thm4/1 : isContr (ℑ ∗)
    thm4/1 = (Iso.fun ∗-iso-ℑ∗ tt*) , (Iso.rightInv ∗-iso-ℑ∗)
    thm4/2 : ◯-isConnType {ℓ} {∗} {∗} {Dsk} ∗
    thm4/2 = thm4/1

    thm5/1 : isContr (ℑ Dsk)
    thm5/1 = (Iso.fun (invIso thm3) tt*) , Iso.leftInv thm3
    thm5 : ◯-isConnType {ℓ} {∗} {∗} {Dsk} Dsk
    thm5 = thm5/1

    private
      ℑ-isConn = ◯-isConnType {ℓ} {∗} {∗} {Dsk}

    ℑ-isConnectedRetract : {A : Type ℓ} {B : Type ℓ}
      (f : A → B) (g : B → A)
      (h : (x : A) → g (f x) ≡ x)
      → ℑ-isConn B → ℑ-isConn A
    ℑ-isConnectedRetract f g h = isContrRetract 
                                  (Modality.◯-map ISM f) 
                                  (Modality.◯-map ISM g) 
                                  (Modality.◯-elim ISM 
                                    (λ _ → Modality.◯-=-isModal ISM _ _) 
                                    λ x → cong η (h x))

    thm6 : {A : Type ℓ}
      (f : A → Dsk) (g : Dsk → A)
      (h : (x : A) → g (f x) ≡ x)
       → ℑ-isConn A
    thm6 f g h = ℑ-isConnectedRetract f g h thm5

    thm7 : {A : Type ℓ}
      (f : A → Dsk) (g : Dsk → A)
      (h : (x : A) → g (f x) ≡ x)
       → Iso (ℑ A) ∗
    thm7 {A} f g h = iso (λ _ → tt*) 
                         (λ x → fst (thm6 f g h)) 
                         (λ b i → tt*) 
                         λ a i → (snd (thm6 f g h)) a i
    
    -- isConnectedRetract (suc n) f g h =
    --   isContrRetract
    --     (Trunc.map f)
    --     (Trunc.map g)
    --     (Trunc.elim
    --       (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
    --       (λ a → cong ∣_∣ (h a)))


    -- cor1 : {X : Type ℓ}(f : X → Dsk) → isEmbedding f → isEmbedding (Modality.◯-map ISM f)
    -- cor1 {X} f iE = λ w x → record { 
    --                   equiv-proof = λ y → ((λ i → {!  !}) , {!   !}) , 
    --                                       λ y₁ i → {!   !} , {!   !} }
    private
      ℑ-isConnMap = ◯-isConnMap {ℓ} {Dsk} {∗} {Dsk} {λ _ → tt*} 
    -- ℑDsk-iso2/3 : ((P : ∗ → Modality.◯-Types ISM)
    --                             → hasSection (λ x _ → x tt*))
    --                             →  ℑ-isConnMap λ _ → tt*
    -- ℑDsk-iso2/3 F = {!   !}

    -- Constants map A → (Dsk → A) is an equivalence for each modal type A
    constants-map : (X : Modality.◯-Types ISM) → fst X → (Dsk → fst X)
    constants-map X a = λ x → a
    constants-map-is-equiv : (X : Modality.◯-Types ISM) → isEquiv (constants-map X)
    constants-map-is-equiv X = toIsEquiv (constants-map X) (snd X)

    --precomposition map
    precomp : {A B : Type ℓ} → (f : A → B) → (P : B → Modality.◯-Types ISM) →
                ((b : B) → fst (P b)) → ((a : A) → fst (P (f a)))
    precomp f P s = s ∘ f

    constants-map-as-precomp : {A : Type ℓ} → (X : Modality.◯-Types ISM) →
                (fst X) → (A → fst X)
    constants-map-as-precomp X s = precomp (λ x → tt*) (λ x → X) λ b → s
    -- Disk is implicit here, but if we try to force for an arbitrary type A, 
    -- then it does not typecheck
    constants-map-as-precomp-equiv : (X : Modality.◯-Types ISM) → (s : fst X) 
                                    → isEquiv (constants-map-as-precomp X)
    constants-map-as-precomp-equiv X s = toIsEquiv (constants-map-as-precomp X) (snd X) 

    --ℑ-connectedness
    ℑconnected-type : (X : Type ℓ) → Type ℓ
    ℑconnected-type X = isContr (ℑ X) 

    ℑconnected-map : {X Y : Type ℓ} → (f : X → Y) → Type ℓ
    ℑconnected-map {Y = Y} f = (y : Y) → ℑconnected-type (fiber f y)

    -- precomp isEquiv ⇒ precomp has a section

    sectionOfPrecomp : {A B : Type ℓ} → (f : A → B) → (P : B → Modality.◯-Types ISM) →
                    isEquiv (precomp f P) → hasSection (precomp f P)
    sectionOfPrecomp f P g = sectionOfEquiv (precomp f P) g

    -- Experiments --

    P : {A B : Type ℓ} (f : A → B) (b : B) → Modality.◯-Types ISM
    P f b = (ℑ (fiber f b)) , Modality.◯-isModal ISM

    c : {A B : Type ℓ}(f : A → B) → isEquiv (precomp f (P f)) → 
                      (b : B) → fst (P f b)
    c f e = fst (sectionOfPrecomp f (P f) e) λ a → η (a , refl)

    constFuncAt : {A B : Type ℓ}(f : A → B)(b : B)(e : isEquiv (precomp f (P f))) →
                  fst (P f b) → fst (P f b)
    constFuncAt = λ f b e x → c f e b

    -- interprop : {A B : Type ℓ}(f : A → B)(b : B)(w : fst (P f b))(e : isEquiv (precomp f (P f))) →
    --               c f e b ≡ w
    -- interprop f b w e i = J (λ y x → fst (P f (x i))) 
    --                         {!   !}
    --                         refl

    -- interprop f b (hub f₁) e = {!   !}
    -- interprop f b (spoke f₁ s i) e = {!   !}
    -- interprop f b (≡hub p₁ i) e = {!   !}
    -- interprop f b (≡spoke p₁ s i i₁) e = {!   !}
    
    --hasSection→isConnMap :  {A B : Type ℓ} → (f : A → B) → (P : B → Modality.◯-Types ISM) →
                  --          hasSection (precomp f P) → ℑconnected-map (precomp f P)
    --hasSection→isConnMap f P hS = {!   !}

    -- Experiments --
    experiment3 : (x y : ℑ Dsk) → Iso (x ≡ y) (Dsk → x ≡ y)
    experiment3 x y = toIso (λ x₁ x₂ i → x₁ i) (Modality.◯-=-isModal ISM x y)
    Dsk→ℑDsk-isModal : Modality.isModal ISM (Dsk → ℑ Dsk)
    Dsk→ℑDsk-isModal = Modality.→-isModal ISM (Modality.◯-isModal ISM)  
    --ℑDsk-iso3' : (s : Dsk) → Iso (Dsk → ℑ Dsk) (ℑ (Dsk → ℑ Dsk))
    --ℑDsk-iso3' = λ s → Modality.isModalToIso ISM Dsk→ℑDsk-isModal

    ∗→ℑDsk-isModal : Modality.isModal ISM (∗ → ℑ Dsk)
    ∗→ℑDsk-isModal = Modality.→-isModal ISM (Modality.◯-isModal ISM)  
    ℑ∗-iso3 : (s : Dsk) → Iso (∗ → ℑ Dsk) (ℑ (∗ → ℑ Dsk))
    ℑ∗-iso3 = λ s → Modality.isModalToIso ISM ∗→ℑDsk-isModal
  