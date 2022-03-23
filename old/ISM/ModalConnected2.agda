{-# OPTIONS --cubical --safe #-}
module SDG.ISM.ModalConnected2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec)
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.S1
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Modalities.Modality
open import Cubical.Homotopy.Connected

module _ {ℓ : Level}{A B S : Type ℓ}{f : A → B} where
    
    private
      ◯-asModality = NullModality S
      η = Modality.η ◯-asModality
      ◯ = Modality.◯ ◯-asModality
      ◯-Type = Modality.◯-Types ◯-asModality
      
    --ℑ-connectedness

    ◯-isConnType : (A : Type ℓ) → Type ℓ
    ◯-isConnType A = isContr (◯ A)
    ◯-isConnMap : (f : A → B) → Type ℓ
    ◯-isConnMap f = (y : B) → ◯-isConnType (fiber f y)

    private
        typeToFiberIso : (A : Type ℓ) → Iso A (fiber (λ (x : A) → tt) tt)
        Iso.fun (typeToFiberIso A) x = x , refl
        Iso.inv (typeToFiberIso A) = fst
        Iso.rightInv (typeToFiberIso A) b i = fst b , (isOfHLevelSuc 1 (isPropUnit) tt tt (snd b) refl) i
        Iso.leftInv (typeToFiberIso A) a = refl

        typeToFiber : (A : Type ℓ) → A ≡ fiber (λ (x : A) → tt) tt
        typeToFiber A = isoToPath (typeToFiberIso A)
        ◯-isModal = Modality.◯-isModal ◯-asModality
        ◯-=-isModal = Modality.◯-=-isModal ◯-asModality
        ◯-map-β = Modality.◯-map-β ◯-asModality
        ◯-map = Modality.◯-map ◯-asModality

    private
        ◯f = Modality.◯-map ◯-asModality f
        inv :  (P : B → ◯-Type)
            → ((a : A) → P (f a) .fst)
            → (b : B)
            → ◯ (fiber f b) → P b .fst
        inv P t b = Modality.◯-rec ◯-asModality (P b .snd) λ {(a , p) → subst (fst ∘ P) p (t a)}
    -- isIsoPrecompose : (P : B → ◯-Type)
    --                 → ◯-isConnMap {ℓ} {A} {B} {f} {◯-asModality} f
    --                 → Iso ((b : B) → P b .fst) ((a : A) → P (f a) .fst)
    -- Iso.fun (isIsoPrecompose P x) = _∘ f
    -- Iso.inv (isIsoPrecompose P x) t b = inv P t b (x b .fst)
    -- Iso.rightInv (isIsoPrecompose P x) t = 
    --     λ i a → (cong (inv {! P  !} {!   !} {!   !} {!   !}) {!   !} ∙ (substRefl {B = fst ∘ P} (t a))) i
    -- Iso.leftInv (isIsoPrecompose P x) s = {!   !}

    isConnectedPrecompose : ((P : B → ◯-Type)
                                → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
                                →  ◯-isConnMap f
    isConnectedPrecompose  P→sect b = (c P→sect b) , λ y → sym (fun P→sect b y)
        where
            P : ((P : B → ◯-Type) → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
                → B → Type ℓ
            P s b = ◯ (fiber f b)
            
            c : ((P : B → ◯-Type)
                → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f)) → (b : B)
                → ◯ (fiber f b)
            c s = (s λ b → (◯ (fiber f b) , Modality.◯-isModal ◯-asModality)) .fst
              λ a → η (a , refl)

            fun : (P→sect : ((P : B → ◯-Type)
                    → hasSection λ(s : (b : B) → P b .fst) → s ∘ f))
                    → (b : B) (w : (◯ (fiber f b)))
                    → w ≡ c P→sect b
            fun P→sect b = Modality.◯-elim ◯-asModality (λ x → Modality.◯-=-isModal ◯-asModality _ _) 
                            λ a → J (λ b p → (η ((fst a) , p)) ≡ c P→sect b) (c* (fst a)) (snd a)
                where
                c* : ((a : A) → η (a , refl {x = f a})  ≡ c P→sect (f a))
                c* a = sym (cong (λ x → x a) (P→sect (λ b → ◯ (fiber f b) , Modality.◯-isModal ◯-asModality) .snd λ a → η (a , refl)))
    
    
    -- ◯-indMapEquiv→conType : ◯-isConnMap {ℓ} {A} {B} {f} {◯-asModality} f → isEquiv (Modality.◯-map ◯-asModality f)
    -- ◯-indMapEquiv→conType con = record { equiv-proof = λ y → (fst {! con  !} , {!   !}) }
    ◯-connectedTruncIso :  ◯-isConnMap f
                             → Iso (◯ A) (◯ B)
    ◯-connectedTruncIso con = g
        where
        back : B → ◯ A
        back y = ◯-map fst ((con y) .fst)

        backSection : (b : B) → Path (◯ B) 
                                    (Modality.◯-rec ◯-asModality 
                                        ◯-isModal
                                        (λ x → η (f x)) 
                                        (Modality.◯-rec ◯-asModality 
                                            ◯-isModal 
                                            back 
                                            (η b))) 
                                    (η b)
        backSection b = helper (λ p → ◯-map f p ≡ η b) 
                                (λ x → Modality.◯-=-isModal ◯-asModality _ _) 
                                (λ a p → cong ∣_∣ p) 
                                (fst (con b))
            where
            helper :   {C : A → Type ℓ}(P : ◯ A → Type ℓ)
                        → ((x : ◯ (Σ A C)) → Modality.isModal ◯-asModality (P (◯-map fst x)))
                        → ((a : A) (b : C a) → P (η a))
                        → (p : ◯ (Σ A C))
                        →  P (◯-map fst p)
            helper P mod pf = Modality.◯-elim ◯-asModality mod λ x → pf (fst x) (snd x)

        g : Iso (◯ A) (◯ B)
        Iso.fun g = ◯-map f
        Iso.inv g = Modality.◯-rec ◯-asModality ◯-isModal back
        Iso.leftInv g = Modality.◯-elim ◯-asModality 
                                         (λ x → ◯-=-isModal _ _) 
                                         -- With a generic modality the following ◯-map fst gets stuck
                                         λ a → cong (◯-map fst) ((con (f a) .snd (η (a , refl))))
        Iso.rightInv g = Modality.◯-elim ◯-asModality 
                                          (λ x → ◯-=-isModal _ _)
                                          backSection


module Results {ℓ : Level}{S : Type ℓ} where

    private
        ◯-asModality = NullModality S
        η = Modality.η ◯-asModality
        ◯ = Modality.◯ ◯-asModality
        ◯-Type = Modality.◯-Types ◯-asModality
        ∗ = Unit* {ℓ}

    -- Properties of ∗
    ∗-isModal : Modality.isModal ◯-asModality ∗
    ∗-isModal = record { sec = (λ _ → tt*) , λ b i x → tt* ; 
                         secCong = λ x y → (λ z i → tt*) , λ b i i₁ x₁ → tt* }
    ∗-iso-ℑ∗ : (s : S) → Iso ∗ (◯ ∗)
    ∗-iso-ℑ∗ = λ s → Modality.isModalToIso ◯-asModality ∗-isModal
    
    cor1 :  ◯-isConnMap {ℓ} {S} {∗} {S} (λ x → tt*)
                 → Iso (◯ S) (◯ ∗)
    cor1 = ◯-connectedTruncIso 

    cor2 : ((P : ∗ → ◯-Type)
                → hasSection λ v _ → v tt*)
                →  ◯-isConnMap {ℓ} {S} λ x → tt*
    cor2 = isConnectedPrecompose

    precomp : {A B : Type ℓ} → (f : A → B) → (P : B → Modality.◯-Types ◯-asModality) →
                ((b : B) → fst (P b)) → ((a : A) → fst (P (f a)))
    precomp f P s = s ∘ f
    tcomp = _∘_
    cor3 : (P : ∗ → ◯-Type) → isEquiv (λ(s : (b : ∗) → P b .fst) → s ∘ λ x → tt*)
                → hasSection {ℓ} (λ(s : (b : ∗) → P b .fst) → tcomp {ℓ} {S} s λ x → tt*)
    cor3 P eq = sectionOfEquiv (λ(s : (b : ∗) → P b .fst) → s ∘ λ x → tt*) eq 

    trivial-iso : (X : Type ℓ) → Iso (∗ → X) X
    Iso.fun (trivial-iso X) = λ x → x tt*
    Iso.inv (trivial-iso X) = λ x x₁ → x
    Iso.rightInv (trivial-iso X) = λ b i → b
    Iso.leftInv (trivial-iso X) = λ a i x → a tt*

    cor4/1 : (P : ∗ → ◯-Type)(s : S) → isEquiv {ℓ} {ℓ} 
                                                {fst (P tt*)} 
                                                {S → fst (P tt*)} 
                                                λ x _ → x
    cor4/1 P s = toIsEquiv (λ x _ → x) (snd (P tt*))

    -- cor4/1/1 : (P : ∗ → ◯-Type)(s : S) → Iso (fst (P tt*)) (S → fst (P tt*)) 
    -- cor4/1/1 P s = toIso (λ x _ → x) (snd (P tt*))
    -- cor4/1/2 : (P : ∗ → ◯-Type)(s : S) → Iso (∗ → fst (P tt*)) (fst (P tt*)) 
    -- cor4/1/2 P s = trivial-iso (fst (P tt*))
    -- cor4/1/3 : (P : ∗ → ◯-Type)(s : S) → Iso (∗ → fst (P tt*)) (S → fst (P tt*)) 
    -- cor4/1/3 P s = ({! cor4/1/1 P s  !} ∘ {! cor4/1/1 P s  !}) (cor4/1/2 P s)
    


    -- cor4/2 : (P : ∗ → ◯-Type)(s : S) → isEquiv {ℓ} {ℓ} 
    --                                             {∗ → fst (P tt*)} 
    --                                             {S → fst (P tt*)} 
    --                                             λ x _ → x tt*
    -- cor4/2 P s = toIsEquiv (λ x _ → x tt*) (record 
    --     { sec = {!   !} ; 
    --     secCong = {!   !} })
    

    -- cor4 : (P : ∗ → ◯-Type)(s : S) → isEquiv {ℓ} {ℓ} 
    --                                     {(b : ∗) → fst (P tt*)} 
    --                                     {(a : S) → fst (P tt*)} 
    --                                     (λ x _ → x tt*)
    -- cor4 P s = {!   !}
        -- where
        -- sect : hasSection (λ x _ → x tt*)
        -- sect = (Iso.inv {!   !}) , {!   !}
        -- sectCong : (x y : ∗ → fst (P tt*)) → hasSection (cong (λ x₁ _ → x₁ tt*))
        -- sectCong = {!   !}
        -- isPathSplit : isPathSplitEquiv (λ x _ → x tt*)
        -- isPathSplit = record { sec = sect ; secCong = sectCong }
    --toIsEquiv (λ x _ → x) (Modality.Π-isModal ◯-asModality λ a → snd (P tt*))

    cor5 : (P : ∗ → ◯-Type)(s : S) → (λ(s : (b : ∗) → P b .fst) → tcomp {ℓ} {S} s  _) ≡  λ x _ → x _
    cor5 P s = λ i s₁ a → s₁ tt*

    
    
    --cor5 :  ((P : ∗ → ◯-Type)(a : S) → 
    --        isEquiv (λ(s : (b : ∗) → P b .fst) → tcomp {ℓ} {S} s (λ _ → tt*)))
    --cor5 P a = record { equiv-proof = λ y → {!   !} }

    


          