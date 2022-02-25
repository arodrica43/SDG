{-# OPTIONS --cubical --safe #-}
module SDG.ISM.ModalConnected where

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

module _ {ℓ : Level}{A B : Type ℓ}{f : A → B}{◯-asModality : Modality ℓ} where
    
    private

      -- hint
       --     η' : A → A', A' modal
       -- _ ∘ η' : (A' → B) ≃ (A → B) for all modal B
       -- => A'= O A
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
    -- ◯-connectedTruncIso :  ◯-isConnMap f
    --                          → Iso (◯ A) (◯ B)
    -- ◯-connectedTruncIso con = g
    --     where
    --     back : B → ◯ A
    --     back y = ◯-map fst ((con y) .fst)

    --     g : Iso (◯ A) (◯ B)
    --     Iso.fun g = ◯-map f
    --     Iso.inv g = Modality.◯-rec ◯-asModality ◯-isModal back
    --     Iso.leftInv g = Modality.◯-elim ◯-asModality 
    --                                      (λ x → {!   !}) 
    --                                      λ a → cong {! ◯-map  !} ((con (f a) .snd (η (a , refl))))
    --     Iso.rightInv g = {!   !}


    --     where
    --     back : B → ◯ A
    --     back y = Modality.◯-map ◯-asModality fst (con y .fst) -- map fst ((con y) .fst)

    --     backSection :  (b : B) → Path (◯ B) 
    --                                   (Modality.◯-rec ◯-asModality (Modality.◯-isModal ◯-asModality) 
    --                                     (λ a → η (f a)) (Modality.◯-rec ◯-asModality ((Modality.◯-isModal ◯-asModality)) 
    --                                         back (η b))) 
    --                                   (η b)
    --     backSection b = helper (λ p → (Modality.◯-map ◯-asModality f p) ≡ η b)
    --                            (λ x → {! Modality. !}) 
    --                            (λ a p → cong η p)
    --                            (fst (con b))
    --         where
    --         helper : {B : A → Type ℓ} (P : ◯ A → Type ℓ)
    --                 → ((x : ◯ (Σ A B)) → {!   !})
    --                 → ((a : A) (b : B a) → {!   !})
    --                 → (p : ◯ (Σ A B))
    --                 →  {!   !} 
    --         helper = {!   !}
    --     g : Iso (◯ A) (◯ B)
    --     Iso.fun g = Modality.◯-map ◯-asModality f
    --     Iso.inv g = Modality.◯-rec ◯-asModality (Modality.◯-isModal ◯-asModality) back
    --     Iso.leftInv g = Modality.◯-elim ◯-asModality (λ x → Modality.◯-=-isModal ◯-asModality _ x) 
    --                                                     λ a → cong ({!   !} fst) (con (f a) .snd (η (a , refl))) 
    --     Iso.rightInv g = Modality.◯-elim ◯-asModality (λ x → Modality.◯-=-isModal ◯-asModality _ x) 
    --                                                     backSection                             

--   isIsoPrecompose zero P fConn = isContr→Iso (isOfHLevelΠ _ (λ b → P b .snd)) (isOfHLevelΠ _ λ a → P (f a) .snd)
--  Iso.rightInv (isIsoPrecompose (suc n) P fConn) t =
--     funExt λ a → cong (inv n P t (f a)) (fConn (f a) .snd ∣ a , refl ∣)
--                ∙ substRefl {B = fst ∘ P} (t a)
 --   Iso.leftInv (isIsoPrecompose (suc n) P fConn) s =
--     funExt λ b →
--           Trunc.elim
--             {B = λ d → inv n P (s ∘ f) b d ≡ s b}
--             (λ _ → isOfHLevelPath (suc n) (P b .snd) _ _)
--             (λ {(a , p) i → transp (λ j → P (p (j ∨ i)) .fst) i (s (p i))})
--             (fConn b .fst)

--   isEquivPrecompose : ∀ {ℓ'''} (n : ℕ) (P : B → TypeOfHLevel ℓ''' n)
--                    → isConnectedFun n f
--                    → isEquiv (λ(s : (b : B) → P b .fst) → s ∘ f)
--   isEquivPrecompose zero P fConn = isoToIsEquiv theIso
--     where
--     theIso : Iso ((b : B) → P b .fst) ((a : A) → P (f a) .fst)
--     Iso.fun theIso = λ(s : (b : B) → P b .fst) → s ∘ f
--     Iso.inv theIso = λ _ b → P b .snd .fst
--     Iso.rightInv theIso g = funExt λ x → P (f x) .snd .snd (g x)
--     Iso.leftInv theIso g = funExt λ x → P x .snd .snd (g x)
--   isEquivPrecompose (suc n) P fConn = isoToIsEquiv (isIsoPrecompose (suc n) P fConn)

--   isConnectedPrecompose : (n : ℕ) → ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') n)
--                                     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
--                        → isConnectedFun n f
--   isConnectedPrecompose zero P→sect b = isContrUnit*
--   isConnectedPrecompose (suc n) P→sect b = c n P→sect b , λ y →  sym (fun n P→sect b y)
--     where
--     P : (n : HLevel) → ((P : B → TypeOfHLevel ℓ (suc n))
--      → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
--      → B → Type _
--     P n s b = hLevelTrunc (suc n) (fiber f b)

--     c : (n : HLevel) → ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') (suc n))
--      → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f)) → (b : B)
--      → hLevelTrunc (suc n) (fiber f b)
--     c n s = (s λ b → (hLevelTrunc (suc n) (fiber f b) , isOfHLevelTrunc _)) .fst
--               λ a → ∣ a , refl ∣

--     fun : (n : HLevel) (P→sect : ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') (suc n))
--                      → hasSection λ(s : (b : B) → P b .fst) → s ∘ f))
--       → (b : B) (w : (hLevelTrunc (suc n) (fiber f b)))
--       → w ≡ c n P→sect b
--     fun n P→sect b = Trunc.elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc _) _ _)
--                                        λ a → J (λ b p → ∣ (fst a) , p ∣ ≡ c n P→sect b)
--                                                (c* (fst a))
--                                                (snd a)
--         where
--         c* : ((a : A) → ∣ (a , refl {x = f a}) ∣ ≡ c n P→sect (f a))
--         c* a = sym (cong (λ x → x a) (P→sect (λ b → hLevelTrunc (suc n) (fiber f b) , isOfHLevelTrunc _) .snd λ a → ∣ a , refl ∣))
        