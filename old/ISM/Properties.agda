{-# OPTIONS --cubical #-}
module SDG.ISM.Properties where

  open import Cubical.Foundations.Everything
  open import Cubical.Modalities.Modality
  open import Cubical.Homotopy.Connected
  
  module _ {ℓ : Level}{A B : Type ℓ}{f : A → B}{◯-asModality : Modality ℓ} where
    
    private
      η = Modality.η ◯-asModality
      ◯ = Modality.◯ ◯-asModality
      ◯-Type = Modality.◯-Types ◯-asModality
    --ℑ-connectedness
    ◯-connType : (X : Type ℓ) → Type ℓ
    ◯-connType X = isContr (◯ X) 
    ◯-connMap : {X Y : Type ℓ} → (f : X → Y) → Type ℓ
    ◯-connMap {Y = Y} f = (y : Y) → ◯-connType (fiber f y)

    precomp : (P : B → ◯-Type) →
                ((b : B) → fst (P b)) → ((a : A) → fst (P (f a)))
    precomp P s = s ∘ f

    P : (b : B) → ◯-Type 
    P b = (◯ (fiber f b)) , Modality.◯-isModal ◯-asModality

    c : hasSection (precomp P) → ((b : B) → fst (P b))
    c hS = fst hS (λ a → η (a , refl))

    baseCase/1 : (hS : hasSection (precomp P)) → (a : A) → c hS (f a) ≡ η (a , refl)
    baseCase/1 hS a = λ i → snd hS (λ a₁ → η (a₁ , refl)) i a

    idFun-◯fib : (b : B) → (fst (P b) → fst (P b))
    idFun-◯fib b = λ x → x
    constMap-◯fib : (b : B) → fst (P b) → (fst (P b) → fst (P b))
    constMap-◯fib b = λ cons → λ x → cons


    ---

   
    

    -- 3→1/1 : (a : A)(b : B) →
    --           (hS : hasSection (precomp P)) → (idFun-◯fib b) ≡ constMap-◯fib b (c hS b)
    -- 3→1/1 a b hS = λ i x → {!   !}

    -- 3→1 : (P : B → ◯-Type) →
    --         hasSection (precomp P) → ◯-connMap f
    -- 3→1 P hS = {!   !}


     