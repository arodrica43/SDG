{-# OPTIONS --cubical #-}
module SDG.Infinitesimal.Spec where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.FinData
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra -- Some of this imports should be moved to Base
  open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  open import Cubical.Algebra.CommAlgebra.FGIdeal
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Data.Sigma.Properties

  variable
    ℓ : Level
  module _ {k : CommRing ℓ} where
    
    private
        CAlg = CommAlgebra k ℓ
        k-as-alg : CAlg
        k-as-alg = freeAlgebra 0

    Spec : CAlg → Type ℓ
    Spec A = CommAlgebraHom A k-as-alg

  
    -- helper : Composition of CommAlgHoms is a CommAlgHom
    
    open IsAlgebraHom
    compIsCommAlgebraHom : {A : CAlg} {B : CAlg} {C : CAlg} 
        {g : ⟨ B ⟩ → ⟨ C ⟩} {f : ⟨ A ⟩ → ⟨ B ⟩}
        → IsCommAlgebraHom (B .snd) g (C .snd)
        → IsCommAlgebraHom (A .snd) f (B .snd)
        → IsCommAlgebraHom (A .snd) (g ∘ f) (C .snd)
    compIsCommAlgebraHom = compIsAlgebraHom

    -- Spec is a covariant functor

    Sp : {A B : CAlg} (f : CommAlgebraHom A B) → (Spec B → Spec A)  
    Sp {A} {B} f = λ g → (fst g ∘ fst f) , compIsCommAlgebraHom {A} {B} {k-as-alg} (snd g) (snd f)
  
    thm1 : {A B : CAlg} →
            (g : CommAlgebraHom A B) →
            (f : CommAlgebraHom B A) →
              ((x : fst A) → (fst f) ((fst g) x) ≡ x) → 
            ((x : Spec A) → fst ((Sp {A} {B} g) ((Sp {B} {A} f) x)) ≡ fst x)
    thm1 g f hS x = funExt λ z → cong (fst x) (hS z)

    thm2 : {A B : CAlg} →
            (g : CommAlgebraHom A B) →
            (f : CommAlgebraHom B A) →
              ((x : fst A) → (fst f) ((fst g) x) ≡ x) → 
            ((x : Spec A) → ((Sp {A} {B} g) ((Sp {B} {A} f) x)) ≡ x)
    thm2 {A} {B} g f hS x = Σ≡Prop iPIH (thm1 {A} {B} g f hS x)
      where
        iPIH = isPropIsCommAlgebraHom {ℓ} {k} {ℓ} {A} {k-as-alg}
    
    thm3 : {A B : CAlg} →
            (g : CommAlgebraHom A B) →
            (f : CommAlgebraHom B A) →
            section (fst f) (fst g) → 
            retract (Sp {B} {A} f) (Sp {A} {B} g)
    thm3 {A} {B} g f hS = λ a → thm2 {A} {B} g f hS a

    thm4 : {A B : CAlg} →
            (g : CommAlgebraHom A B) →
            (f : CommAlgebraHom B A) →
            section (fst f) (fst g) → 
            hasRetract (Sp {B} {A} f)
    thm4 {A} {B} g f hS = Sp {A} {B} g , (thm3 {A} {B} g f hS)

    -- thm1/2 : {A B : CAlg} →
    --         (g : CommAlgebraHom A B) →
    --         (f : CommAlgebraHom B A) →
    --           (hS : ((x : fst A) → (fst f) ((fst g) x) ≡ x)) → 
    --         ((x : Spec A) → snd ((Sp {A} {B} g) ((Sp {B} {A} f) x)) ≡ {!   !})
    -- thm1/2 {A} {B} g f hS x = {!   !}

    -- thm2 : {A B : CAlg} →
    --         (g : CommAlgebraHom A B) →
    --         (f : CommAlgebraHom B A) →
    --           ((x : fst A) → (fst f) ((fst g) x) ≡ x) → 
    --         ((x : Spec A) → (Sp {A} {B} g) ((Sp {B} {A} f) x) ≡ x)
    -- thm2 {A} {B} g f hS x = proof0
    --   where
    --     g* = Sp {A} {B} g
    --     f* = Sp {B} {A} f
    --     lem1 : (z : fst A) →  (fst (g* (f* x))) z ≡ (fst x) z
    --     lem1 z = cong (fst x) (hS z)
    --     proof0 : g* (f* x) ≡ x
    --     proof0 = λ i → (thm1 {A} {B} g f hS x i) , 
    --                    {!   !}     