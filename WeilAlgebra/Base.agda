{-# OPTIONS --cubical --safe #-}

module SDG.WeilAlgebra.Base where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.Nat
  open import Cubical.Data.Bool
  open import Cubical.Data.FinData
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommRing.FGIdeal
  open import Cubical.Algebra.Module
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.HITs.PropositionalTruncation
  open import SDG.Base
  open import SDG.WeilAlgebra.Instances

  module Definition (baseRing : CommRing ℓ) where

    module _ (ℝ@(R , str) : CommRing ℓ) (n : ℕ) where

      open BasicInstances ℝ
      open 1DFreeCommAlgebraUtils ℝ
      open ModuleUtils ℝ
      open 1DFundamentalWeilAlgebras ℝ
      open CommIdealUtils (CommAlgebra→CommRing (W n))
      open commonExtractors
      open import Cubical.Algebra.CommAlgebra.Ideal
    
      weilAlgebraProperty : (X : CommAlgebra ℝ ℓ) → Type (ℓ-suc ℓ)
      weilAlgebraProperty X = Σ[ N ∈ nilpotentIdeal ] Iso ⟨ Algebra→Module (CommAlgebra→Algebra X) ⟩ ⟨ A⊕ N ⟩ --Σ[ N ∈ nilpotentIdeal ] Iso ⟨ Algebra→Module (CommAlgebra→Algebra X) ⟩ ⟨ A⊕ ? ⟩
        where
          reclift : (n : ℕ) → Lift {ℓ-zero} {ℓ} (Fin n) → Fin n
          reclift n (lift i) = i
          A⊕ : (N : nilpotentIdeal) → LeftModule (CommRing→Ring (CommAlgebra→CommRing (W n))) ℓ
          A⊕ N = pointwiseModule (CommAlgebra→CommRing (W n)) {X = Lift (Fin 2)} 
                    (λ k →  CommIdeal→LeftModule (CommAlgebra→CommRing (W n)) 
                      (if (reclift 2 k) == zero 
                        then 
                          1Ideal (W n)
                        else 
                          (fst N)))

      isWeilAlgebra : (X : CommAlgebra ℝ ℓ) → Type (ℓ-suc ℓ)
      isWeilAlgebra X = ∥ weilAlgebraProperty X ∥₁ 

      isFPWeilAlgebra : Σ[ X ∈ CommAlgebra ℝ ℓ ] isFPAlgebra X → Type (ℓ-suc ℓ)
      isFPWeilAlgebra X = isWeilAlgebra (fst X) 

  module 1DFundamentalWeilAlgebrasProperties (ℝ@(R , str) : CommRing ℓ) (n : ℕ) where

    open Definition ℝ
    open 1DFundamentalWeilAlgebras ℝ
    open 1DFreeCommAlgebraUtils ℝ
    open BasicInstances ℝ

    -- mainThm : isWeilAlgebra ℝ n (W n)
    -- mainThm = ∣ (genIdeal {n = 1} (CommAlgebra→CommRing (W n)) (λ _ → eps₀ n) , ∣ (suc n) , (λ x → {!   !}) ∣₁) ,
    --            iso (λ x k → if (reclift 2 k) == zero 
    --                     then 
    --                       {!   !} , {!   !}
    --                     else 
    --                       {!   !}) {!   !} {!   !} {!   !} ∣₁
     
    --   where
    --     reclift : (n : ℕ) → Lift {ℓ-zero} {ℓ} (Fin n) → Fin n
    --     reclift n (lift i) = i 