{-# OPTIONS --cubical --safe #-}

module SDG.Nilpotent where

    open import Cubical.Algebra.CommRing
    open import Cubical.Algebra.Algebra
    open import Cubical.Algebra.CommAlgebra
    open import Cubical.Algebra.CommAlgebra.FPAlgebra
    open import Cubical.Algebra.CommAlgebra.Instances.FreeCommAlgebra renaming (inducedHom to canonicalHom)
    open import Cubical.Foundations.Everything
    open import Cubical.Data.Nat
    open import Cubical.Data.FinData
    
    open import SDG.CommAlgebra.DirProd
    open import SDG.Base

    open import Cubical.Algebra.Ring.BigOps

    private
        variable
            ℓ : Level

    module _ (k : CommRing ℓ) where
        private
            k-as-ring = CommRing→Ring k
            0k : fst k
            0k = CommRingStr.0r (snd k)
            k-as-CAlg : CommAlgebra k ℓ
            k-as-CAlg = freeAlgebra 0
        open Product k-as-ring
        open Foundations 
        isNilpRing : CommRing ℓ → Type ℓ
        isNilpRing A = Σ ℕ λ n → (v : FinVec (fst k) n) → ∏ (λ i → v i) ≡ 0k

        NilpRing : Type (ℓ-suc ℓ)
        NilpRing = Σ (CommRing ℓ) λ A → isNilpRing A 

        isNilpAlg : CommAlgebra k ℓ → Type ℓ
        isNilpAlg A = isNilpRing (CommAlgebra→CommRing A)

        NilpAlg : Type (ℓ-suc ℓ)
        NilpAlg = Σ (CommAlgebra k ℓ) λ A → isNilpAlg A 

        NilpAlg→CommAlgebra : NilpAlg → CommAlgebra k ℓ
        NilpAlg→CommAlgebra A = fst A

        FPNilpAlg : Type (ℓ-suc ℓ)
        FPNilpAlg = Σ FPAlg λ A → Σ NilpAlg λ N → (FPAlg→CommAlgebra A) ≡ (k-as-CAlg ⊗ NilpAlg→CommAlgebra N)

        FPNilpAlg2 : Type (ℓ-suc ℓ)
        FPNilpAlg2 = Σ (FPAlg {ℓ} {k}) λ A → Σ NilpAlg λ N → Iso (fst (FPAlg→CommAlgebra A)) (fst (k-as-CAlg ⊗ NilpAlg→CommAlgebra N))

        FPNilpAlg3 : Type (ℓ-suc ℓ)
        FPNilpAlg3 = Σ (FPAlg {ℓ} {k}) λ A → Σ NilpAlg λ N → Σ (CommAlgebraHom (FPAlg→CommAlgebra A) (k-as-CAlg ⊗ NilpAlg→CommAlgebra N)) λ ϕ → isIso (fst ϕ)

        FPNilpAlg→CommAlgebra : FPNilpAlg → CommAlgebra k ℓ
        FPNilpAlg→CommAlgebra W = FPAlg→CommAlgebra (fst W)

        FPNA→Type : (W : FPNilpAlg) → Type ℓ
        FPNA→Type W = fst (fst (fst W))

        FPNA-0a : (W : FPNilpAlg) → FPNA→Type W
        FPNA-0a W = CommAlgebraStr.0a (snd (FPNilpAlg→CommAlgebra W))

        -- ϕ : (W : FPNilpAlg2) → fst (FPAlg→CommAlgebra (fst W)) → fst (k-as-CAlg ⊗ NilpAlg→CommAlgebra (fst (snd W)))
        -- ϕ W = λ x → Iso.fun (snd (snd W)) x
        -- spec-prept : (W : FPNilpAlg2) → fst (fst (fst W)) → fst k-as-CAlg -- (k-as-CAlg ⊗ (NilpAlg→CommAlgebra (fst (snd W))))
        -- spec-prept W = λ x → fst (ϕ W x) 

        ϕ : (W : FPNilpAlg3) → CommAlgebraHom (FPAlg→CommAlgebra (fst W)) (k-as-CAlg ⊗ NilpAlg→CommAlgebra (fst (snd W)))
        ϕ W = fst (snd (snd W))
        
        ψ : (W : FPNilpAlg3) → CommAlgebraHom (k-as-CAlg ⊗ NilpAlg→CommAlgebra (fst (snd W))) (k-as-CAlg)
        ψ W = (λ x →  fst x) , record
                                { pres0 = refl
                                ; pres1 = refl
                                ; pres+ = λ x y i → (snd k-as-CAlg CommAlgebraStr.+ fst x) (fst y)
                                ; pres· = λ x y i → ((snd k-as-CAlg) CommAlgebraStr.· fst x) (fst y)
                                ; pres- = λ x i → (CommAlgebraStr.- (snd k-as-CAlg)) (fst x)
                                ; pres⋆ = λ r y i → ((snd k-as-CAlg) CommAlgebraStr.⋆ r) (fst y)
                                }
        
        ψ∘ϕ : (W : FPNilpAlg3) → CommAlgebraHom (FPAlg→CommAlgebra (fst W)) (k-as-CAlg)
        ψ∘ϕ W =  (λ x → fst (ψ W) (fst (ϕ W) x)) , compIsAlgebraHom (snd (ψ W)) (snd (ϕ W))
        --                                         { pres0 = λ i → {!   !}
        --                                         ; pres1 = {!   !}
        --                                         ; pres+ = {!   !}
        --                                         ; pres· = {!   !}
        --                                         ; pres- = {!   !}
        --                                         ; pres⋆ = {!   !}
        --                                         }
        FPWSpec : FPNilpAlg3 → Type ℓ
        FPWSpec W = Spec (FPAlg→CommAlgebra (fst W))

        spec-pt : (W : FPNilpAlg3) → FPWSpec W
        spec-pt W = ψ∘ϕ W
          
        --open Theory {ℓ} {ℓ} {k} 
               
        --spec_pt : (W : FreeCommAlgebra (CommRing→Ring k) ℓ) → ASpec {ℓ} {k} W
        --spec_pt W = {! inducedHom  !}
                 