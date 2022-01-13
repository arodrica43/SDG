{-# OPTIONS --cubical #-}

module SDG.Basics where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.FinData
  
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  open import Cubical.Algebra.CommAlgebra.Ideal
  open import Cubical.Algebra.CommAlgebra.FGIdeal
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.Instances.FreeCommAlgebra
  open import Cubical.Data.Nat
  open import Cubical.Data.Unit
  open import Cubical.Algebra.Ring.BigOps
  open import Cubical.Algebra.RingSolver.Reflection

  private
    variable
      ℓ : Level
      C : fst (freeAlgebra (suc zero))

  module _ {k : CommRing ℓ} where
    open KroneckerDelta (CommRing→Ring k)
    k-as-algebra : CommAlgebra k ℓ
    k-as-algebra = freeAlgebra 0

    k-as-type : Type ℓ
    k-as-type = fst k
    
    k-Alg = CommAlgebra k ℓ

    0r =  CommRingStr.0r (snd k)
    1r =  CommRingStr.1r (snd k)
    
    _*_ : k-as-type → k-as-type → k-as-type
    x * y = (snd k CommRingStr.· x) y
    
    k-action : {W : k-Alg} → k-as-type → (fst W) → (fst W)
    k-action {W = W} r a = (snd W CommAlgebraStr.⋆ r) a


    _^_ : k-as-type → ℕ → k-as-type
    x ^ zero = 1r
    x ^ suc n =  (x ^ n) * x

    D : ℕ → Type ℓ
    D n = Σ k-as-type λ x → x ^ (suc n) ≡ 0r

    D∞ = Σ ℕ λ n → D n

    ξ : {n : ℕ} → Fin n → fst (freeAlgebra {ℓ} {k} n)
    ξ i = Construction.var i

    exp-var : {n : ℕ} → Fin n → ℕ → fst (freeAlgebra {ℓ} {k} n)
    exp-var i zero = Construction.1a k
    exp-var i (suc n) = (ξ i) Construction.· (exp-var i n)

    constant :  {n : ℕ} → fst k → fst (freeAlgebra {ℓ} {k} n)
    constant a = Construction.const a

    monomial : {n : ℕ} → fst k → Fin n → ℕ → fst (freeAlgebra {ℓ} {k} n)
    monomial a i n = (constant a) Construction.· (exp-var i n)

    exp-var-vec : {n : ℕ} → FinVec ℕ n →  FinVec (fst (freeAlgebra {ℓ} {k} n)) n
    exp-var-vec r = λ i → exp-var i (r i)

    vec-suc : {n : ℕ} → FinVec ℕ n → FinVec ℕ n -- From a vector (i₁,...,iₙ), returns (i₁ + 1,...,iₙ + 1)
    vec-suc v = λ i → suc (v i)

    FundWeilAlgebra : {m : ℕ} (n : ℕ)(r : FinVec ℕ n) → k-Alg
    FundWeilAlgebra n r = makeFPAlgebra {m = n} n (exp-var-vec (vec-suc r))

    FreeWeilAlgebra : {m : ℕ}(n : ℕ)(r : FinVec ℕ n)(v : FinVec (fst (FundWeilAlgebra {n} n r)) m) → k-Alg
    FreeWeilAlgebra n r v = FundWeilAlgebra {n} n r / generatedIdeal (FundWeilAlgebra {n} n r) v
  
    k[ε] = FundWeilAlgebra {1} 1 λ x → 2

    k[ε]-zero : fst k[ε]
    k[ε]-zero = CommAlgebraStr.0a (snd k[ε])

    FPAlg : Type _
    FPAlg = Σ (Type ℓ) λ X → Σ ℕ (λ m → Σ ℕ (λ n → Σ (FinVec (fst (freeAlgebra {ℓ} {k} n)) m) λ v → X ≡ (fst (makeFPAlgebra {ℓ} n v))))
    
    getCommAlg : FPAlg → k-Alg
    getCommAlg W = makeFPAlgebra {ℓ} (fst (snd (snd W))) (fst (snd (snd (snd W))))

    Spec : k-Alg → Type ℓ
    Spec W = CommAlgebraHom W k-as-algebra

    --base-pt : {W : k-Alg} → Spec W
    --base-pt {W = W} = 
      
    --trivial-morph : {W : k-Alg} → fst k → fst k-as-algebra
    --trivial-morph {W = W} w = (snd k-as-algebra CommAlgebraStr.⋆ w) (CommAlgebraStr.1a (snd k-as-algebra))
    
    evalAt : {W : k-Alg}(d : Spec W)(w : fst W) → fst k-as-algebra
    evalAt d w = d .fst w -- is this correct?

    canonical : {W : k-Alg}(w : fst W) → (Spec W → fst k-as-algebra)
    canonical {W = W} w = λ d → evalAt {W} d w

    postulate
        Kock-Lawvere : (W : FPAlg) → isIso (canonical {getCommAlg W})

    --coefficients : {W : k-Alg} → (Spec W → fst k-as-algebra) → fst W
    --coefficients f = {!   !}

    --Disk = Spec k[ε]
    Disk = D 1
    -- center : Unit → Disk
    -- center ⋆ = 
    --   makeCommAlgebraHom {M = k[ε]} {N = k-as-algebra} 
    --   (λ x → (k Construction.⋆ {! 0r !}) (Construction.const {!   !})) 
    --   {!   !} {!   !} {!   !} {!   !}

    TangentSpace : Type ℓ → Type ℓ
    TangentSpace X = Disk → X
    
    0D : Disk
    0D = 0r , solve k -- solving simplification with RingSolver

    Tangent-space-of_at_ : (X : Type ℓ) → (x : X) → Type ℓ
    Tangent-space-of X at x = Σ (Disk → X) (λ f → f 0D ≡ x) -- Tangent vectors are terms of this type

    VecField : (X : Type ℓ) → Type ℓ
    VecField X = (x : X) → Tangent-space-of X at x

    first-DE : {X : Type ℓ} → VecField X → Type ℓ
    first-DE {X = X} F = (x : X) → F x ≡ ((λ d → x) , λ i → x)
