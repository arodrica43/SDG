{-# OPTIONS --cubical #-}
module SDG.Nilpotent.Instances where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.FinData
  open import Cubical.Data.Nat
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra -- Some of this imports should be moved to Base
  open import Cubical.HITs.SetQuotients renaming (_/_ to _//_)
  open import Cubical.HITs.PropositionalTruncation
  open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  open import Cubical.Algebra.CommAlgebra.FGIdeal
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Data.Sigma
  open import SDG.Base 
  open Foundations renaming (_^_ to pow)
  variable
     ℓ : Level
  module _ {k : CommRing ℓ} where 
    private
      CAlg = CommAlgebra k ℓ
      k-as-alg : CAlg
      k-as-alg = freeAlgebra 0
      _Dim-freeAlg : (n : ℕ) → CAlg 
      n Dim-freeAlg = freeAlgebra {ℓ} {k} n

    -- Fundamental Weil Algebras
    -- n = Ambient dimension
    -- N r = Nilpotent Orthotope Ideal ( ξᵢ^(rᵢ + 1) ≡ 0 )
    W : (n : ℕ) → FinVec ℕ n → CAlg
    W n r = makeFPAlgebra {m = n} n (N r)
      where
        N : {n : ℕ} → FinVec ℕ n → Fin n → fst (n Dim-freeAlg) -- nilpotent orthotope  
        N r = exp-var-vec (vec-suc {ℓ} {k} r)               -- ∀ i : Fin n → gives ξᵢ^(suc (r i))

    -- Formal Weil Algebras are quotients of 
    -- Fundamental Weil Algebras by a finitely generated ideal.
    W/J : {m : ℕ}(n : ℕ)(r : FinVec ℕ n)(v : FinVec (fst (W n r)) m) → k-Alg
    W/J n r v = W n r / generatedIdeal (W n r) v

    -- There is a map π : W → W/J that has a section σ : W/J → W 

    π : {m : ℕ}{n : ℕ}{r : FinVec ℕ n}{v : FinVec (fst (W n r)) m} →
            fst (W n r) → fst (W/J n r v)
    π {n = n} {r = r} {v = v} = [_]/ {ℓ} {k} {W n r} {generatedIdeal (W n r) v}

    -- Without the Axiom of Choice, we can not ensure that every surjetion has a section.
    π-hasSect/1 : {m : ℕ}{n : ℕ}{r : FinVec ℕ n}{v : FinVec (fst (W n r)) m} →
                  (y : fst (W/J n r v)) → ∃[ x ∈ fst (W n r) ] π x ≡ y --hasSection (π {m} {n} {r} {v})
    π-hasSect/1 = []surjective 

    

    --π-hasSect/2 : {m : ℕ}{n : ℕ}{r : FinVec ℕ n}{v : FinVec (fst (W n r)) m} →
    --              {!   !} --(y : fst (W/J n r v)) → fst (W n r) --∃[ x ∈ fst (W n r) ] π x ≡ y --hasSection (π {m} {n} {r} {v})
    --π-hasSect/2 = {!   !}
    




      

    
      