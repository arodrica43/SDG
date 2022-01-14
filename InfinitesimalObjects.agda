{-# OPTIONS --cubical #-}

module SDG.InfinitesimalObjects where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.FinData
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra -- Some of this imports should be moved to Base
  open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  open import Cubical.Algebra.CommAlgebra.FGIdeal
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Data.Nat
  open import Cubical.Algebra.RingSolver.Reflection
  open import SDG.Base renaming (_^_ to pow) 

  private
    variable
      ℓ : Level

  module _ {k : CommRing ℓ} where
    D : ℕ → Type ℓ
    D n = Σ (k-as-type {ℓ} {k}) λ x → pow {ℓ} {k} x (suc n) ≡ 0r {ℓ} {k}

    D∞ = Σ ℕ λ n → D n

    FundFPNA : {m : ℕ} (n : ℕ)(r : FinVec ℕ n) → k-Alg {ℓ} {k}
    FundFPNA n r = makeFPAlgebra {m = n} n (exp-var-vec (vec-suc {ℓ} {k} r))

    FreeFPNA : {m : ℕ}(n : ℕ)(r : FinVec ℕ n)(v : FinVec (fst (FundFPNA {n} n r)) m) → k-Alg
    FreeFPNA n r v = FundFPNA {n} n r / generatedIdeal (FundFPNA {n} n r) v
  
    k[ε] = FundFPNA {1} 1 λ x → 2

    k[ε]-zero : fst k[ε]
    k[ε]-zero = CommAlgebraStr.0a (snd k[ε]) -- This 0a should be in Base

    Disk = D 1
    
    0D : Disk
    0D = 0r {ℓ} {k} , solve k -- solving simplification with RingSolver
 