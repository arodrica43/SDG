{-# OPTIONS --cubical #-}

module SDG.Basics where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.FinData
  
  open import Cubical.Algebra.Ring        using ()
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.Instances.FreeCommAlgebra
  open import Cubical.Data.Nat
  open import Cubical.Algebra.Ring.BigOps

  private
    variable
      ℓ : Level
      n : ℕ
      C : fst (freeAlgebra (suc zero))

  module _ {k : CommRing ℓ} where
    open KroneckerDelta (CommRing→Ring k)
    k-as-type : Type ℓ
    k-as-type = fst k
    
    0r =  CommRingStr.0r (snd k)
    1r =  CommRingStr.1r (snd k)
    
    _*_ : k-as-type → k-as-type → k-as-type
    x * y = (snd k CommRingStr.· x) y
    
    _^_ : k-as-type → ℕ → k-as-type
    x ^ zero = 1r
    x ^ suc n =  (x ^ n) * x

    D : ℕ → Type ℓ
    D n = Σ k-as-type λ x → x ^ n ≡ 0r

    ξ : {n : ℕ} → Fin n → fst (freeAlgebra {ℓ} {k} n)
    ξ i = Construction.var i

    exp-var : {n : ℕ} → Fin n → ℕ → fst (freeAlgebra {ℓ} {k} n)
    exp-var i zero = Construction.1a k
    exp-var i (suc n) = (ξ i) Construction.· (exp-var i n)

    constant :  {n : ℕ} → fst k → fst (freeAlgebra {ℓ} {k} n)
    constant a = Construction.const a

    monomial : {n : ℕ} → fst k → Fin n → ℕ → fst (freeAlgebra {ℓ} {k} n)
    monomial a i n = (constant a) Construction.· (exp-var i n)

    Weil1 :  {m : ℕ} (n : ℕ) → (r : ℕ) → CommAlgebra k ℓ
    Weil1 n r = makeFPAlgebra {m = 1} 1 λ x → exp-var zero r
 
  

    