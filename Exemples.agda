{-# OPTIONS --cubical --safe #-}
module SDG.Exemples where

open import Cubical.Foundations.Everything


data ℕ : Type where
    zero : ℕ
    suc : ℕ → ℕ

suma : ℕ → ℕ → ℕ
suma zero zero = zero
suma zero (suc n) = suc n
suma (suc n) zero = suc n
suma (suc n) (suc m) = suc (suc (suma n m))
 