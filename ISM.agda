{-# OPTIONS --cubical #-}

module SDG.ISM where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.CommRing

  private
    variable
      ℓ : Level
    
  module _ {k : CommRing ℓ} where
    -- TO DO :: Implement ISM as localization at D∞