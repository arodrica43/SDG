{-# OPTIONS --cubical #-}

module SDG.KockLawvere where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.CommRing
  open import SDG.Base

  private
    variable
      ℓ : Level

 
  postulate -- KL axiom for FPAs
      Kock-Lawvere : (W : FPAlg) → isIso (canonical {ℓ} {k} {getCommAlg W})

  -- TO DO :: KL axiom for FPNAs. Axiom variations. 