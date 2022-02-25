{-# OPTIONS --cubical #-}

module SDG.KockLawvere where

  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.CommRing
  open import SDG.Base
  open import SDG.Nilpotent
  open Foundations

  variable
    ℓ : Level
    k : CommRing ℓ

  FPNcanonical : {W :  FPNilpAlg k} → (w : fst (FPNilpAlg→CommAlgebra k W)) → (Spec (FPNilpAlg→CommAlgebra k W) → fst (k-as-algebra {ℓ} {k}))
  FPNcanonical w = λ d → d .fst w

  postulate 
    --Kock-Lawvere : (W : FPAlg) → isIso (canonical {ℓ} {k} {FPAlg→CommAlgebra W}) -- KL axiom for FPAs
    Kock-Lawvere : (W : FPNilpAlg k) → isIso (FPNcanonical {ℓ} {k} {W})

  --FPNcanonical-inv : {W :  FPNilpAlg k} → (Spec (FPNilpAlg→CommAlgebra k W) → fst (k-as-algebra {ℓ} {k})) → fst (FPNilpAlg→CommAlgebra k W)
  --FPNcanonical-inv {W = W} g = {!  !} 

  FPNcanonical-inv : {W : FPNilpAlg k} → (Spec (FPNilpAlg→CommAlgebra k W) → fst (k-as-algebra {ℓ} {k})) → fst (FPNilpAlg→CommAlgebra k W)
  FPNcanonical-inv {W = W} = fst (Kock-Lawvere W)

  --FPNcanonical : {W :  FPNilpAlg k} → (w : fst (FPNilpAlg→CommAlgebra k W)) → (Spec (FPNilpAlg→CommAlgebra k W) → fst (k-as-algebra {ℓ} {k}))
  --FPNcanonical w = λ d → d .fst w  --λ d → evalAt {FPNilpAlg→CommAlgebra k W} d w
 
  --canonical-inv : (W : FPNilpAlg k) → (Spec (FPNilpAlg→CommAlgebra k W) → fst (k-as-algebra {ℓ} {k})) → fst (FPNilpAlg→CommAlgebra k W)
  --canonical-inv W g = fst {! Kock-Lawvere  !}
   