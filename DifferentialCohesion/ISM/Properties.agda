{-# OPTIONS --cubical --safe #-}

module SDG.DifferentialCohesion.ISM.Properties where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.Nat
  open import Cubical.Data.FinData
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Modalities.Modality
  open import Cubical.Foundations.Equiv.PathSplit
  
  open import Cubical.HITs.Localization renaming (rec to Lrec)
  open import Cubical.HITs.Nullification renaming (elim to elim-Null ; rec to Nrec)
  open import Cubical.Data.Unit
  open import Cubical.Data.Empty
  open import Cubical.Functions.Embedding

  open import SDG.Base
  open import SDG.Infinitesimals.Instances
  open import SDG.WeilAlgebra.Instances
  open import SDG.Infinitesimals.Base
  open import SDG.DifferentialCohesion.ISM.Base

  module BasicProperties (ℝ@(R , str) : CommRing ℓ) where

    open 1Disk ℝ
    open BasicInstances ℝ
    open RingUtils (CommAlgebra→CommRing A)
    open 1DFreeCommAlgebraUtils ℝ
    open NullProperties (infDskOfOrder∞ A)
    open CommRingStr (snd (CommAlgebra→CommRing A))
    private
      D = infDskOfOrder∞ A
      ι : D → ⟨ A ⟩
      ι d = fromZeroLocus₁ 1 (var-power (fst d)) A (snd d) zero
      _at_ = polynomialAt
      infDispl : {n : ℕ} → FinVec ⟨ CommAlgebra→CommRing A ⟩ n → D → ⟨ CommAlgebra→CommRing A ⟩
      infDispl p d = p at ι d
      0D : D
      0D = (1 , (0d A 1))
      
    infDisplIsNullified : (n : ℕ)(p q : FinVec ⟨ CommAlgebra→CommRing A ⟩ n) (a b : D) → η (p at ι 0D) ≡ η (q at ι 0D) →
                          η (infDispl p a) ≡ η (infDispl q b) 
    infDisplIsNullified n p q a b sC = (ηinfDispl≡ηEvalAt0 p a ∙ sC ∙ sym (ηinfDispl≡ηEvalAt0 q a)) ∙ ηinfDisplConnImg q a b
      where
        ηinfDisplConnImg : (p : FinVec ⟨ CommAlgebra→CommRing A ⟩ n) → (a b : D) → η (infDispl p a) ≡ η (infDispl p b)
        ηinfDisplConnImg p a b = precompByηContrImg (infDispl p) a b
          where
            precompByηContrImg : {X : Type ℓ}(f : D → X) (x y : D) → η (f x) ≡ η (f y)
            precompByηContrImg f x y = imageFromNullifierContr (η ∘ f) x y
        ηinfDispl≡ηEvalAt0 : (p : FinVec ⟨ CommAlgebra→CommRing A ⟩ n)(a : D) → η (infDispl p a) ≡ η (p at ι 0D)
        ηinfDispl≡ηEvalAt0 p a =  (ηinfDisplConnImg p a 0D) ∙ cong η refl

  module KillInfinitesimalDisk (ℝ@(R , str) : CommRing ℓ)(A : CommAlgebra ℝ ℓ) where
    
    open BasicInstances ℝ renaming (A to R[⊥])
    open 1Disk ℝ -- n-disk → ∞-disk
    open 1DFundamentalWeilAlgebras ℝ
    open 1DFreeCommAlgebraUtils ℝ
    open NullProperties (infDskOfOrder∞ A) -- Nullification at the ∞-disk
    open AlgebraSpectrum ℝ A
    private
      ∗ = Unit*

    -- Final Theorem 1 :: Nullification at infDiskOfOrder∞ nullifies all infDsisksOfOrder n
    ℑKillDisksOfAnyOrder : (n : ℕ) → Iso {ℓ} {ℓ} (◯ (infDskOfOrder A n)) ∗
    ℑKillDisksOfAnyOrder n = RetrNullifierReflectsToUnitIso (incl A n) (retr A n) (isRetrRetr n A)

    -- Final Theorem 2 :: ℑ Kills Fundamental FPNAs
    ℑKill1DFundFPNAs : (n : ℕ) → Iso (◯ (Spec (W n))) ∗
    ℑKill1DFundFPNAs n = compIso (ℑhelperIso n) (ℑKillDisksOfAnyOrder n)
      where
        -- Helper Lemma :: ℑ preserves FPHomIso, via equivalences
        ℑhelperIso : (n : ℕ) → Iso (◯ (Spec (W n)))  (◯ (infDskOfOrder A n))
        ℑhelperIso n = equivToIso (◯-map (fst (isoToEquiv (FPHomIso 1 (var-power n)))) , 
                                        (◯-preservesEquiv (fst (isoToEquiv (FPHomIso 1 (var-power n)))) 
                                                            (snd (isoToEquiv (FPHomIso 1 (var-power n))))))

