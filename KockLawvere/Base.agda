{-# OPTIONS --cubical #-}

module SDG.KockLawvere.Base where

  open import Cubical.Foundations.Everything renaming (const to consts)
  open import Cubical.Data.FinData
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra renaming (_[_] to _⟦_⟧)
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_ ; 
                                          +-assoc to +-assocℕ ; +-comm to +-commℕ ;
                                          ·-assoc to ·-assocℕ ; ·-comm to ·-commℕ)
  open import Cubical.Foundations.Powerset
  open import Cubical.Data.Sigma
  open import Cubical.Algebra.Ring.BigOps
  open import Cubical.HITs.SetQuotients renaming (_/_ to _//_)
  open import Cubical.HITs.PropositionalTruncation
  open import Cubical.Data.Fin.LehmerCode 
  open import Cubical.Algebra.CommRing.FGIdeal renaming (generatedIdeal to genIdealRing)
  open import Cubical.Algebra.CommAlgebra.FGIdeal
  open import SDG.Base
  open import SDG.Nilpotent.Base
  open import SDG.Infinitesimal.Base


  module Axiom (ℝ@(R , str) : CommRing ℓ) where

    open Foundations ℝ
    open Spectrum ℝ
    open WeilAlgebra ℝ
    open InfExperimental ℝ
    postulate
      KL1 : isIso canMap1
      KL : (n : ℕ) → isIso (canMap n)
      FKL : (n : ℕ) → isIso (fcanMap n)
      NKL : (n : ℕ)(A : CommAlgebra ℝ ℓ) → isIso (canonical n A)
    invMAP : (n : ℕ)(A : CommAlgebra ℝ ℓ) → (infDskOfOrder A n → ⟨ A ⟩) → ⟨ W n ⟩
    invMAP n A = fst (NKL n A)


    invMap :  (n : ℕ) → (Spec (W n) → ⟨ A ⟩) → ⟨ A[ξ] ⟩
    invMap n = fst (KL n)
    invMap1 :  (Spec (W 1) → ⟨ A ⟩) → ⟨ A[ξ] ⟩
    invMap1 = fst KL1
    finvMap : (n : ℕ) → (Spec (W n) → ⟨ A ⟩) → ⟨ W n ⟩
    finvMap n = fst (FKL n)

  module Derivative (ℝ@(R , str) : CommRing ℓ) where
    open Foundations ℝ
    open Construction ℝ
    d/dξ : ⟨ A[ξ] ⟩ → ⟨ A[ξ] ⟩
    d/dξ (const c) = 0a
    d/dξ (var i) = 1a
    d/dξ (p + q) = (d/dξ p) + (d/dξ q)
    d/dξ (- p) = - (d/dξ p)
    d/dξ (p · q) = ((d/dξ p) · q) + (p · (d/dξ q))
    d/dξ (+-assoc p q r i) = +-assoc (d/dξ p) ((d/dξ q)) ((d/dξ r)) i
    d/dξ (+-rid p i) = +-rid (d/dξ p) i
    d/dξ (+-rinv p i) = +-rinv (d/dξ p) i
    d/dξ (+-comm p q i) = +-comm (d/dξ p) (d/dξ q) i
    d/dξ (·-assoc p q r i) = (((d/dξ p · (q · r)) + (p · ((d/dξ q · r) + (q · d/dξ r)))) ≡⟨ cong (λ a → a + (p · ((d/dξ q · r) + (q · d/dξ r)))) (·-assoc (d/dξ p) q r) ⟩ 
                              (((d/dξ p · q ) · r) + (p · ((d/dξ q · r) + (q · d/dξ r)))) ≡⟨ cong (λ a → ((d/dξ p · q ) · r) + a) (·-comm p ((d/dξ q · r) + (q · d/dξ r))) ⟩ 
                              (((d/dξ p · q ) · r) + (((d/dξ q · r) + (q · d/dξ r)) · p)) ≡⟨ cong (λ a → ((d/dξ p · q ) · r) + a) (ldist (d/dξ q · r) (q · d/dξ r) p) ⟩ 
                              (((d/dξ p · q ) · r) + (((d/dξ q · r) · p) + ((q · d/dξ r) · p))) ≡⟨ +-assoc ((d/dξ p · q) · r) ((d/dξ q · r) · p) ((q · d/dξ r) · p) ⟩ 
                              ((((d/dξ p · q ) · r) + ((d/dξ q · r) · p)) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + a) + ((q · d/dξ r) · p)) (sym (·-assoc (d/dξ q) r p)) ⟩ 
                              ((((d/dξ p · q ) · r) + (d/dξ q · (r · p))) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + (d/dξ q · a)) + ((q · d/dξ r) · p)) (·-comm r p) ⟩ 
                              ((((d/dξ p · q ) · r) + (d/dξ q · (p · r))) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + a) + ((q · d/dξ r) · p)) (·-assoc (d/dξ q) p r) ⟩
                              ((((d/dξ p · q ) · r) + ((d/dξ q · p) · r)) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → a + ((q · d/dξ r) · p)) (sym (ldist (d/dξ p · q) (d/dξ q · p) r)) ⟩ 
                              ((((d/dξ p · q ) + (d/dξ q · p)) · r) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) + a) · r) + ((q · d/dξ r) · p)) (·-comm (d/dξ q) p) ⟩ 
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + a) (sym (·-assoc q (d/dξ r) p)) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · (d/dξ r · p))) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · a)) (·-comm (d/dξ r) p) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · (p · d/dξ r))) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + a) (·-assoc q p (d/dξ r)) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + ((q · p) · d/dξ r)) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + (a · d/dξ r)) (·-comm q p) ⟩
                              ((((d/dξ p · q) + (p · d/dξ q)) · r) + ((p · q) · d/dξ r)) ∎) i
    d/dξ (·-lid p i) = (((0a · p) + (1a · d/dξ p)) ≡⟨ cong (λ a → a + (1a · (d/dξ p))) (RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) p) ⟩ 
                        (0a + (1a · d/dξ p)) ≡⟨ (+-comm 0a (1a · d/dξ p)) ∙ (+-rid (1a · d/dξ p)) ⟩ 
                        (1a · d/dξ p) ≡⟨ ·-lid (d/dξ p) ⟩ 
                        d/dξ p ∎) i
    d/dξ (·-comm p q i) = ((d/dξ p · q) + (p · d/dξ q) ≡⟨ +-comm (d/dξ p · q) (p · d/dξ q) ⟩ 
                           (p · d/dξ q) + (d/dξ p · q) ≡⟨ cong (λ a → a + (d/dξ p · q)) (·-comm p (d/dξ q)) ⟩ 
                           (d/dξ q · p) + (d/dξ p · q) ≡⟨ cong (λ a → (d/dξ q · p) + a) (·-comm (d/dξ p) q) ⟩ 
                           (d/dξ q · p) + (q · d/dξ p) ∎) i
    d/dξ (ldist p q r i) = ((((d/dξ p + d/dξ q) · r) + ((p + q) · d/dξ r)) ≡⟨ cong (λ a → a + ((p + q) · d/dξ r)) (ldist (d/dξ p) (d/dξ q) r) ⟩ 
                            (((d/dξ p · r) + (d/dξ q · r)) + ((p + q) · d/dξ r)) ≡⟨ cong (λ a → ((d/dξ p · r) + (d/dξ q · r)) + a) (ldist p q (d/dξ r)) ⟩ 
                            (((d/dξ p · r) + (d/dξ q · r)) + ((p · d/dξ r) + (q · d/dξ r))) ≡⟨ +-assoc ((d/dξ p · r) + (d/dξ q · r)) (p · d/dξ r) (q · d/dξ r) ⟩ 
                            ((((d/dξ p · r) + (d/dξ q · r)) + (p · d/dξ r)) + (q · d/dξ r)) ≡⟨ cong (λ a → a + (q · d/dξ r)) (sym (+-assoc (d/dξ p · r) (d/dξ q · r) (p · d/dξ r))) ⟩ 
                            (((d/dξ p · r) + ((d/dξ q · r) + (p · d/dξ r))) + (q · d/dξ r)) ≡⟨ cong (λ a → ((d/dξ p · r) + a) + (q · d/dξ r)) (+-comm (d/dξ q · r) (p · d/dξ r)) ⟩ 
                            (((d/dξ p · r) + ((p · d/dξ r) + (d/dξ q · r))) + (q · d/dξ r)) ≡⟨ cong (λ a → a + (q · d/dξ r)) (+-assoc (d/dξ p · r) (p · d/dξ r) (d/dξ q · r)) ⟩ 
                            ((((d/dξ p · r) + (p · d/dξ r)) + (d/dξ q · r)) + (q · d/dξ r)) ≡⟨ sym (+-assoc ((d/dξ p · r) + (p · d/dξ r)) (d/dξ q · r) (q · d/dξ r)) ⟩ 
                            (((d/dξ p · r) + (p · d/dξ r)) + ((d/dξ q · r) + (q · d/dξ r))) ∎) i
    d/dξ (+HomConst s t i) = sym (+-rid 0a) i
    d/dξ (·HomConst s t i) = (0a ≡⟨ sym (+-rid 0a) ⟩ 
                              (0a + 0a) ≡⟨ cong (λ a → 0a + a) step1 ⟩ 
                              (0a + ((const s) · 0a)) ≡⟨ cong (λ a → a + ((const s) · 0a)) step2 ⟩ 
                              ((0a · (const t)) + ((const s) · 0a)) ∎) i
      where
        step1 : 0a ≡ (const s · 0a)
        step1 = sym (RingTheory.0RightAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) (const s))
        step2 : 0a ≡ 0a · (const t)
        step2 = sym (RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) (const t))
    d/dξ (0-trunc p q α β i j) = isSetCommAlgebra A[ξ] (d/dξ p) (d/dξ q) (cong d/dξ α) (cong d/dξ β) i j

    
    lem1 : (n : ℕ)(P : ⟨ A[ξ] ⟩) → d/dξ (exp-num {A = A[ξ]} P (suc n)) ≡ (embedℕinAlg A[ξ] (suc n)) · ((exp-num {A = A[ξ]} P n) · (d/dξ P))
    lem1 zero P = d/dξ (exp-num {A = A[ξ]} P 1) ≡⟨ cong (λ a → d/dξ a) help1 ⟩ 
                  d/dξ P ≡⟨ sym (·-lid (d/dξ P)) ⟩ 
                  (exp-num {A = A[ξ]} P zero · d/dξ P) ≡⟨ sym (·-lid (exp-num {A = A[ξ]} P zero · d/dξ P)) ⟩
                  (1a ·  (exp-num {A = A[ξ]} P zero · d/dξ P)) ≡⟨ cong (λ a → a · (exp-num {A = A[ξ]} P zero · d/dξ P)) help2 ⟩
                  (embedℕinAlg A[ξ] 1 · (exp-num {A = A[ξ]} P zero · d/dξ P)) ∎
      where
        help1 : (P · 1a) ≡ P
        help1 = (·-comm P 1a) ∙ (·-lid P)
        help2 : 1a ≡ 0a + 1a
        help2 = sym ((+-comm 0a 1a) ∙ (+-rid 1a))
    lem1 (suc n) P = d/dξ (exp P (suc (suc n))) ≡⟨ refl ⟩   
                     d/dξ (P · exp P (suc n)) ≡⟨ refl ⟩  
                     ((d/dξ P · exp P (suc n)) + (P · d/dξ (exp P (suc n)))) ≡⟨ cong (λ a → (d/dξ P · exp P (suc n)) + (P · a)) (lem1 n P) ⟩  
                     ((d/dξ P · exp P (suc n)) + (P · (n+1 · ((exp P n) · (d/dξ P))))) ≡⟨ cong (λ a → a + ((P · (n+1 · P^nP')))) (·-comm (d/dξ P) (exp P (suc n))) ⟩  
                     (P^snP' + (P · (n+1 · P^nP'))) ≡⟨ cong (λ a → P^snP' + a) ((·-assoc P n+1 P^nP') ∙ 
                                                                                (cong (λ a → a · P^nP') (·-comm P n+1)) ∙ 
                                                                                sym (·-assoc n+1 P P^nP')) ⟩
                     (P^snP' + (n+1 · (P · ((exp P n) · (d/dξ P))))) ≡⟨ cong (λ a → P^snP' + (n+1 · a))  (·-assoc P (exp P n) (d/dξ P)) ⟩  
                     (P^snP' + (n+1 · ((P · (exp P n)) · (d/dξ P)))) ≡⟨ cong (λ a → P^snP' + (n+1 · (a · (d/dξ P)))) refl ⟩
                     (P^snP' + (n+1 · P^snP')) ≡⟨ cong (λ a → a + (n+1 · P^snP')) (sym (·-lid P^snP')) ⟩
                     ((1a · P^snP') + (n+1 · P^snP')) ≡⟨ sym (ldist 1a n+1 P^snP') ⟩  
                     ((1a + n+1) · P^snP') ≡⟨ cong (λ a → a · P^snP') help1 ⟩
                     (n+2 · P^snP') ∎
      where
        n+1 = embedℕinAlg A[ξ] (suc n)
        n+2 = embedℕinAlg A[ξ] (suc (suc n))
        exp = exp-num {A = A[ξ]}
        P^nP' = exp P n · d/dξ P
        P^snP' = exp P (suc n) · d/dξ P
        help1 : (1a + n+1) ≡ (n+1 + 1a) -- ≡ n+2
        help1 = +-comm 1a n+1
    
    lem2 : (n : ℕ) → d/dξ (var-power n zero) ≡ (embedℕinAlg A[ξ] (suc n)) · ((exp-num {A = A[ξ]} (ξ zero) n) · (d/dξ (ξ zero)))
    lem2 n = lem1 n (ξ zero)

    link : (n : ℕ) → ⟨ W n ⟩ ≡ ⟨ FPAlgebra2 1 (var-power (suc n)) (var-power n) ⟩
    link n = makeFP1Char 1 (var-power n) ∙ (sym (makeFP2Char 1 (var-power (suc n)) (var-power n))) --(makeFP1Char 1 (var-power n)) ∙ sym (makeFP2Char 1 (var-power (suc n)) (var-power n))

    pred/dε : (n : ℕ) → ⟨ W (suc n) ⟩ → ⟨ FPAlgebra2 1 (var-power (suc n)) (var-power n) ⟩
    pred/dε n = makeFPMap2 1 (var-power (suc n)) (var-power n) d/dξ help1
      where
        lc = linearCombination R[ξ]
        derivReducesDeg : (a b : ⟨ A[ξ] ⟩) → Type ℓ
        derivReducesDeg a b = ∥ Σ (FinVec ⟨ A[ξ] ⟩ 1) (λ x → ((d/dξ a) + (- (d/dξ b))) ≡ linearCombination R[ξ] x (var-power n)) ∥₁

        help1 : (a b : ⟨ A[ξ] ⟩) → ((a + (- b)) ∈ fst (relationsIdeal 1 (var-power (suc n)))) → 
                derivReducesDeg a b
        help1 a b r = map decreaseDeg r
          where
            decreaseDeg : Σ (FinVec ⟨ Polynomials 1 ⟩ 1) (λ x → (a + (- b)) ≡ linearCombination R[ξ] x (var-power (suc n))) → 
                        Σ (FinVec ⟨ Polynomials 1 ⟩ 1) λ x → (d/dξ a + (- (d/dξ b))) ≡ linearCombination R[ξ] x (var-power n)
            decreaseDeg H = factor , 
                            ((d/dξ a + (- d/dξ b))                                                                                                    ≡⟨ refl ⟩ 
                            d/dξ (a + (- b))                                                                                                          ≡⟨ cong (λ z → d/dξ z) (snd H) ⟩
                            d/dξ (linearCombination R[ξ] (fst H) (var-power (suc n)))                                                                 ≡⟨ refl ⟩
                            d/dξ (((fst H zero) · (var-power (suc n) zero)) + 0a)                                                                     ≡⟨ cong (λ z → d/dξ z) (+-rid ((fst H zero) · (var-power (suc n) zero))) ⟩
                            d/dξ ((fst H zero) · (var-power (suc n) zero))                                                                            ≡⟨ refl ⟩
                            (((d/dξ (fst H zero)) · (var-power (suc n) zero)) + ((fst H zero) · (d/dξ (var-power (suc n) zero))))                     ≡⟨ refl ⟩
                            (((d/dξ (fst H zero)) · ((ξ zero) · (var-power n zero))) + ((fst H zero) · (d/dξ (var-power (suc n) zero))))              ≡⟨ cong (λ z → z + ((fst H zero) · (d/dξ (var-power (suc n) zero)))) (·-assoc (d/dξ (fst H zero)) (ξ zero) (var-power n zero)) ⟩
                            (expr + ((fst H zero) · (d/dξ (var-power (suc n) zero))))                                                                 ≡⟨ cong (λ z → expr + ((fst H zero) · z)) helper1 ⟩
                            (expr + ((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · (exp-num {A = A[ξ]} (ξ zero) (suc n) · d/dξ (ξ zero)))))        ≡⟨ refl ⟩
                            (expr + ((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · (var-power n zero · d/dξ (ξ zero)))))                           ≡⟨ cong (λ z → expr + ((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · z))) (·-comm (var-power n zero) (d/dξ (ξ zero))) ⟩
                            (expr + ((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · (d/dξ (ξ zero) · var-power n zero))))                           ≡⟨ cong (λ z → expr + ((fst H zero) · z)) (·-assoc (embedℕinAlg A[ξ] (suc (suc n))) (d/dξ (ξ zero)) (var-power n zero)) ⟩
                            (expr + ((fst H zero) · ((embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero)) · var-power n zero)))                           ≡⟨ cong (λ z → expr + z) (·-assoc (fst H zero) (embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero)) (var-power n zero)) ⟩
                            (expr + (((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero))) · var-power n zero))                           ≡⟨ sym (ldist (d/dξ (fst H zero) · ξ zero) (fst H zero · (embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero))) (var-power n zero)) ⟩
                            (((d/dξ (fst H zero) · ξ zero) +  (fst H zero · (embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero)))) · var-power n zero)    ≡⟨ cong (λ z → ((d/dξ (fst H zero) · ξ zero) +  (fst H zero · z)) · var-power n zero) ((·-comm (embedℕinAlg A[ξ] (suc (suc n))) (d/dξ (ξ zero))) ∙ (·-lid (embedℕinAlg A[ξ] (suc (suc n))))) ⟩
                            (((d/dξ (fst H zero) · ξ zero) +  (fst H zero · (embedℕinAlg A[ξ] (suc (suc n))))) · var-power n zero)                    ≡⟨ cong (λ z → ((d/dξ (fst H zero) · ξ zero) +  z) · var-power n zero) (·-comm (fst H zero) (embedℕinAlg A[ξ] (suc (suc n)))) ⟩
                            (((d/dξ (fst H zero) · ξ zero) +  ((embedℕinAlg A[ξ] (suc (suc n))) · fst H zero)) · var-power n zero)                    ≡⟨ sym (+-rid (factor zero · var-power n zero)) ⟩
                            linearCombination R[ξ] factor (var-power n) ∎)
              where
                expr = (d/dξ (fst H zero) · (ξ zero)) · (var-power n zero)
                helper1 : d/dξ (var-power (suc n) zero) ≡ (embedℕinAlg A[ξ] (suc (suc n)) · (exp-num {A = A[ξ]} (ξ zero) (suc n) · d/dξ (ξ zero)))
                helper1 = lem2 (suc n) 
                factor : FinVec ⟨ Polynomials 1 ⟩ 1
                factor = λ _ → (d/dξ (fst H zero) · ξ zero) +  ((embedℕinAlg A[ξ] (suc (suc n))) · fst H zero)

    d/dε : (n : ℕ) → ⟨ W (suc n) ⟩ → ⟨ W n ⟩
    d/dε n x = transport (sym (link n)) (pred/dε n x)
    open Axiom ℝ

    open InfExperimental ℝ   

    factCoeff : (n : ℕ) → ⟨ W n ⟩ → ⟨ A ⟩
    factCoeff zero p = evPoly2 zero A p (λ x → 0d A zero)
    factCoeff (suc n) p = factCoeff n (d/dε n p)

    d/dx : (n : ℕ)(f : ⟨ A ⟩ → ⟨ A ⟩) → ⟨ A ⟩ → ⟨ A ⟩
    d/dx n f a = factCoeff n (invMAP n A λ d → f (((snd A) CommAlgebraStr.+ a) (fromZeroLocus₁ 1 (var-power n) A d zero))) --((snd A) CommAlgebraStr.+ a) (fromZeroLocus₁ 1 (var-power n) A d zero)) 
    
    open import Cubical.Data.Bool

    ∂/∂x : (n k : ℕ) → Fin n → (⟨ A^ n ⟩ → ⟨ A ⟩) → ⟨ A^ n ⟩ → ⟨ A ⟩
    ∂/∂x n k j f v = factCoeff k (invMAP k A (λ d → f (λ i → if reclift n i == j then ((snd A) CommAlgebraStr.+ (v i)) (fromZeroLocus₁ 1 (var-power k) A d zero) else v i))) --d/dx 1 (λ x → f (λ i → if (i == k) then x else (v i)))

    anODE : Type ℓ
    anODE = Σ (⟨ A ⟩ → ⟨ A ⟩) λ f → (x : ⟨ A ⟩) → (d/dx 1 f x) ≡ x

    -- sol : anODE 
    -- sol = (λ _ → 0a) , λ x → d/dx 1 (λ _ → 0a) x ≡⟨ refl ⟩ 
    --                          factCoeff 1 (invMAP 1 A (λ d → 0a)) ≡⟨ refl ⟩ 
    --                          evPoly2 zero A (d/dε 0 (invMAP 1 A (λ d → 0a))) (λ x₁ → 0d A zero) ≡⟨ {!   !} ⟩ 
    --                          {!   !} ≡⟨ {!   !} ⟩
    --                          {!   !} ∎