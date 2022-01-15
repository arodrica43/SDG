{-# OPTIONS --cubical --safe #-}

module SDG.Ring.DirProd where

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Foundations.Everything


private
  variable
    ℓ : Level

module _ (R' S' : Ring ℓ) where
  
  private
    R = ⟨ R' ⟩
    S = ⟨ S' ⟩
    OpR = snd R' 
    OpS = snd S'
    0R = RingStr.0r OpR
    0S = RingStr.0r OpS
    1R = RingStr.1r OpR
    1S = RingStr.1r OpS
    _+R_ = RingStr._+_ OpR
    _+S_ = RingStr._+_ OpS
    _·R_ = RingStr._·_ OpR
    _·S_ = RingStr._·_ OpS
    -R_ = RingStr.-_ OpR
    -S_ = RingStr.-_ OpS
    asAbGroupR = Ring→AbGroup R'
    asAbGroupS = Ring→AbGroup S'
    isRingR = RingStr.isRing OpR
    isRingS = RingStr.isRing OpS

  asAbGroupR×S : AbGroup ℓ
  asAbGroupR×S = dirProdAb asAbGroupR asAbGroupS

  asTypeR×S : Type ℓ
  asTypeR×S = fst asAbGroupR×S

  0r : asTypeR×S
  0r = 0R , 0S
  1r : asTypeR×S
  1r = 1R , 1S

  _+_ : asTypeR×S → asTypeR×S → asTypeR×S
  u + v = (fst u +R fst v) , (snd u +S snd v)
  
  _·_ : asTypeR×S → asTypeR×S → asTypeR×S
  u · v = (fst u ·R fst v) , (snd u ·S snd v)

  -_ : asTypeR×S → asTypeR×S
  - u = (-R (fst u)) , (-S (snd u))

  sum-of-Sets-is-Set : (X Y : Type ℓ) → (p : isSet X) → (q : isSet Y) → isSet (Σ X (λ _ → Y))
  sum-of-Sets-is-Set X Y p q = λ x y u v i j → (p (fst x)
                                                 (fst y) 
                                                 (λ k → fst (u k)) 
                                                 (λ k → fst (v k)) i j) , 
                                              (q (snd x) 
                                                 (snd y) 
                                                 (λ k → snd (u k)) 
                                                 (λ k → snd (v k)) i j)
  isSetR×S : isSet asTypeR×S
  isSetR×S = sum-of-Sets-is-Set R S (isSetRing R') (isSetRing S')

  ·Assoc : (x y z : asTypeR×S) → (x · (y · z)) ≡ ((x · y) · z)
  ·Assoc x y z = λ i → IsRing.·Assoc 
                        (isRingR) 
                        (fst x) (fst y) (fst z) i , 
                       IsRing.·Assoc 
                        (isRingS) 
                        (snd x) (snd y) (snd z) i

  ·Lid : (x : asTypeR×S) → (1r · x) ≡ x
  ·Lid x = λ i → IsRing.·Lid (isRingR) (fst x) i , 
                 IsRing.·Lid (isRingS) (snd x) i
  ·Rid : (x : asTypeR×S) → (x · 1r) ≡ x
  ·Rid x = λ i → IsRing.·Rid (isRingR) (fst x) i , 
                 IsRing.·Rid (isRingS) (snd x) i

  ·asMonoidR×S : Monoid ℓ
  ·asMonoidR×S = asTypeR×S , monoidstr 1r _·_ 
                             (ismonoid (issemigroup isSetR×S 
                                                    ·Assoc) 
                                       λ x → ·Rid x , ·Lid x)

  ·Rdist+ : (x y z : asTypeR×S) → x · (y + z) ≡ (x · y) + (x · z)
  ·Rdist+ x y z = λ i → IsRing.·Rdist+ isRingR (fst x) (fst y) (fst z) i , 
                        IsRing.·Rdist+ isRingS (snd x) (snd y) (snd z) i

  ·Ldist+ : (x y z : asTypeR×S) → (x + y) · z ≡ (x · z) + (y · z)
  ·Ldist+ x y z = λ i → IsRing.·Ldist+ isRingR (fst x) (fst y) (fst z) i , 
                        IsRing.·Ldist+ isRingS (snd x) (snd y) (snd z) i

  isRingR×S : IsRing 0r 1r _+_ _·_ -_
  isRingR×S = isring (AbGroupStr.isAbGroup (snd asAbGroupR×S)) 
                     (MonoidStr.isMonoid (snd ·asMonoidR×S)) 
                     λ x y z → (·Rdist+ x y z) , (·Ldist+ x y z)

  asRingR×S : Ring ℓ
  asRingR×S = asTypeR×S , (ringstr 0r 1r _+_ _·_ -_ isRingR×S)


_⊗_ : Ring ℓ → Ring ℓ → Ring ℓ
R ⊗ S = asRingR×S R S 