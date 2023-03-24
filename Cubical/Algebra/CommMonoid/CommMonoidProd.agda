{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.CommMonoidProd where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommMonoid.Base

open import Cubical.Instances.HLevels

open CommMonoidStr

private
  variable
    ℓ ℓ' : Level


CommMonoidProd : CommMonoid ℓ → CommMonoid ℓ' → CommMonoid (ℓ-max ℓ ℓ')
CommMonoidProd M N = makeCommMonoid ε× _·×_ ⦃ Is-set× ⦄ assoc× ·IdR× comm×
  where
  ε× : (fst M) × (fst N)
  ε× = (ε (snd M)) , (ε (snd N))

  _·×_ : (fst M) × (fst N) → (fst M) × (fst N) → (fst M) × (fst N)
  (x₁ , x₂) ·× (y₁ , y₂) = (_·_ (snd M) x₁ y₁) , (_·_ (snd N) x₂ y₂)

  Is-set× : IsSet ((fst M) × (fst N))
  IsOfHLevel.iohl Is-set× = isSet× (snd M .is-set .iohl) (snd N .is-set .iohl)

  assoc× : ∀ x y z → x ·× (y ·× z) ≡ (x ·× y) ·× z
  assoc× _ _ _ = cong₂ (_,_) (·Assoc (snd M) _ _ _) (·Assoc (snd N) _ _ _)

  ·IdR× : ∀ x → x ·× ε× ≡ x
  ·IdR× _ =  cong₂ (_,_) (·IdR (snd M) _) (·IdR (snd N) _)

  comm× : ∀ x y → x ·× y ≡ y ·× x
  comm× _ _ = cong₂ (_,_) (·Comm (snd M) _ _) (·Comm (snd N) _ _)
