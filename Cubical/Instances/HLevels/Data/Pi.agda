{-# OPTIONS --safe #-}
module Cubical.Instances.HLevels.Data.Pi where

open import Cubical.Foundations.Prelude

open import Cubical.Instances.HLevels.Base

private variable
  ℓ ℓ′ : Level
  h : HLevel
  A : Type ℓ
  B : A → Type ℓ′

instance
  IsOfHLevelΠ : ⦃ {a : A} → IsOfHLevel h (B a) ⦄
              → IsOfHLevel h ((x : A) → B x)
  IsOfHLevel.iohl IsOfHLevelΠ = isOfHLevelΠ _ (λ _ → iohl)
