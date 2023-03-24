{-# OPTIONS --safe #-}
module Cubical.Instances.HLevels.Data.Sigma where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.Base

open import Cubical.Instances.HLevels.Base

private variable
  ℓ ℓ′ : Level
  h : HLevel
  A : Type ℓ
  B : A → Type ℓ′

instance
  IsOfHLevelΣ : ⦃ IsOfHLevel h A ⦄ → ⦃ {a : A} → IsOfHLevel h (B a) ⦄
              → IsOfHLevel h (Σ A B)
  IsOfHLevel.iohl IsOfHLevelΣ = isOfHLevelΣ _ iohl (λ _ → iohl)
