{-# OPTIONS --safe #-}
module Cubical.Interface.HLevels.TypeFormers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Erased

open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Base

open import Cubical.Interface.HLevels.Base

open IsOfHLevel ⦃ ... ⦄

private variable
  ℓ ℓ′ : Level
  n : ℕ
  A : Type ℓ
  B : A → Type ℓ′

instance
  IsPropIsOfHLevel : IsProp (IsOfHLevel n A)
  IsOfHLevel.iohl IsPropIsOfHLevel _ _ = IsOfHLevel≡ (isPropIsOfHLevel _ _ _)

  IsOfHLevelSuc : ⦃ Al : IsOfHLevel n A ⦄ → IsOfHLevel (suc n) A
  IsOfHLevel.iohl (IsOfHLevelSuc ⦃ Al ⦄) = isOfHLevelSuc _ iohl

  IsOfHLevelΣ : ⦃ Al : IsOfHLevel n A ⦄ ⦃ Bl : {x : A} → IsOfHLevel n (B x) ⦄
              → IsOfHLevel n (Σ A B)
  IsOfHLevel.iohl IsOfHLevelΣ = isOfHLevelΣ _ iohl (λ _ → iohl)

  -- IsOfHLevel× : {B : Type ℓ′}
  --               ⦃ Al : IsOfHLevel n A ⦄ ⦃ Bl : IsOfHLevel n B ⦄
  --             → IsOfHLevel n (A × B)
  -- IsOfHLevel× ⦃ Al ⦄ ⦃ Bl ⦄ = IsOfHLevelΣ {Al = Al} {Bl = λ _ → Bl}

  IsOfHLevelΠ : ⦃ Bl : {x : A} → IsOfHLevel n (B x) ⦄
              → IsOfHLevel n ((x : A) → B x)
  IsOfHLevel.iohl (IsOfHLevelΠ ⦃ Bl ⦄) = isOfHLevelΠ _ (λ _ → Bl .iohl)

  -- IsOfHLevel→ : {B : Type ℓ′}
  --               ⦃ Bl : IsOfHLevel n B ⦄
  --             → IsOfHLevel n (A → B)
  -- IsOfHLevel→ ⦃ Bl = Bl ⦄ = IsOfHLevelΠ ⦃ Bl = λ {_} → Bl ⦄

  IsOfHLevelPath : ⦃ Al : IsOfHLevel (suc n) A ⦄ → {x y : A} → IsOfHLevel n (x ≡ y)
  IsOfHLevel.iohl (IsOfHLevelPath ⦃ Al ⦄) = isOfHLevelPath' _ (Al .iohl) _ _

  IsPropErased : ⦃ Al : IsProp A ⦄ → IsProp (Erased A)
  IsOfHLevel.iohl (IsPropErased ⦃ Al ⦄) _ _ = []-cong [ Al .iohl _ _ ]
