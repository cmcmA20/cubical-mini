{-# OPTIONS --safe #-}
module Cubical.Data.Sigma.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

open DecEq ⦃ ... ⦄
open IsOfHLevel ⦃ ... ⦄
open Show ⦃ ... ⦄

private variable
  ℓ ℓ′ : Level
  n : HLevel
  A : Type ℓ
  B : A → Type ℓ′

instance
  DecEqΣ : ⦃ DecEq A ⦄ → ⦃ {x : A} → DecEq (B x) ⦄ → DecEq (Σ A B)
  DecEq._≟_ DecEqΣ = discreteΣ _≟_ λ _ → _≟_

instance
  IsOfHLevelΣ : ⦃ Al : IsOfHLevel n A ⦄ ⦃ Bl : {x : A} → IsOfHLevel n (B x) ⦄
              → IsOfHLevel n (Σ A B)
  IsOfHLevel.iohl IsOfHLevelΣ = isOfHLevelΣ _ iohl (λ _ → iohl)

instance
  ShowΣ : ⦃ Show A ⦄ → ⦃ {x : A} → Show (B x) ⦄ → Show (Σ A B)
  Show.show ShowΣ (a , b) = show a ++ (" , " ++ show b)
