{-# OPTIONS --safe #-}
module Cubical.Data.Sum.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sum.Properties

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
  B : Type ℓ′

instance
  DecEq⊎ : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (A ⊎ B)
  DecEq._≟_ DecEq⊎ = discrete⊎ _≟_ _≟_

instance
  IsOfHLevel⊎ : ⦃ IsOfHLevel (suc (suc n)) A ⦄ → ⦃ IsOfHLevel (suc (suc n)) B ⦄
              → IsOfHLevel (suc (suc n)) (A ⊎ B)
  IsOfHLevel.iohl (IsOfHLevel⊎ ⦃ Al ⦄ ⦃ Bl ⦄) = isOfHLevel⊎ _ (Al .iohl) (Bl .iohl)

instance
  Show⊎ : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A ⊎ B)
  Show.show Show⊎ (inl x) = "inl " ++ show x
  Show.show Show⊎ (inr x) = "inr " ++ show x
