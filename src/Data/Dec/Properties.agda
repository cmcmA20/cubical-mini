{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Idiom
open import Meta.Search.HLevel

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

open import Data.Empty.Properties
open import Data.Sum.Properties

open import Data.Dec.Base as Dec
open import Data.Dec.Path

private variable
  ℓ ℓ′ : Level
  A P : Type ℓ
  B : Type ℓ′

dec-∥-∥₁-equiv : ∥ Dec P ∥₁ ≃ Dec ∥ P ∥₁
dec-∥-∥₁-equiv = prop-extₑ!
  (∥-∥₁.rec! $ Dec.map pure ∥-∥₁.rec!)
  (Dec.rec (yes <$>_) $ pure ∘ no ∘ _∘ pure)

dec-≃ : A ≃ B → Dec A ≃ Dec B
dec-≃ eqv = dec-as-sum ∙ₑ ⊎-ap (¬-≃ to from) eqv ∙ₑ (dec-as-sum ₑ⁻¹)
  where open Equiv eqv
