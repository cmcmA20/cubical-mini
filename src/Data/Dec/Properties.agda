{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Idiom
open import Meta.Search.HLevel

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

open import Data.Empty.Base
open import Data.Empty.Properties
open import Data.Empty.Instances.HLevel
open import Data.Sum.Properties

open import Data.Dec.Base as Dec
open import Data.Dec.Path
open import Data.Dec.Instances.HLevel

private variable
  ℓ ℓ′ : Level
  A P : Type ℓ
  B : Type ℓ′

dec-∥-∥₁-equiv : ∥ Dec P ∥₁ ≃ Dec ∥ P ∥₁
dec-∥-∥₁-equiv = prop-extₑ!
  (∥-∥₁.rec! $ Dec.map pure ∥-∥₁.rec!)
  (Dec.rec (yes <$>_) $ pure ∘ no ∘ _∘ pure)

Dec-≃ : A ≃ B → Dec A ≃ Dec B
Dec-≃ eqv = dec-as-sum ∙ₑ ⊎-ap-r eqv ∙ₑ ⊎-ap-l (¬-≃ (eqv .fst) ((eqv ₑ⁻¹) .fst)) ∙ₑ (dec-as-sum ₑ⁻¹)
