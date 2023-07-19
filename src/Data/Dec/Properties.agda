{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Idiom
open import Meta.Search.HLevel

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

open import Data.Empty.Base
open import Data.Empty.Instances.HLevel

open import Data.Dec.Base as Dec
open import Data.Dec.Instances.HLevel

private variable
  ℓ : Level
  P : Type ℓ

dec-∥-∥₁-equiv : ∥ Dec P ∥₁ ≃ Dec ∥ P ∥₁
dec-∥-∥₁-equiv = prop-extₑ!
  (∥-∥₁.rec! $ Dec.map pure ∥-∥₁.rec!)
  (Dec.rec (yes <$>_) $ pure ∘ no ∘ _∘ pure)
