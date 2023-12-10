{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.Bind where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Bind

open import Truncation.Propositional.Base
open import Truncation.Propositional.Instances.Idiom public

instance
  Bind-∥-∥₁ : Bind (eff ∥_∥₁)
  Bind-∥-∥₁ ._>>=_ = flip $ rec $ hlevel 1
