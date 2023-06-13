{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.Bind where

open import Foundations.Base

open import Meta.Bind

open import Truncation.Propositional.Base
open import Truncation.Propositional.Instances.Idiom public

instance
  Bind-∥-∥₁ : Bind (eff ∥_∥₁)
  Bind-∥-∥₁ .Bind._>>=_ ∣a∣₁ mf = rec squash₁ mf ∣a∣₁
