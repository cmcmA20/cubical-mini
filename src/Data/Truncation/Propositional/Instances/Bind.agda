{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Instances.Bind where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Base
open import Meta.Effect.Bind
open import Meta.Inductive

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Instances.Idiom public

instance
  Bind-∥-∥₁ : Bind (eff ∥_∥₁)
  Bind-∥-∥₁ ._>>=_ = flip rec! where
    instance _ = hlevel-prop-instance squash₁
