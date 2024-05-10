{-# OPTIONS --safe #-}
module Data.Truncation.Set.Instances.Bind where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Bind
open import Meta.Inductive

open import Data.Truncation.Set.Base
open import Data.Truncation.Set.Instances.Idiom public

instance
  Bind-∥-∥₂ : Bind (eff ∥_∥₂)
  Bind-∥-∥₂ .Bind._>>=_ = flip rec! where
    instance _ = hlevel-basic-instance 2 squash₂
