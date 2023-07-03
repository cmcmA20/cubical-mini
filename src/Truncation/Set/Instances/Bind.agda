{-# OPTIONS --safe #-}
module Truncation.Set.Instances.Bind where

open import Foundations.Base

open import Meta.Bind

open import Truncation.Set.Base
open import Truncation.Set.Instances.Idiom public

instance
  Bind-∥-∥₂ : Bind (eff ∥_∥₂)
  Bind-∥-∥₂ .Bind._>>=_ ∣a∣₂ mf = rec ∥-∥₂-is-set mf ∣a∣₂
