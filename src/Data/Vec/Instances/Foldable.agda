{-# OPTIONS --safe #-}
module Data.Vec.Instances.Foldable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Foldable

open import Data.Vec.Base

instance
  Foldable-Vec : ∀{n} → Foldable (eff λ T → Vec T n)
  Foldable-Vec .fold-r f z = rec z f
