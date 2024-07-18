{-# OPTIONS --safe #-}
module Data.Vec.Ergonomic.Instances.Foldable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Foldable

open import Data.Vec.Ergonomic.Base

instance
  Foldable-Vec : ∀{n} → Foldable (eff λ T → Vec T n)
  Foldable-Vec .fold-r f z = rec z f
