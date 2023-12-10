{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Foldable where

open import Foundations.Base

open import Meta.Effect.Foldable

open import Data.Maybe.Base

instance
  Foldable-Maybe : Foldable (eff Maybe)
  Foldable-Maybe .fold-r f b (just x) = f x b
  Foldable-Maybe .fold-r _ b nothing  = b
