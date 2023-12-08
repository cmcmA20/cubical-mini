{-# OPTIONS --safe #-}
module Data.List.Instances.Foldable where

open import Foundations.Base

open import Meta.Effect.Foldable

open import Data.List.Base as List

instance
  Foldable-List : Foldable (eff List)
  Foldable-List .Foldable.fold-r = rec
