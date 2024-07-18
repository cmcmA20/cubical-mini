{-# OPTIONS --safe #-}
module Data.List.Instances.Foldable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Foldable

open import Data.List.Base as List

instance
  Foldable-List : Foldable (eff List)
  Foldable-List .fold-r = flip rec
