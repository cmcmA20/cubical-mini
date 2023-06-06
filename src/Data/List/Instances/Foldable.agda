{-# OPTIONS --safe #-}
module Data.List.Instances.Foldable where

open import Foundations.Base
open import Meta.Foldable

import Data.List.Base as List
open List public
  using (List)

private variable
  ℓ : Level
  A : Type ℓ

instance
  Foldable-List : Foldable (eff List)
  Foldable-List .Foldable.fold-r = List.fold-r
