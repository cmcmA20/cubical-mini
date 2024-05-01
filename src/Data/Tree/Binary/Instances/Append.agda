{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Append where

open import Foundations.Base

open import Meta.Groupoid

open import Data.Tree.Binary.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  Reflexiveᵘ-Tree : Reflexiveᵘ (Tree A)
  Reflexiveᵘ-Tree .mempty = empty

  Transitiveᵘ-Tree : Transitiveᵘ (Tree A)
  Transitiveᵘ-Tree ._<>_ = node
