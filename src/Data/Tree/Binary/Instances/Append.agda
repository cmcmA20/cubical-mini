{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Append where

open import Foundations.Base

open import Data.Tree.Binary.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  Reflᵘ-Tree : Reflᵘ (Tree A)
  Reflᵘ-Tree .mempty = empty

  Transᵘ-Tree : Transᵘ (Tree A)
  Transᵘ-Tree ._<>_ = node
