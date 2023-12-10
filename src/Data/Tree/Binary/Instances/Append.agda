{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Append where

open import Foundations.Base

open import Meta.Append

open import Data.Tree.Binary.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  Append-Tree : Append (Tree A)
  Append-Tree .mempty = empty
  Append-Tree ._<>_   = node
