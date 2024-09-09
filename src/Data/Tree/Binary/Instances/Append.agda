{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Append where

open import Foundations.Base

open import Data.Tree.Binary.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  Pointed-Tree : Pointed (Tree A)
  Pointed-Tree .mempty = empty

  Has-binary-op-Tree : Has-binary-op (Tree A)
  Has-binary-op-Tree ._<>_ = node
