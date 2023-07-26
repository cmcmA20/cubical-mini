{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Map where

open import Foundations.Base

open import Meta.Idiom

open import Data.Tree.Binary.Base public

private variable
  ℓ : Level
  A : Type ℓ

instance
  Map-Tree : Map (eff Tree)
  Map-Tree ._<$>_ = map
