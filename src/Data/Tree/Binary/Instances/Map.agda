{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Idiom

open import Data.Tree.Binary.Base as Tree public

private variable
  ℓ : Level
  A : Type ℓ

instance
  Map-Tree : Map (eff Tree)
  Map-Tree .Map.map = Tree.map
