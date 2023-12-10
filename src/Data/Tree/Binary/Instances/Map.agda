{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Map

open import Data.Tree.Binary.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  Map-Tree : Map (eff Tree)
  Map-Tree .map {A} {B} = go where
    go : (A → B) → Tree A → Tree B
    go _ empty = empty
    go f (leaf x) = leaf (f x)
    go f (node l r) = node (go f l) (go f r)
