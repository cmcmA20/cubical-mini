{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Traversable

open import Data.Tree.Binary.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  Traversable-Tree : Traversable (eff Tree)
  Traversable-Tree .traverse {M} {A} {B} = go where
    private module M = Effect M
    go : (A → M.₀ B) → Tree A → M.₀ (Tree B)
    go f empty      = pure empty
    go f (leaf x)   = ⦇ leaf (f x) ⦈
    go f (node l r) = ⦇ node (go f l) (go f r) ⦈
