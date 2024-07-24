{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
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

  Lawful-Map-Tree : Lawful-Map (eff Tree)
  Lawful-Map-Tree .Lawful-Map.has-map = Map-Tree
  Lawful-Map-Tree .Lawful-Map.map-pres-id {A} = fun-ext go
    where
    go : (xs : Tree A) → map refl xs ＝ xs
    go empty = refl
    go (leaf _) = refl
    go (node l r) = ap² node (go l) (go r)
  Lawful-Map-Tree .Lawful-Map.map-pres-comp {A} {f} {g} = fun-ext go
    where
    go : (xs : Tree A) → map (f ∙ g) xs ＝ (map f ∙ map g) xs
    go empty = refl
    go (leaf _) = refl
    go (node l r) = ap² node (go l) (go r)
