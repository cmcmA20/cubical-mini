{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Map

open import Data.Vec.Inductive.Base as Vec

private variable @0 n : ℕ

instance
  Map-Vec : Map (eff (λ T → Vec T n))
  Map-Vec .map {A} {B} = go where
    go : (A → B) → Vec A n → Vec B n
    go _ []       = []
    go f (x ∷ xs) = f x ∷ go f xs
