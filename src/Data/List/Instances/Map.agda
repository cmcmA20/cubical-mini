{-# OPTIONS --safe #-}
module Data.List.Instances.Map where

open import Meta.Effect.Map

open import Data.List.Base as List

instance
  Map-List : Map (eff List)
  Map-List .Map.map {A} {B} = go where
    go : (A → B) → List A → List B
    go f []       = []
    go f (x ∷ xs) = f x ∷ go f xs
