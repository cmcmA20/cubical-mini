{-# OPTIONS --safe #-}
module Data.List.Instances.Map where

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.List.Base

instance
  Map-List : Map (eff List)
  Map-List .map {A} {B} = go where
    go : (A → B) → List A → List B
    go f []       = []
    go f (x ∷ xs) = f x ∷ go f xs
