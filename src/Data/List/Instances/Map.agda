{-# OPTIONS --safe #-}
module Data.List.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.List.Base

instance
  Map-List : Map (eff List)
  Map-List .map {A} {B} = go where
    go : (A → B) → List A → List B
    go f []       = []
    go f (x ∷ xs) = f x ∷ go f xs

  Lawful-Map-List : Lawful-Map (eff List)
  Lawful-Map-List .Lawful-Map.has-map = Map-List
  Lawful-Map-List .Lawful-Map.map-pres-id {A} = fun-ext go
    where
    go : (xs : List A) → map refl xs ＝ xs
    go [] = refl
    go (x ∷ xs) = ap (x ∷_) (go xs)
  Lawful-Map-List .Lawful-Map.map-pres-comp {A} {f} {g} = fun-ext go
    where
    go : (xs : List A) → map (f ∙ g) xs ＝ (map f ∙ map g) xs
    go [] = refl
    go (x ∷ xs) = ap (g (f x) ∷_) (go xs)
