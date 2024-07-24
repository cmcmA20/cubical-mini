{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Vec.Inductive.Base as Vec

private variable @0 n : ℕ

instance
  Map-Vec : Map (eff (λ T → Vec T n))
  Map-Vec .map {A} {B} = go where
    go : (A → B) → Vec A n → Vec B n
    go _ []       = []
    go f (x ∷ xs) = f x ∷ go f xs

  Lawful-Map-Vec : Lawful-Map (eff (λ T → Vec T n))
  Lawful-Map-Vec .Lawful-Map.has-map = Map-Vec
  Lawful-Map-Vec .Lawful-Map.map-pres-id {A} = fun-ext go
    where
    go : (xs : Vec A n) → map refl xs ＝ xs
    go [] = refl
    go (x ∷ xs) = ap (x ∷_) (go xs)
  Lawful-Map-Vec .Lawful-Map.map-pres-comp {A} {f} {g} = fun-ext go
    where
    go : (xs : Vec A n) → map (f ∙ g) xs ＝ (map f ∙ map g) xs
    go [] = refl
    go (x ∷ xs) = ap (g (f x) ∷_) (go xs)
