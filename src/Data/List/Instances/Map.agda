{-# OPTIONS --safe #-}
module Data.List.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.List.Base

private variable
  ℓ : Level
  A B : Type ℓ

mapₗ : (A → B) → List A → List B
mapₗ f []       = []
mapₗ f (x ∷ xs) = f x ∷ mapₗ f xs

open Map ⦃ ... ⦄
open Lawful-Map ⦃ ... ⦄

instance
  Map-List : Map (eff List)
  Map-List .map = mapₗ

  Lawful-Map-List : Lawful-Map (eff List)
  Lawful-Map-List .map-pres-id {A} = fun-ext go where opaque
    go : (xs : List A) → map refl xs ＝ xs
    go [] = refl
    go (x ∷ xs) = ap (_ ∷_) (go xs)
  Lawful-Map-List .map-pres-comp {A} {f} {g} = fun-ext go where opaque
    go : (xs : List A) → map (f ∙ g) xs ＝ (map f ∙ map g) xs
    go [] = refl
    go (x ∷ xs) = ap (_ ∷_) (go xs)
