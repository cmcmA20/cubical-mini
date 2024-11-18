{-# OPTIONS --safe #-}
module Data.List.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Container
open import Meta.Effect.Map

open import Data.List.Base
open import Data.List.Instances.Container

private variable
  ℓ : Level
  A B : Type ℓ

mapₗ : (A → B) → List A → List B
mapₗ f []       = []
mapₗ f (x ∷ xs) = f x ∷ mapₗ f xs

open Map ⦃ ... ⦄

instance
  Map-List : Map (eff List)
  Map-List .map = mapₗ

  Lawful-Map-List : Lawful-Map (eff List)
  Lawful-Map-List = Lawful-Map-AC λ f → fun-ext $ go f where
    go : ∀{ℓa ℓb} {A : 𝒰 ℓa} {B : 𝒰 ℓb} (f : A → B) (xs : List A) → map f xs ＝ Map-AC-default .map f xs
    go f [] = refl
    go f (x ∷ xs) = ap (f x ∷_) (go f xs)
