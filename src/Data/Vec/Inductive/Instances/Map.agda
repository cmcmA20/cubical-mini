{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Vec.Inductive.Base as Vec

private variable
  @0 n : ℕ
  ℓ : Level
  A B : Type ℓ

mapᵥ : (A → B) → Vec A n → Vec B n
mapᵥ f []       = []
mapᵥ f (x ∷ xs) = f x ∷ mapᵥ f xs

instance
  Map-Vec : Map (eff (λ T → Vec T n))
  Map-Vec .map = mapᵥ

  Lawful-Map-Vec : Lawful-Map (eff (λ T → Vec T n))
  Lawful-Map-Vec .map-pres-id {A} = fun-ext go where opaque
    go : (xs : Vec A n) → map refl xs ＝ xs
    go [] = refl
    go (x ∷ xs) = ap (x ∷_) (go xs)
  Lawful-Map-Vec .map-pres-comp {A} {f} {g} = fun-ext go where opaque
    go : (xs : Vec A n) → map (f ∙ g) xs ＝ (map f ∙ map g) xs
    go [] = refl
    go (x ∷ xs) = ap (g (f x) ∷_) (go xs)
