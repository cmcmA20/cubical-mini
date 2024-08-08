{-# OPTIONS --safe #-}
module Data.List.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.List.Base

map-list : ∀ {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
         → (A → B) → List A → List B
map-list f []       = []
map-list f (x ∷ xs) = f x ∷ map-list f xs

map-list-id : ∀ {ℓᵃ} {A : 𝒰 ℓᵃ}
            → (xs : List A) → map-list id xs ＝ xs
map-list-id [] = refl
map-list-id (x ∷ xs) = ap (x ∷_) (map-list-id xs)

map-list-comp : ∀ {ℓᵃ ℓᵇ ℓᶜ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
                  {f : A → B} {g : B → C}
                  (xs : List A)
               → map-list (g ∘ f) xs ＝ map-list g (map-list f xs)
map-list-comp         []       = refl
map-list-comp {f} {g} (x ∷ xs) = ap (g (f x) ∷_) (map-list-comp xs)

instance
  Map-List : Map (eff List)
  Map-List .map = map-list

  Lawful-Map-List : Lawful-Map (eff List)
  Lawful-Map-List .Lawful-Map.has-map = Map-List
  Lawful-Map-List .Lawful-Map.map-pres-id {A} = fun-ext map-list-id
  Lawful-Map-List .Lawful-Map.map-pres-comp = fun-ext map-list-comp
