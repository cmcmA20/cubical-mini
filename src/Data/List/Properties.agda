{-# OPTIONS --safe #-}
module Data.List.Properties where

open import Foundations.Base

open import Meta.Effect.Map

open import Data.List.Base public
open import Data.List.Instances.Map

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ

open Map ⦃ ... ⦄

map-++ : {A : Type ℓᵃ} {B : Type ℓᵇ} (f : A → B) (xs ys : List A)
       → map f (xs ++ ys) ＝ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = ap (f x ∷_) (map-++ f xs ys)

++-id-l : (xs : List A) → [] ++ xs ＝ xs
++-id-l _ = refl

++-id-r : (xs : List A) → xs ++ [] ＝ xs
++-id-r []       = refl
++-id-r (x ∷ xs) = ap (x ∷_) (++-id-r xs)

++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ＝ xs ++ ys ++ zs
++-assoc []       _  _  = refl
++-assoc (x ∷ xs) ys zs = ap (x ∷_) (++-assoc xs ys zs)
