{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Traversable

open import Data.Vec.Inductive.Base

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  @0 n : ℕ

open Idiom ⦃ ... ⦄
open Traversable ⦃ ... ⦄

vec-traverse : {M : Effect} ⦃ i : Idiom M ⦄
             → let module M = Effect M in
                (A → M.₀ B) → Vec A n → M.₀ (Vec B n)
vec-traverse _ []        = pure []
vec-traverse f (x ∷ xs) = ⦇ f x ∷ vec-traverse f xs ⦈

instance
  Traversable-Vec : Traversable (eff λ T → Vec T n)
  Traversable-Vec .traverse = vec-traverse
