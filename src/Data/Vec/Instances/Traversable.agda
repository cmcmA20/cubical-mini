{-# OPTIONS --safe #-}
module Data.Vec.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Traversable

open import Data.Vec.Base

open Idiom ⦃ ... ⦄
open Traversable ⦃ ... ⦄

private variable ℓᵃ ℓᵇ ℓᶜ : Level

vec-traverse : {A : Type ℓᵃ} {B : Type ℓᵇ} {M : Effect} ⦃ i : Idiom M ⦄ {n : ℕ}
              → let module M = Effect M in
                (A → M.₀ B) → Vec A n → M.₀ (Vec B n)
vec-traverse {n = 0}     _ _        = pure (lift tt)
vec-traverse {n = suc n} f (x , xs) = ⦇ f x , vec-traverse f xs ⦈

instance
  Traversable-Vec : ∀{n} → Traversable (eff λ T → Vec T n)
  Traversable-Vec .traverse = vec-traverse
