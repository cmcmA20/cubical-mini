{-# OPTIONS --safe #-}
module Data.HVec.Properties where

open import Foundations.Base
open import Foundations.Equiv

-- yes, it's the right one
open import Data.Vec.Ergonomic.Base

open import Data.HVec.Base

private variable
  ℓ : Level
  n : ℕ

vec-of-types≃types : ∀ n → Vec (Type ℓ) n ≃ Types n (replicate n ℓ)
vec-of-types≃types _ = iso→equiv $ to , iso from ri li where
  to : ∀ {n} → Vec (Type ℓ) n → Types n (replicate n ℓ)
  to {n = 0} _ = _
  to {n = 1} A = A
  to {n = suc (suc n)} (A , As) = A , to As

  from : ∀ {n} → Types n (replicate n ℓ) → Vec (Type ℓ) n
  from {n = 0} _ = _
  from {n = 1} x = x
  from {n = suc (suc n)} (A , As) = A , from As

  ri : ∀ {n} (xs : Types n (replicate n ℓ)) → to (from xs) ＝ xs
  ri {n = 0} _ = refl
  ri {n = 1} _ = refl
  ri {n = suc (suc _)} (_ , xs) = Σ-pathP refl (ri xs)

  li : ∀ {n} (xs : Vec (Type ℓ) n) → from (to xs) ＝ xs
  li {n = 0} _ = refl
  li {n = 1} _ = refl
  li {n = suc (suc _)} (_ , xs) = Σ-pathP refl (li xs)

module vec-of-types≃types {n} {ℓ} = Equiv (vec-of-types≃types {ℓ} n)
