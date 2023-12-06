{-# OPTIONS --safe #-}
module Data.Vec.Instances.Finite where

open import Foundations.Base

open import Meta.Search.Finite.Bishop

open import Data.Nat.Base
open import Data.Unit.Instances.Finite

open import Data.Vec.Base public

private variable
  ℓ ℓ′ : Level
  n : ℕ
  A : Type ℓ
  B : Type ℓ′

vec-is-bishop-finite : is-bishop-finite A → is-bishop-finite (Vec A n)
vec-is-bishop-finite {A} {0} _ = lift-is-bishop-finite ⊤-is-bishop-finite
vec-is-bishop-finite {A} {suc _} A-fin =
  ×-is-bishop-finite A-fin (vec-is-bishop-finite A-fin)

instance
  decomp-fin-vec : goal-decomposition (quote is-bishop-finite) (Vec A n)
  decomp-fin-vec = decomp (quote vec-is-bishop-finite) [ `search (quote is-bishop-finite) ]
