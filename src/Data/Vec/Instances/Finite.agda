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

vec-is-fin-set : is-fin-set A → is-fin-set (Vec A n)
vec-is-fin-set {A} {0} _ = lift-is-fin-set ⊤-is-fin-set
vec-is-fin-set {A} {1} A-fin = A-fin
vec-is-fin-set {A} {suc (suc _)} A-fin =
  ×-is-fin-set A-fin (vec-is-fin-set A-fin)

instance
  decomp-fin-vec : goal-decomposition (quote is-fin-set) (Vec A n)
  decomp-fin-vec = decomp (quote vec-is-fin-set) [ `search (quote is-fin-set) ]
