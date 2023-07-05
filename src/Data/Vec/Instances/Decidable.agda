{-# OPTIONS --safe #-}
module Data.Vec.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Correspondences.Decidable

open import Data.Dec.Base
open import Data.List.Base using ([]) renaming (_∷_ to _∷ₗ_)
open import Data.Vec.Base

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

opaque
  unfolding is-decidable-at-hlevel
  vec-is-discrete : is-discrete A → is-discrete (Vec A n)
  vec-is-discrete _ [] [] = yes refl
  vec-is-discrete di (x ∷ xs) (y ∷ ys) with di x y
  ... | no  x≠y = no $ x≠y ∘ ap head
  ... | yes x=y with vec-is-discrete di xs ys
  ... | no  xs≠ys = no $ xs≠ys ∘ ap tail
  ... | yes xs=ys = yes (ap₂ _∷_ x=y xs=ys)

instance
  decomp-dec₁-vec : goal-decomposition (quote is-decidable-at-hlevel) (Vec A n)
  decomp-dec₁-vec = decomp (quote vec-is-discrete) (`search (quote is-decidable-at-hlevel) ∷ₗ [])
