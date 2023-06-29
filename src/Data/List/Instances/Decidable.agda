{-# OPTIONS --safe #-}
module Data.List.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

import Data.Dec.Base as Dec
open Dec
open import Data.List.Path

private variable
  ℓ : Level
  A : Type ℓ

opaque
  unfolding is-decidable-at-hlevel
  list-is-discrete : is-discrete A → is-discrete (List A)
  list-is-discrete _ [] []      = yes refl
  list-is-discrete _ [] (_ ∷ _) = no $ ∷≠[] ∘ sym
  list-is-discrete _ (_ ∷ _) [] = no ∷≠[]
  list-is-discrete di (x ∷ xs) (y ∷ ys) with di x y
  ... | no  x≠y = no $ x≠y ∘ ∷-head-inj
  ... | yes x=y with list-is-discrete di xs ys
  ... | no  xs≠ys = no $ xs≠ys ∘ ap tail
  ... | yes xs=ys = yes (ap₂ _∷_ x=y xs=ys)

instance
  decomp-dec₁-list : goal-decomposition (quote is-decidable-at-hlevel) (List A)
  decomp-dec₁-list = decomp (quote list-is-discrete) (`search (quote is-decidable-at-hlevel) ∷ [])
