{-# OPTIONS --safe #-}
module Data.List.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.HLevel

open import Correspondences.Nullary.Decidable

import Data.Dec.Base as Dec
open Dec
open import Data.List.Path

instance
  list-is-discrete : {ℓ : Level} {A : Type ℓ} → ⦃ is-discrete A ⦄ → is-discrete (List A)
  list-is-discrete {A} = is-discrete-η go
    where
      go : (xs ys : List A) → Dec (xs ＝ ys)
      go []       []       = yes refl
      go []       (y ∷ ys) = no λ p → ∷≠[] (sym p)
      go (x ∷ xs) []       = no ∷≠[]
      go (x ∷ xs) (y ∷ ys) with x ≟ y
      ... | no  x≠y = no λ p → x≠y (∷-head-inj p)
      ... | yes x＝y with go xs ys
      ... | no  xs≠ys  = no λ p → xs≠ys (ap tail p)
      ... | yes xs＝ys = yes (ap₂ _∷_ x＝y xs＝ys)
