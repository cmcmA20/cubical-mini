{-# OPTIONS --safe #-}
module Data.List.Instances.Discrete where

open import Foundations.Base
open import Meta.Discrete
open import Meta.Reflection.HLevel

import Data.Dec.Base as Dec
open import Data.List.Path

instance
  Discrete-List : {ℓ : Level} {A : Type ℓ} → ⦃ Discrete A ⦄ → Discrete (List A)
  Discrete-List {A} .Discrete._≟_ = go
    where
      go : is-discrete (List A)
      go []       []       = yes refl
      go []       (y ∷ ys) = no λ p → ∷≠[] (sym p)
      go (x ∷ xs) []       = no ∷≠[]
      go (x ∷ xs) (y ∷ ys) with x ≟ y
      ... | no  x≠y = no λ p → x≠y (∷-head-inj p)
      ... | yes x＝y with go xs ys
      ... | no  xs≠ys  = no λ p → xs≠ys (ap tail p)
      ... | yes xs＝ys = yes (ap₂ _∷_ x＝y xs＝ys)
