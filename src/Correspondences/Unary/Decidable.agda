{-# OPTIONS --safe #-}
module Correspondences.Unary.Decidable where

open import Foundations.Base

open import Data.Dec.Base

open import Correspondences.Base public

open import Structures.n-Type

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

Decidable : Pred _ (Pred ℓ′ A)
Decidable {A} P = Π[ a ꞉ A ] Dec (P a)

Decidable₁ : Pred _ (Pred₁ ℓ′ A)
Decidable₁ {A} P = Π[ a ꞉ A ] Dec ⌞ P a ⌟

-- TODO properties about decidable predicates?
