{-# OPTIONS --safe #-}
module Correspondences.Unary.Decidable where

open import Foundations.Base
open import Data.Dec.Base public

open import Structures.Discrete

open import Correspondences.Base public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

Decidable : Pred _ (Pred ℓ′ A)
Decidable {A} P = Π[ a ꞉ A ] Dec (P a)

-- TODO properties about decidable predicates?
