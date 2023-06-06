{-# OPTIONS --safe #-}
module Correspondences.Unary.Decidable where

open import Foundations.Base
open import Data.Dec.Base public
  using (¬_; Dec; yes; no)

open import Correspondences.Base public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : Pred ℓ′ A

Decidable : Pred _ (Pred ℓ′ A)
Decidable {A} P = Π[ a ꞉ A ] Dec (P a)

-- TODO properties about decidable predicates?
