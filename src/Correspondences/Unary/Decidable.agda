{-# OPTIONS --safe #-}
module Correspondences.Unary.Decidable where

open import Foundations.Base
open import Data.Dec.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

Decidable : (A → Type ℓ′) → Type _
Decidable {A} P = Π[ a ꞉ A ] Dec (P a)
