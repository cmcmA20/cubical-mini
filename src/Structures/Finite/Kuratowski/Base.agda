{-# OPTIONS --safe #-}
module Structures.Finite.Kuratowski.Base where

open import Foundations.Base
open import Foundations.Equiv.Base

open import Data.Nat.Base
open import Data.Fin.Sum
open import Data.List.Base

open import Functions.Surjection

open import Truncation.Propositional.Base

private variable
  ℓ : Level
  A : Type ℓ

-- TODO List ∈
-- 𝒦 : Type ℓ → Type ℓ
-- 𝒦 A = Σ[ support ꞉ List A ] Π[ x ꞉ A ] ∥ x ∈ support ∥₁
