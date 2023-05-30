{-# OPTIONS --safe #-}
module Structures.Finite.ManifestEnumerable.Base where

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
-- ℰ : Type ℓ → Type ℓ
-- ℰ A = Σ[ support ꞉ List A ] Π[ x ꞉ A ] ∥ x ∈ support ∥₁
