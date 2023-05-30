{-# OPTIONS --safe #-}
module Structures.Finite.ManifestEnumerable.Container where

open import Foundations.Base

open import Data.Nat.Base

open import Functions.Surjection

open import Containers.List.Base

open import Truncation.Propositional.Base

private variable
  ℓ : Level
  A : Type ℓ

ℰ : Type ℓ → Type ℓ
ℰ A = Σ[ support ꞉ ⟦ ListC ⟧ A ] Π[ x ꞉ A ] ∥ x ∈ support ∥₁
