{-# OPTIONS --safe #-}
module Structures.Separated where

open import Foundations.Base

open import Data.Empty

open import Meta.Reflection.HLevel

open import Structures.Base
open import Structures.IdentitySystem.Base

open import Structures.Negation

private variable
  ℓ : Level
  A : Type ℓ

infix 0 ¬¬_
¬¬_ : Type ℓ → Type ℓ
¬¬ A = ¬ ¬ A

Separated : Type ℓ → Type ℓ
Separated A = (¬¬_ stable_) on-paths-of A

separated-identity-system
  : Separated A
  → is-identity-system (λ x y → ¬¬ (x ＝ y)) (λ _ k → k refl)
separated-identity-system A-sep =
  set-identity-system (λ _ _ → hlevel!) (A-sep _ _)
