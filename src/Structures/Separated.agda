{-# OPTIONS --safe #-}
module Structures.Separated where

open import Foundations.Base

open import Data.Empty
import Data.Empty as ⊥

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

is-separated : Type ℓ → Type ℓ
is-separated A = (¬¬_ stable_) on-paths-of A

separated-identity-system
  : is-separated A
  → is-identity-system (λ x y → ¬¬ (x ＝ y)) (λ _ k → k refl)
separated-identity-system A-sep =
  set-identity-system (λ _ _ → hlevel!) (A-sep _ _)

is-separated→is-set
  : is-separated A
  → is-set A
is-separated→is-set As =
  identity-system→hlevel 1
    (separated-identity-system As) λ _ _ _ f →
      fun-ext λ g → absurd (f g)

is-separated-is-prop : is-prop (is-separated A)
is-separated-is-prop As As′ =
  fun-ext λ x i y p j → (is-separated→is-set As) x y (As _ _ p) (As′ _ _ p) i j
