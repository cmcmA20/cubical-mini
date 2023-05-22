{-# OPTIONS --safe #-}
module Structures.Discrete where

open import Foundations.Base

open import Data.Dec.Base
open import Data.Dec.Path
open import Data.Empty.Base

open import Structures.Base
open import Structures.IdentitySystem.Base
open import Structures.Separated

open import Meta.HLevel
open import Meta.Reflection.HLevel

private variable
  ℓ : Level
  A : Type ℓ

is-discrete : Type ℓ → Type ℓ
is-discrete A = Dec on-paths-of A

dec→¬¬-stable : Dec A → ¬¬_ stable A
dec→¬¬-stable (no ¬a) f = absurd (f ¬a)
dec→¬¬-stable (yes a) _ = a

is-discrete→separated : is-discrete A → Separated A
is-discrete→separated dec x y f = dec→¬¬-stable (dec x y) f

-- Hedberg
is-discrete→is-set : is-discrete A → is-set A
is-discrete→is-set dec =
  identity-system→hlevel 1
    (separated-identity-system (is-discrete→separated dec)) λ _ _ _ f →
      fun-ext λ g → absurd (f g)

abstract
  is-discrete-is-prop : is-prop (is-discrete A)
  is-discrete-is-prop d₁ _ = fun-ext λ x  → fun-ext λ y →
    Dec-is-of-hlevel 1 (is-discrete→is-set d₁ x y) _ _
