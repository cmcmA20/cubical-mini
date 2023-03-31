{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.Negation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty.Base as ⊥

private variable
  ℓ  : Level
  A  : Type ℓ

infix 3 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

NonEmpty : Type ℓ → Type ℓ
NonEmpty A = ¬ ¬ A

Stable : Type ℓ → Type ℓ
Stable A = NonEmpty A → A

_≢_ : {A : Type ℓ} → A → A → Type ℓ
x ≢ y = ¬ (x ≡ y)
