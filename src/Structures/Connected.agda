{-# OPTIONS --safe #-}
module Structures.Connected where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Reflection.HLevel

open import Truncation.Propositional

open import Structures.Base

private variable
  ℓ : Level
  A : Type ℓ

-- weak form of contractibility
is-connected : Type ℓ → Type ℓ
is-connected A = ∥ A ∥₁ × (∥_∥₁ on-paths-of A)

is-connected-is-prop : is-prop (is-connected A)
is-connected-is-prop _ _ = prop!

Connected-component : {A : Type ℓ} (c : A) → Type ℓ
Connected-component {A} c = Σ[ a ꞉ A ] ∥ c ＝ a ∥₁
