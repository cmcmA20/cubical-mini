{-# OPTIONS --safe #-}
module Correspondences.Nullary.Connected where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.Base

open import Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ

opaque
  -- weak form of contractibility
  is-connected : Type ℓ → Type ℓ
  is-connected A = ∥ A ∥₁ × (∥_∥₁ on-paths-of A)

  is-connected-is-prop : is-prop (is-connected A)
  is-connected-is-prop = is-prop-η λ _ _ → prop!

Connected-component : {A : Type ℓ} (c : A) → Type ℓ
Connected-component {A} c = Σ[ a ꞉ A ] ∥ c ＝ a ∥₁
