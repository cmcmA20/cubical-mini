{-# OPTIONS --safe #-}
module Correspondences.Connected where

open import Meta.Prelude

open import Data.Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ

opaque
  -- weak form of contractibility
  is-connected : Type ℓ → Type ℓ
  is-connected A = ∥ A ∥₁ × (∥_∥₁ on-paths-of A)

  centre₁ : is-connected A → ∥ A ∥₁
  centre₁ = fst

  paths₁ : is-connected A → ∥_∥₁ on-paths-of A
  paths₁ = snd

  is-connected-β : is-connected A → ∥ A ∥₁ × (∥_∥₁ on-paths-of A)
  is-connected-β = id

  is-connected-η : ∥ A ∥₁ × (∥_∥₁ on-paths-of A) → is-connected A
  is-connected-η = id

  is-connected-is-prop : is-prop (is-connected A)
  is-connected-is-prop  _ _ = prop!

instance opaque
  H-Level-conn : ∀ {n} → H-Level (suc n) (is-connected A)
  H-Level-conn = hlevel-prop-instance is-connected-is-prop

Connected-component : (c : A) → Type (level-of-type A)
Connected-component {A} c = Σ[ a ꞉ A ] ∥ c ＝ a ∥₁
