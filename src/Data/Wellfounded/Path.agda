{-# OPTIONS --safe #-}
module Data.Wellfounded.Path where

open import Meta.Prelude
open import Data.Wellfounded.Base

private variable ℓ ℓ′ : Level

opaque
  acc-is-prop
    : {A : Type ℓ} {_<_ : A → A → 𝒰 ℓ′}
    → ∀ x → is-prop (Acc _<_ x)
  acc-is-prop x (acc s) (acc t) = ap acc $
    fun-ext λ y → fun-ext λ y<x → acc-is-prop y (s y y<x) (t y y<x)

instance opaque
  H-Level-Acc
    : {A : Type ℓ} {_<_ : A → A → 𝒰 ℓ′}
    → ∀ {x} {n} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (Acc _<_ x)
  H-Level-Acc ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (acc-is-prop _)
  {-# OVERLAPPING H-Level-Acc #-}
