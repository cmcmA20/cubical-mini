{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Path where

open import Meta.Prelude

open import Meta.Effect.Map

open import Structures.n-Type

open import Data.Truncation.Propositional.Base as ∥-∥₁
  using (∥_∥₁; ∣_∣₁)
open import Data.Truncation.Propositional.Instances.Map
open import Data.Unit.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  x y : A

ae : A ≃ B → ∥ A ∥₁ ≃ ∥ B ∥₁
ae {A} {B} e = ≅→≃ $ to , iso from ri li where
  to   = map (e    $_)
  from = map (e ⁻¹ $_)

  module e = Equiv e
  ri : from is-right-inverse-of to
  ri = ∥-∥₁.elim hlevel! (ap ∣_∣₁ ∘ e.ε)

  li : from is-left-inverse-of to
  li = ∥-∥₁.elim hlevel! (ap ∣_∣₁ ∘ e.η)
