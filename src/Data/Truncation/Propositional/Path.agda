{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Path where

open import Meta.Prelude

open import Data.Bool.Base
open import Data.Reflects.Base
open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Instances.Map
open import Data.Unit.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  x y : A

instance opaque
  H-Level-∥-∥₁ : ∀ {n} → ⦃ n ≥ʰ 1 ⦄ → H-Level n ∥ A ∥₁
  H-Level-∥-∥₁ ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance squash₁
  {-# OVERLAPPING H-Level-∥-∥₁ #-}

instance
  Reflects-∥-∥₁-Path : {a b : ∥ A ∥₁} → Reflects (a ＝ b) true
  Reflects-∥-∥₁-Path = ofʸ prop!
  {-# OVERLAPPING Reflects-∥-∥₁-Path #-}

ae : A ≃ B → ∥ A ∥₁ ≃ ∥ B ∥₁
ae {A} {B} e = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
  to : ∥ A ∥₁ → ∥ B ∥₁
  to   = map (e    $_)
  from = map (e ⁻¹ $_)

  module e = Equiv e
  ri : from section-of′ to
  ri = elim! $ happly $ e.ε ▷ ∣_∣₁

  li : from retract-of′ to
  li = elim! $ happly $ sym $ e.η ▷ ∣_∣₁
