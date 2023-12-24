{-# OPTIONS --safe #-}
module Correspondences.Countable.Base where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Effect.Bind
open import Meta.Record
open import Meta.Search.HLevel

open import Correspondences.Discrete

open import Data.Nat.Instances.Discrete

open import Truncation.Propositional as ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : A → Type ℓ′
  B : Type ℓ′

record is-countable {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  constructor mk-is-countable
  field enumeration₁ : ∥ A ≃ ℕ ∥₁

open is-countable public

unquoteDecl is-countable-iso =
  declare-record-iso is-countable-iso (quote is-countable)

instance
  H-Level-is-countable : ∀ {n} → H-Level (suc n) (is-countable A)
  H-Level-is-countable = hlevel-prop-instance $
    iso→is-of-hlevel 1 is-countable-iso hlevel!

countable₁ : ⦃ c : is-countable A ⦄ → is-countable A
countable₁ ⦃ c ⦄ = c

is-countable→is-discrete : is-countable A → is-discrete A
is-countable→is-discrete cn = ∥-∥₁.proj! do
  e ← enumeration₁ cn
  pure $ is-discrete-≃ e ℕ-is-discrete

-- TODO generalize to sigma?
-- TODO Cantor's pairing function
-- ×-is-countable
--   : is-countable A → is-countable B
--   → is-countable (A × B)
-- ×-is-countable ca cb .enumeration₁ = do
--   ea ← enumeration₁ ca
--   eb ← enumeration₁ cb
--   pure $ ×-ap ea eb ∙ₑ ℕ×ℕ≃ℕ
