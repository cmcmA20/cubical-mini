{-# OPTIONS --safe #-}
module Correspondences.Countable.Base where

open import Meta.Prelude

open import Meta.Deriving.HLevel
open import Meta.Effect.Bind
open import Meta.Record

open import Correspondences.Discrete

open import Data.Nat.Instances.Discrete

open import Data.Truncation.Propositional as ∥-∥₁

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

unquoteDecl H-Level-is-countable =
  declare-record-hlevel 1 H-Level-is-countable (quote is-countable)

is-countable→is-discrete : is-countable A → is-discrete A
is-countable→is-discrete {A} cn = ∥-∥₁.proj! go where
  go : ∥ is-discrete A ∥₁
  go = do
    e ← enumeration₁ cn
    pure $ λ {x} {y} → ≃→is-discrete e ℕ-is-discrete

≃→is-countable : B ≃ A → is-countable A → is-countable B
≃→is-countable e c .enumeration₁ = do
  x ← c .enumeration₁
  pure (e ∙ x)

-- TODO generalize to sigma?
-- TODO Cantor's pairing function
-- ×-is-countable
--   : is-countable A → is-countable B
--   → is-countable (A × B)
-- ×-is-countable ca cb .enumeration₁ = do
--   ea ← enumeration₁ ca
--   eb ← enumeration₁ cb
--   pure $ ×-ap ea eb ∙ₑ ℕ×ℕ≃ℕ
