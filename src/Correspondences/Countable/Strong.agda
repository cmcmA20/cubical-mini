{-# OPTIONS --safe #-}
module Correspondences.Countable.Strong where

open import Meta.Prelude

open import Meta.Record
open import Meta.Search.HLevel

open import Correspondences.Discrete

open import Data.Nat.Instances.Discrete

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : A → Type ℓ′
  B : Type ℓ′

record Countable {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  constructor mk-countable
  field enumeration : A ≃ ℕ

open Countable public

unquoteDecl countable-iso =
  declare-record-iso countable-iso (quote Countable)

instance
  H-Level-countable : ∀ {n} → H-Level (2 + n) (Countable A)
  H-Level-countable = hlevel-basic-instance 2 $
    ≅→is-of-hlevel 2 countable-iso hlevel!

countable : ⦃ c : Countable A ⦄ → Countable A
countable ⦃ c ⦄ = c

countable→is-discrete : Countable A → is-discrete A
countable→is-discrete cn = ≃→is-discrete (enumeration cn) ℕ-is-discrete

≃→countable : B ≃ A → Countable A → Countable B
≃→countable e c .enumeration = e ∙ c .enumeration
