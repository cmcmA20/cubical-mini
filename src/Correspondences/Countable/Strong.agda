{-# OPTIONS --safe #-}
module Correspondences.Countable.Strong where

open import Meta.Prelude

open import Meta.Deriving.HLevel

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

instance
  unquoteDecl H-Level-countable =
    declare-record-hlevel 2 H-Level-countable (quote Countable)

countable→is-discrete : Countable A → is-discrete A
countable→is-discrete cn = ≃→is-discrete (enumeration cn) ℕ-is-discrete

≃→countable : B ≃ A → Countable A → Countable B
≃→countable e c .enumeration = e ∙ c .enumeration
