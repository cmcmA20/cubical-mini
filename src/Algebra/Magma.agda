
module Algebra.Magma where

open import Foundations.Base
open import Meta.Search.HLevel
open import Meta.Record

private variable
  ℓ : Level
  A : 𝒰 ℓ

record is-magma {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  field
    instance has-is-groupoid : is-of-hlevel 3 A

private
  unquoteDecl eqv = declare-record-iso eqv (quote is-magma)

record Magma-on (A : 𝒰 ℓ) : 𝒰 ℓ where
  field
    _⋆_          : A → A → A
    has-is-magma : is-magma _⋆_

Magma : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
Magma ℓ = Σ[ A ꞉ 𝒰 ℓ ] Magma-on A

instance
  is-magma-is-prop : {_⋆_ : A → A → A} → is-prop (is-magma _⋆_)
  is-magma-is-prop = is-of-hlevel-≃ 1 (iso→equiv eqv) hlevel!