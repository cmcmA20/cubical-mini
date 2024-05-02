{-# OPTIONS --safe #-}
module Homotopy.Connectedness where

open import Meta.Prelude

open import Meta.Deriving.HLevel

open import Data.Truncation.Propositional.Base

private variable
  ℓ : Level
  A : Type ℓ

record is-connected {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    centre₁ : ∥ A ∥₁
    paths₁  : ∥_∥₁ on-paths-of A

unquoteDecl H-Level-is-connected =
  declare-record-hlevel 1 H-Level-is-connected (quote is-connected)

Connected-component : (c : A) → Type (level-of-type A)
Connected-component {A} c = Σ[ a ꞉ A ] ∥ c ＝ a ∥₁
