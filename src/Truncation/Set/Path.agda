{-# OPTIONS --safe #-}
module Truncation.Set.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel
open import Meta.Variadic

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁; ∣_∣₁)
open import Truncation.Set.Base public
open import Truncation.Set.Properties

private variable
  ℓ : Level
  A : Type ℓ
  x y : A

∥-∥₂-is-of-hlevel : ∀ n → is-of-hlevel (2 + n) ∥ A ∥₂
∥-∥₂-is-of-hlevel n = is-of-hlevel-+-left 2 n ∥-∥₂-is-set

instance
  decomp-hlevel-∥-∥₂ : goal-decomposition (quote is-of-hlevel) ∥ A ∥₂
  decomp-hlevel-∥-∥₂ = decomp (quote ∥-∥₂-is-of-hlevel ) (`level-minus 2 ∷ [])

@0 ∥-∥₂-path-equiv
  : {x y : A}
  → ∣ x ∣₂ ＝ ∣ y ∣₂
  ≃ ∥ x ＝ y ∥₁
∥-∥₂-path-equiv {x} {y} = prop-extₑ! (encode x ∣ y ∣₂) (decode x (∣ y ∣₂)) where
  code : ∀ x (y : ∥ A ∥₂) → Prop _
  code x = elim! (λ y → el! ∥ x ＝ y ∥₁)

  encode : ∀ x y → ∣ x ∣₂ ＝ y → ⌞ code x y ⌟
  encode x y = J (λ y p → ⌞ code x y ⌟ ) ∣ refl ∣₁

  decode : ∀ x y → ⌞ code x y ⌟ → ∣ x ∣₂ ＝ y
  decode x = elim! (λ _ → ∥-∥₁.rec! (ap ∣_∣₂))

module @0 ∥-∥₂-path {ℓ} {A : Type ℓ} {x} {y} =
  Equiv (∥-∥₂-path-equiv {A = A} {x = x} {y = y})
