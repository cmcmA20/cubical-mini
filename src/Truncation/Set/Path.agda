{-# OPTIONS --safe #-}
module Truncation.Set.Path where

open import Meta.Prelude

open import Meta.Effect.Map
open import Meta.Search.HLevel

open import Truncation.Propositional as ∥-∥₁
  using (∥_∥₁; ∣_∣₁)
open import Truncation.Set.Base public
open import Truncation.Set.Instances.Map
open import Truncation.Set.Properties

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  x y : A

∥-∥₂-is-of-hlevel : ∀ n → is-of-hlevel (2 + n) ∥ A ∥₂
∥-∥₂-is-of-hlevel n = is-of-hlevel-+-left 2 n ∥-∥₂-is-set

instance
  decomp-hlevel-∥-∥₂ : goal-decomposition (quote is-of-hlevel) ∥ A ∥₂
  decomp-hlevel-∥-∥₂ = decomp (quote ∥-∥₂-is-of-hlevel ) [ `level-minus 2 ]

@0 ∥-∥₂-path-equiv
  : {x y : A}
  → ∣ x ∣₂ ＝ ∣ y ∣₂
  ≃ ∥ x ＝ y ∥₁
∥-∥₂-path-equiv {x} {y} = prop-extₑ! (encode x ∣ y ∣₂) (decode x (∣ y ∣₂)) where
  code : ∀ x (y : ∥ A ∥₂) → Prop _
  code x = elim! (λ y → el! ∥ x ＝ y ∥₁)

  encode : ∀ x y → ∣ x ∣₂ ＝ y → ⌞ code x y ⌟
  encode x y = Jₜ (λ y p → ⌞ code x y ⌟ ) ∣ refl ∣₁

  decode : ∀ x y → ⌞ code x y ⌟ → ∣ x ∣₂ ＝ y
  decode x = elim! (λ _ → ∥-∥₁.rec! (ap ∣_∣₂))

module @0 ∥-∥₂-path {ℓ} {A : Type ℓ} {x} {y} =
  Equiv (∥-∥₂-path-equiv {A = A} {x = x} {y = y})

∥-∥₂-≃ᴱ : A ≃ B → ∥ A ∥₂ ≃ᴱ ∥ B ∥₂
∥-∥₂-≃ᴱ e = map e.to , is-isoᴱ→is-equivᴱ
  ( map e.from
  , erase (elim! λ x → ∥-∥₂-path.from ∣ e.ε _ ∣₁)
  , erase (elim! λ x → ∥-∥₂-path.from ∣ e.η _ ∣₁))
    where module e = Equiv e
