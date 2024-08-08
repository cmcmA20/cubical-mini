{-# OPTIONS --safe #-}
module Data.Reflects.Properties where

open import Meta.Prelude

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Empty.Properties

open import Data.Reflects.Base
open import Data.Reflects.Path

private variable
  ℓ ℓ′ : Level
  a b : Bool
  P : Type ℓ
  Q : Type ℓ′

¬-reflects : Reflects⁰ P b → Reflects⁰ (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

reflects-bool-inj : Reflects⁰ P a → Reflects⁰ P b → a ＝ b
reflects-bool-inj (ofʸ  p) (ofʸ  p′) = refl
reflects-bool-inj (ofʸ  p) (ofⁿ ¬p′) = ⊥.rec $ ¬p′ p
reflects-bool-inj (ofⁿ ¬p) (ofʸ  p′) = ⊥.rec $ ¬p p′
reflects-bool-inj (ofⁿ ¬p) (ofⁿ ¬p′) = refl

≃→reflects : P ≃ Q → Reflects⁰ P b → Reflects⁰ Q b
≃→reflects e = dmap (e $_) (_∘ (e ⁻¹ $_))

≃-reflects-≃ : is-prop P → P ≃ Q → Reflects⁰ P b ≃ Reflects⁰ Q b
≃-reflects-≃ P-prop e =
  prop-extₑ (reflects-is-of-hlevel 0 P-prop)
            (reflects-is-of-hlevel 0 (≃→is-of-hlevel 1 (e ⁻¹) P-prop))
            (≃→reflects e) (≃→reflects (e ⁻¹))

reflects-injₑ
  : is-prop P → is-prop Q
  → Reflects⁰ P a → Reflects⁰ Q a → P ≃ Q
reflects-injₑ P-prop Q-prop (ofʸ p)  (ofʸ q)  = prop-extₑ P-prop Q-prop (λ _ → q) (λ _ → p)
reflects-injₑ _      _      (ofⁿ ¬p) (ofⁿ ¬q) = ¬-extₑ ¬p ¬q

-- Automation

reflects-injₑ!
  : ⦃ P-prop : H-Level 1 P ⦄
    ⦃ Q-prop : H-Level 1 Q ⦄
  → Reflects⁰ P a → Reflects⁰ Q a → P ≃ Q
reflects-injₑ! = reflects-injₑ (hlevel 1) (hlevel 1)
