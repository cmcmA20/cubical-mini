{-# OPTIONS --safe #-}
module Data.Reflects.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Empty.Properties

open import Data.Reflects.Base

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
reflects-bool-inj (ofʸ  p) (ofⁿ ¬p′) = ⊥.rec $ᴱ ¬p′ p
reflects-bool-inj (ofⁿ ¬p) (ofʸ  p′) = ⊥.rec $ᴱ ¬p p′
reflects-bool-inj (ofⁿ ¬p) (ofⁿ ¬p′) = refl

reflects-injₑ
  : is-prop P → is-prop Q
  → Reflects⁰ P a → Reflects⁰ Q a → P ≃ Q
reflects-injₑ P-prop Q-prop (ofʸ p)  (ofʸ q)  = prop-extₑ P-prop Q-prop (λ _ → q) (λ _ → p)
reflects-injₑ _      _      (ofⁿ ¬p) (ofⁿ ¬q) = ¬-extₑ ¬p ¬q

reflects-injₑ!
  : {@(tactic hlevel-tactic-worker) P-prop : is-prop P}
    {@(tactic hlevel-tactic-worker) Q-prop : is-prop Q}
  → Reflects⁰ P a → Reflects⁰ Q a → P ≃ Q
reflects-injₑ! {P-prop} {Q-prop} = reflects-injₑ P-prop Q-prop
