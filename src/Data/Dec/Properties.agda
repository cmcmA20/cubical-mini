{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Meta.Prelude

open import Meta.Effect.Idiom

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∥_∥₁)

open import Data.Empty.Properties
open import Data.Sum.Properties

open import Data.Dec.Base as Dec
open import Data.Dec.Path

private variable
  ℓ ℓ′ : Level
  A P : Type ℓ
  B : Type ℓ′

∥-∥₁∘dec≃dec∘∥-∥₁ : ∥ Dec P ∥₁ ≃ Dec ∥ P ∥₁
∥-∥₁∘dec≃dec∘∥-∥₁ = prop-extₑ!
  (∥-∥₁.rec! $ Dec.dmap pure ∥-∥₁.rec!)
  (Dec.rec (yes <$>_) (pure ∘ no ∘ contra pure))

ae : A ≃ B → Dec A ≃ Dec B
ae {A} {B} e = ≅→≃ $ to , iso from ri li where
  to   = Dec.dmap (e    $_) (contra (e ⁻¹ $_))
  from = Dec.dmap (e ⁻¹ $_) (contra (e    $_))

  module e = Equiv e

  ri : from is-right-inverse-of to
  ri = Dec.elim (ap yes ∘ e.ε) (ap no ∘ λ _ → prop!)

  li : from is-left-inverse-of to
  li = Dec.elim (ap yes ∘ e.η) (ap no ∘ λ _ → prop!)

≃→dec : (B ≃ A) → Dec A → Dec B
≃→dec e = ae e ⁻¹ $_
