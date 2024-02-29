{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.Extensional where

open import Foundations.Base

open import Meta.Extensionality
open import Meta.Search.HLevel

open import Functions.Embedding

open import Truncation.Propositional.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : A → Type ℓ′

Extensional-Σ-trunc : ⦃ ea : Extensional A ℓ″ ⦄ → Extensional (Σ[ x ꞉ A ] ∥ B x ∥₁) ℓ″
Extensional-Σ-trunc ⦃ ea ⦄ = Σ-prop→extensional (λ _ → hlevel 1) ea

instance
  extensionality-Σ-trunc : Extensionality (Σ[ x ꞉ A ] ∥ B x ∥₁)
  extensionality-Σ-trunc .Extensionality.lemma = quote Extensional-Σ-trunc
