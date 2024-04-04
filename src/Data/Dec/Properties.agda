{-# OPTIONS --safe #-}
module Data.Dec.Properties where

open import Meta.Prelude

open import Meta.Effect.Idiom
open import Meta.Search.HLevel

open import Truncation.Propositional as ∥-∥₁

open import Data.Empty.Properties
open import Data.Sum.Properties

open import Data.Dec.Base as Dec
open import Data.Dec.Path

private variable
  ℓ ℓ′ : Level
  A P : Type ℓ
  B : Type ℓ′

dec-∥-∥₁-equiv : ∥ Dec P ∥₁ ≃ Dec ∥ P ∥₁
dec-∥-∥₁-equiv = prop-extₑ!
  (∥-∥₁.rec! $ Dec.dmap pure ∥-∥₁.rec!)
  (Dec.rec (yes <$>_) (pure ∘ no ∘ contra pure))

dec-≃ : A ≃ B → Dec A ≃ Dec B
dec-≃ {A} {B} e = iso→≃ $ to , iso from ri li where
  to   = Dec.dmap (e    $_) (contra (e ⁻¹ $_))
  from = Dec.dmap (e ⁻¹ $_) (contra (e    $_))

  module e = Equiv e

  ri : from is-right-inverse-of to
  ri = Dec.elim (ap yes ∘ e.ε) (ap no ∘ λ _ → prop!)

  li : from is-left-inverse-of to
  li = Dec.elim (ap yes ∘ e.η) (ap no ∘ λ _ → prop!)

≃→dec : (B ≃ A) → Dec A → Dec B
≃→dec e = dec-≃ e ⁻¹ $_
