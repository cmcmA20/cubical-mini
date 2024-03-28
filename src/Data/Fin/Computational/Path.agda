{-# OPTIONS --safe #-}
module Data.Fin.Computational.Path where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel
open import Foundations.Sigma

open import Meta.Extensionality

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Order.Computational

open import Data.Fin.Computational.Base

private variable @0 n : ℕ

open Fin

fin-ext : {k₁ k₂ : Fin n} → k₁ .index ＝ k₂ .index → k₁ ＝ k₂
fin-ext {n} = ap e.from ∘ Σ-prop-path (λ _ → erased-is-prop (<-is-prop {n = n})) where
  module e = Equiv (≅→≃ fin-iso)

instance
  Extensional-Fin : Extensional (Fin n) 0ℓ
  Extensional-Fin .Pathᵉ (mk-fin u) (mk-fin v) = u ＝ v
  Extensional-Fin .reflᵉ _ = refl
  Extensional-Fin .idsᵉ .to-path = fin-ext
  Extensional-Fin .idsᵉ .to-path-over p i j = p (i ∧ j)
