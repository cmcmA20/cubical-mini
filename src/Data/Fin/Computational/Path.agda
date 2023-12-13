{-# OPTIONS --safe #-}
module Data.Fin.Computational.Path where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Sigma

open import Correspondences.Erased

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Order.Computational

open import Data.Fin.Computational.Base

private variable @0 n : ℕ

open Fin

fin-ext : {k₁ k₂ : Fin n} → k₁ .index ＝ k₂ .index → k₁ ＝ k₂
fin-ext {n} = ap e.from ∘ Σ-prop-path (λ _ → ∥-∥ᴱ-is-prop (<-is-prop {n = n})) where
  module e = Equiv (iso→equiv fin-iso)
