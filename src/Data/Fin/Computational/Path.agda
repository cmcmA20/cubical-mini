{-# OPTIONS --safe #-}
module Data.Fin.Computational.Path where

open import Foundations.Prelude

open import Meta.Extensionality

open import Data.Empty.Base as ⊥
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Path
open import Data.Nat.Order.Computational

open import Data.Fin.Computational.Base

private variable @0 n : ℕ

open Fin

fin-ext : {k₁ k₂ : Fin n} → k₁ .index ＝ k₂ .index → k₁ ＝ k₂
fin-ext {n} = ap e.from ∘ Σ-prop-path (λ _ → erased-is-prop (<-is-prop {n = n})) where
  module e = Equiv (≅→≃ fin-iso)

mk-fin-inj
  : ∀ {x y : ℕ} {b₁ b₂}
  → mk-fin {n} x {b₁}  ＝ mk-fin y {b₂} → x ＝ y
mk-fin-inj = ap unfin where
  unfin : Fin n → ℕ
  unfin (mk-fin k) = k

instance
  Extensional-Fin : Extensional (Fin n) 0ℓ
  Extensional-Fin .Pathᵉ (mk-fin u) (mk-fin v) = u ＝ v
  Extensional-Fin .reflᵉ _ = refl
  Extensional-Fin .idsᵉ .to-path = fin-ext
  Extensional-Fin .idsᵉ .to-path-over p i j = p (i ∧ j)

  H-Level-Fin0 : ∀ {k} → H-Level (1 + k) (Fin 0)
  H-Level-Fin0 = hlevel-prop-instance $ λ ()
  {-# OVERLAPPING H-Level-Fin0 #-}

  H-Level-Fin1 : ∀ {k} → H-Level k (Fin 1)
  H-Level-Fin1 = hlevel-basic-instance 0 $ fzero , λ where
    (mk-fin zero) → refl
    (mk-fin (suc j) {(b)}) → ⊥.rec (b .erased)
  {-# OVERLAPPING H-Level-Fin1 #-}
