{-# OPTIONS --safe #-}
open import Foundations.Base

module Data.Wellfounded.Base
  {ℓ ℓ′} {A : Type ℓ} (_<_ : A → A → 𝒰 ℓ′)
  where

data Acc (x : A) : Type (ℓ ⊔ ℓ′) where
  acc : (∀ y → y < x → Acc y) → Acc x

Wf : Type _
Wf = ∀ x → Acc x

to-induction
  : Wf → ∀ {ℓ″} (P : A → Type ℓ″)
  → (∀ x → (∀ y → y < x → P y) → P x)
  → ∀ x → P x
to-induction wf P work x = go x (wf x) where
  go : ∀ x → Acc x → P x
  go x (acc w) = work x λ y y<x → go y (w y y<x)

from-induction
  : ( ∀ {ℓ″} (P : A → Type ℓ″)
    → (∀ x → (∀ y → y < x → P y) → P x)
    → ∀ x → P x )
  → Wf
from-induction ind = ind Acc λ _ → acc
