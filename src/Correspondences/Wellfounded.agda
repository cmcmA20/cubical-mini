{-# OPTIONS --safe #-}
open import Foundations.Base
  hiding (_$_)
open import Meta.Variadic

module Correspondences.Wellfounded
  {ℓ ℓ′} {A : Type ℓ} (_<_ : Corr² (A , A) ℓ′)
  where

open import Meta.Extensionality

open import Foundations.HLevel

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

opaque
  unfolding is-of-hlevel
  acc-is-prop : ∀ x → is-prop (Acc x)
  acc-is-prop x (acc s) (acc t) = ap acc $
    ext λ y y<x → acc-is-prop y (s y y<x) (t y y<x)

instance
  H-Level-acc : ∀ {x} {n} → H-Level (suc n) (Acc x)
  H-Level-acc = hlevel-prop-instance (acc-is-prop _)
