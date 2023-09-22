{-# OPTIONS --safe #-}
open import Foundations.Base

open import Meta.Search.HLevel

open import Correspondences.Base

module Correspondences.Wellfounded
  {ℓ ℓ′} {A : Type ℓ} (_<_ : Corr² ℓ′ (A , A))
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

opaque
  unfolding is-of-hlevel
  acc-is-prop : ∀ x → is-prop (Acc x)
  acc-is-prop x (acc s) (acc t) = ap acc $
    fun-ext λ y → fun-ext λ y<x →
    acc-is-prop y (s y y<x) (t y y<x)

acc-is-of-hlevel : ∀ n x → is-of-hlevel (suc n) (Acc x)
acc-is-of-hlevel _ _ = is-of-hlevel-+-left 1 _ (acc-is-prop _)

instance
  decomp-hlevel-acc : ∀ {x} → goal-decomposition (quote is-of-hlevel) (Acc x)
  decomp-hlevel-acc = decomp (quote acc-is-of-hlevel) (`level-minus 1 ∷ `meta ∷ [])
