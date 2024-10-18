{-# OPTIONS --safe #-}
open import Foundations.Base

open import Data.Sum.Base

module Data.Wellfounded.Base
  {ℓ ℓ′} {A : Type ℓ}
  where

data Acc (_<_ : A → A → 𝒰 ℓ′) (x : A) : Type (ℓ ⊔ ℓ′) where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

acc-rec : {_<_ : A → A → 𝒰 ℓ′} {x : A}
        → Acc _<_ x
        → ∀ y → y < x → Acc _<_ y
acc-rec (acc r) = r

-- well-foundedness aka descending chain condition
-- also called Artinianess in algebra

Wf : (A → A → 𝒰 ℓ′) → 𝒰 (ℓ ⊔ ℓ′)
Wf _<_ = ∀ x → Acc _<_ x

to-induction
  : {_<_ : A → A → 𝒰 ℓ′}
  → Wf _<_ → ∀ {ℓ″} (P : A → Type ℓ″)
  → (∀ x → (∀ y → y < x → P y) → P x)
  → ∀ x → P x
to-induction {_<_} wf P work x = go x (wf x) where
  go : ∀ x → Acc _<_ x → P x
  go x (acc w) = work x λ y y<x → go y (w y y<x)

from-induction
  : {_<_ : A → A → 𝒰 ℓ′}
  → ( ∀ {ℓ″} (P : A → Type ℓ″)
    → (∀ x → (∀ y → y < x → P y) → P x)
    → ∀ x → P x )
  → Wf _<_
from-induction {_<_} ind = ind (Acc _<_) λ _ → acc

-- Noetherianess aka ascending chain condition

Noeth : (A → A → 𝒰 ℓ′) → 𝒰 (ℓ ⊔ ℓ′)
Noeth _<_ = ∀ x → Acc (flip _<_) x

to-ninduction
  : {_<_ : A → A → 𝒰 ℓ′}
  → Noeth _<_ → ∀ {ℓ″} (P : A → Type ℓ″)
  → (∀ x → (∀ y → x < y → P y) → P x)
  → ∀ x → P x
to-ninduction {_<_} noeth P work x = go x (noeth x)
  where
  go : ∀ x → Acc (flip _<_) x → P x
  go x (acc n) = work x λ y x<y → go y (n y x<y)

from-ninduction
  : {_<_ : A → A → 𝒰 ℓ′}
  → ( ∀ {ℓ″} (P : A → Type ℓ″)
    → (∀ x → (∀ y → x < y → P y) → P x)
    → ∀ x → P x )
  → Noeth _<_
from-ninduction {_<_} ind = ind (Acc (flip _<_)) λ _ → acc

-- finite height

FinHeight : (A → A → 𝒰 ℓ′) → 𝒰 (ℓ ⊔ ℓ′)
FinHeight _<_ = ∀ x → Acc _<_ x × Acc (flip _<_) x
