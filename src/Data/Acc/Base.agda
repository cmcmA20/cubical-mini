{-# OPTIONS --safe #-}
module Data.Acc.Base where

open import Foundations.Base
open Variadics _

data Acc
  {ℓ ℓ′} {A : Type ℓ} (_<_ : A → A → Type ℓ′)
  (x : A) : Type (ℓ ⊔ ℓ′) where
    acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  _<_ : A → A → Type ℓ
  x : A

acc-rec : Acc _<_ x → Π[ _< x ⇒ Acc _<_ ]
acc-rec (acc r) = r


-- well-foundedness aka descending chain condition
-- also called Artinianess in algebra

is-wf : (A → A → Type ℓ′) → Type (level-of-type A ⊔ ℓ′)
is-wf _<_ = Π[ Acc _<_ ]

to-induction-acc : {A : Type ℓ} {_<_ : A → A → Type ℓ′}
                 → ∀ {ℓ″} (P : A → Type ℓ″)
                 → (∀ x → Π[ _< x ⇒ P ] → P x)
                 → ∀ x → Acc _<_ x → P x
to-induction-acc P ih x (acc w) = ih x λ y y<x → to-induction-acc P ih y (w y y<x)

to-induction
  : {A : Type ℓ} {_<_ : A → A → Type ℓ′}
  → is-wf _<_
  → ∀ {ℓ″} (P : A → Type ℓ″) → (∀ x → Π[ _< x ⇒ P ] → P x) → Π[ P ]
to-induction {_<_} wf P ih x = to-induction-acc P ih x (wf x)

from-induction
  : {_<_ : A → A → Type ℓ′}
  → (∀ {ℓ″} (P : A → Type ℓ″) → (∀ x → Π[ _< x ⇒ P ] → P x) → Π[ P ])
  → is-wf _<_
from-induction {_<_} ind = ind (Acc _<_) λ _ → acc


-- Noetherianess aka ascending chain condition

is-noeth : (A → A → Type ℓ′) → Type (level-of-type A ⊔ ℓ′)
is-noeth _<_ = Π[ Acc (flip _<_) ]

to-ninduction
  : {_<_ : A → A → Type ℓ′}
  → is-noeth _<_
  → ∀ {ℓ″} (P : A → Type ℓ″) → (∀ x → Π[ x <_ ⇒ P ] → P x)
  → Π[ P ]
to-ninduction {_<_} noeth P work x = go x (noeth x)
  where
  go : ∀ x → Acc (flip _<_) x → P x
  go x (acc n) = work x λ y x<y → go y (n y x<y)

from-ninduction
  : {_<_ : A → A → Type ℓ′}
  → (∀ {ℓ″} (P : A → Type ℓ″) → (∀ x → Π[ x <_ ⇒ P ] → P x) → Π[ P ])
  → is-noeth _<_
from-ninduction {_<_} ind = ind (Acc (flip _<_)) λ _ → acc


-- finite height

is-of-finite-height : (A → A → Type ℓ′) → Type (level-of-type A ⊔ ℓ′)
is-of-finite-height _<_ = ∀ x → Acc _<_ x × Acc (flip _<_) x
