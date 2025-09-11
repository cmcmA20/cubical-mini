{-# OPTIONS --safe #-}
module Data.Fin.Operations where

open import Foundations.Base

open import Data.Empty.Base as ⊥
  using (_≠_)
open import Data.Fin.Interface
open import Data.Maybe.Base
  using (Maybe; nothing; just)
open import Data.Nat.Base
  using (ℕ; zero; suc)
open import Data.Sum.Base
  using (_⊎ₜ_; inl; inr)
open import Data.Fin.Base

private variable
  ℓ : Level
  A : Type ℓ
  m n : ℕ

weaken : Fin n → Fin (suc n)
weaken = just

data Fin-view : {n : ℕ} → Fin n → Type where
  zero : ∀ {n}             → Fin-view {suc n}  fzero
  suc  : ∀ {n} (f : Fin n) → Fin-view {suc n} (fsuc f)

fin-view : ∀ {n} (i : Fin n) → Fin-view i
fin-view {n = zero}   f       = ⊥.absurd f
fin-view {n = suc n} (fsuc x) = suc x
fin-view {n = suc n}  fzero   = zero

skip : ∀ {n} → Fin (suc n) → Fin n → Fin (suc n)
skip f g with fin-view f | fin-view g
skip              .fzero     g       | zero  | _     = fsuc g
skip             .(fsuc f)  .fzero   | suc f | zero  = fzero
skip {n = suc n} .(fsuc f) .(fsuc g) | suc f | suc g = fsuc (skip f g)

avoid : ∀ {n} (f g : Fin (suc n)) → f ≠ g → Fin n
avoid               f         g       f≠g with fin-view f | fin-view g
avoid              .fzero    .fzero   f≠g | zero  | zero  = ⊥.absurd (f≠g refl)
avoid              .fzero   .(fsuc g) f≠g | zero  | suc g = g
avoid {n = suc n} .(fsuc f)  .fzero   f≠g | suc f | zero  = fzero
avoid {n = suc n} .(fsuc f) .(fsuc g) f≠g | suc f | suc g = fsuc (avoid f g (f≠g ∘ ap fsuc))

_[_≔_] : ∀ {n}
       → (Fin n → A) → Fin (suc n) → A
       → Fin (suc n) → A
_[_≔_] p f a g with fin-view f | fin-view g
_[_≔_]             p  .fzero   a  .fzero   | zero  | zero  = a
_[_≔_]             p  .fzero   a .(fsuc g) | zero  | suc g = p g
_[_≔_] {n = suc n} p .(fsuc f) a  .fzero   | suc f | zero  = p fzero
_[_≔_] {n = suc n} p .(fsuc f) a .(fsuc g) | suc f | suc g = ((p ∘ fsuc) [ f ≔ a ]) g

delete
  : ∀ {ℓ} {A : Type ℓ} {n}
  → (Fin (suc n) → A) → Fin (suc n)
  → Fin n → A
delete ρ i j = ρ (skip i j)
