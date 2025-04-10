{-# OPTIONS --safe #-}
module Data.Fin.Operations.Properties where

open import Meta.Prelude

open import Data.Empty
open import Data.Fin as Fin
open import Data.Fin.Operations

private variable
  ℓ ℓ′ ℓ″ : Level
  n : ℕ

avoid-insert
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : Fin n → A)
  → (f : Fin (suc n)) (a : A)
  → (g : Fin (suc n))
  → (f≠g : f ≠ g)
  → (ρ [ f ≔ a ]) g ＝ ρ (avoid f g f≠g)
avoid-insert ρ f a g f≠g with fin-view f | fin-view g
avoid-insert             ρ  .fzero   a  .fzero   f≠g | zero  | zero  = absurd (f≠g refl)
avoid-insert             ρ  .fzero   a .(fsuc g) f≠g | zero  | suc g = refl
avoid-insert {n = suc n} ρ .(fsuc f) a  .fzero   f≠g | suc f | zero  = refl
avoid-insert {n = suc n} ρ .(fsuc f) a .(fsuc g) f≠g | suc f | suc g =
  avoid-insert (ρ ∘ fsuc) f a g (f≠g ∘ ap fsuc)

insert-lookup
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : Fin n → A)
  → (f : Fin (suc n)) (a : A)
  → (ρ [ f ≔ a ]) f ＝ a
insert-lookup ρ f a with fin-view f
insert-lookup             ρ  .fzero   a | zero  = refl
insert-lookup {n = suc n} ρ .(fsuc f) a | suc f =
  insert-lookup (ρ ∘ fsuc) f a

insert-delete
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : Fin (suc n) → A)
  → (i : Fin (suc n)) (a : A)
  → ρ i ＝ a
  → ∀ j → ((delete ρ i) [ i ≔ a ]) j ＝ ρ j
insert-delete ρ f a e g with fin-view f | fin-view g
insert-delete             ρ  .fzero   a e  .fzero   | zero  | zero  = e ⁻¹
insert-delete             ρ  .fzero   a e .(fsuc g) | zero  | suc g = refl
insert-delete {n = suc n} ρ .(fsuc f) a e  .fzero   | suc f | zero  = refl
insert-delete {n = suc n} ρ .(fsuc f) a e .(fsuc g) | suc f | suc g =
  insert-delete (ρ ∘ fsuc) f a e g
