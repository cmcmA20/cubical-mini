{-# OPTIONS --safe #-}
module Prim.Data.Sigma where

open import Prim.Type

open import Agda.Builtin.Sigma public

infix 2 Σ-syntax
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ꞉ A ] B

private variable ℓ ℓ′ ℓ″ : Level

infixr 4 _×_
_×_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
A × B = Σ[ _ ꞉ A ] B

∃ᶜ : {A : Type ℓ} → (A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃ᶜ = Σ _

∃₂ᶜ : {A : Type ℓ} {B : A → Type ℓ′}
      (C : (x : A) → B x → Type ℓ″) → Type (ℓ ⊔ ℓ′ ⊔ ℓ″)
∃₂ᶜ C = ∃ᶜ λ a → ∃ᶜ λ b → C a b

infix 2 ∃ᶜ-syntax
∃ᶜ-syntax : {A : Type ℓ} → (A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃ᶜ-syntax = ∃ᶜ

syntax ∃ᶜ-syntax (λ x → B) = ∃ᶜ[ x ] B
