{-# OPTIONS --safe #-}
module Data.Sigma.Base where

open import Foundations.Base
open import Foundations.Sigma.Base public

open import Truncation.Propositional.Base

private variable
  ℓ ℓ′ : Level

-- Unique existence

∃! : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃! A B = is-contr (Σ[ a ꞉ A ] B a)


-- Mere existence

∃ : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃ A B = ∥ Σ[ a ꞉ A ] B a ∥₁

infix 2 ∃-syntax

∃-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ꞉ A ] B
