{-# OPTIONS --safe #-}
module Data.Char.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Char.Base
open import Data.Char.Properties
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Reflects.Base

private variable c c₁ c₂ : Char

instance
  Reflects-Char-Path : Reflects (c₁ ＝ c₂) (char→ℕ c₁ == char→ℕ c₂)
  Reflects-Char-Path {c₁} {c₂} with char→ℕ c₁ == char→ℕ c₂ | recall (char→ℕ c₁ ==_) (char→ℕ c₂)
  ... | false | ⟪ p ⟫ = ofⁿ λ c₁=c₂ → false≠true (p ⁻¹ ∙ (so≃is-true $ true→so! $ ap char→ℕ c₁=c₂))
  ... | true  | ⟪ p ⟫ = ofʸ (char→ℕ-inj (so→true! $ so≃is-true ⁻¹ $ p))

  Char-is-discrete : is-discrete Char
  Char-is-discrete = reflects-path→is-discrete!
  {-# OVERLAPPING Char-is-discrete #-}

Extensional-Char : Extensional Char 0ℓ
Extensional-Char = reflects-path→extensional!

instance opaque
  H-Level-Char : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n Char
  H-Level-Char ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel! 1 (Extensional-Char .idsᵉ)
