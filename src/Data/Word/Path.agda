{-# OPTIONS --safe #-}
module Data.Word.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Word.Base
open import Data.Word.Properties
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Reflects.Base

private variable w w₁ w₂ : Word64

instance
  Reflects-Word64-Path : Reflects (w₁ ＝ w₂) (word64→ℕ w₁ == word64→ℕ w₂)
  Reflects-Word64-Path {w₁} {w₂} with word64→ℕ w₁ == word64→ℕ w₂ | recall (word64→ℕ w₁ ==_) (word64→ℕ w₂)
  ... | false | ⟪ p ⟫ = ofⁿ λ w₁=w₂ → false! (p ⁻¹ ∙ (so≃is-true $ true→so! $ ap word64→ℕ w₁=w₂))
  ... | true  | ⟪ p ⟫ = ofʸ (word64→ℕ-inj (so→true! $ so≃is-true ⁻¹ $ p))

  Word64-is-discrete : is-discrete Word64
  Word64-is-discrete = reflects-path→is-discrete!

Extensional-Word64 : Extensional Word64 0ℓ
Extensional-Word64 = reflects-path→extensional!

instance opaque
  H-Level-Word64 : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n Word64
  H-Level-Word64 ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel! 1 (Extensional-Word64 .idsᵉ)
