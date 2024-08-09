{-# OPTIONS --safe #-}
module Data.Float.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Dec.Base as Dec
open import Data.Float.Base
open import Data.Float.Properties
open import Data.Maybe.Path
open import Data.Reflects.Base
open import Data.Word.Path

private variable f f₁ f₂ : Float

instance
  Reflects-Float-Path : Reflects (f₁ ＝ f₂) (float→word64ᵐ f₁ =? float→word64ᵐ f₂)
  Reflects-Float-Path {f₁} {f₂} =
    caseᵈ float→word64ᵐ f₁ ＝ float→word64ᵐ f₂
    return (λ d → Reflects (f₁ ＝ f₂) ⌊ d ⌋) of λ where
      (no ¬p) → ofⁿ (λ p → ¬p (ap float→word64ᵐ p))
      (yes p) → ofʸ (float→word64ᵐ-inj p)

  Float-is-discrete : is-discrete Float
  Float-is-discrete = reflects-path→is-discrete!
  {-# OVERLAPPING Float-is-discrete #-}

Extensional-Float : Extensional Float 0ℓ
Extensional-Float = reflects-path→extensional!

instance opaque
  H-Level-Float : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n Float
  H-Level-Float ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel! 1 (Extensional-Float .idsᵉ)
