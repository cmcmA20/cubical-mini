{-# OPTIONS --safe #-}
module Data.String.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Char.Path
open import Data.Dec.Base as Dec
open import Data.List.Path
open import Data.Reflects.Base
open import Data.String.Base
open import Data.String.Properties

private variable s s₁ s₂ : String

instance
  Reflects-String-Path : Reflects (s₁ ＝ s₂) (string→list s₁ =? string→list s₂)
  Reflects-String-Path {s₁} {s₂} =
    caseᵈ string→list s₁ ＝ string→list s₂
    return (λ d → Reflects (s₁ ＝ s₂) ⌊ d ⌋) of λ where
      (no ¬p) → ofⁿ (λ p → ¬p (ap string→list p))
      (yes p) → ofʸ (string→list-inj p)

  String-is-discrete : is-discrete String
  String-is-discrete = reflects-path→is-discrete!

Extensional-String : Extensional String 0ℓ
Extensional-String = reflects-path→extensional!

instance opaque
  H-Level-String : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n String
  H-Level-String ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel! 1 (Extensional-String .idsᵉ)
