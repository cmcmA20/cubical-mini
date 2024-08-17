{-# OPTIONS --safe #-}
module Data.Bool.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Bool.Base  as Bool
open import Data.Empty.Base as ⊥
open import Data.Unit.Base  as ⊤
open import Data.Reflects.Base as Reflects

private variable
  ℓ : Level
  b b₁ b₂ : Bool
  n : HLevel

instance
  Reflects-Bool-Path : Reflects (b₁ ＝ b₂) (b₁ equals b₂)
  Reflects-Bool-Path {(false)} {(false)} = ofʸ refl
  Reflects-Bool-Path {(false)} {(true)}  = ofⁿ λ p → ¬-so-false (subst So (p ⁻¹) oh)
  Reflects-Bool-Path {(true)}  {(false)} = ofⁿ λ p → ¬-so-false (subst So p oh)
  Reflects-Bool-Path {(true)}  {(true)}  = ofʸ refl

  Bool-is-discrete : is-discrete Bool
  Bool-is-discrete = reflects-path→is-discrete!

Extensional-Bool : Extensional Bool 0ℓ
Extensional-Bool = reflects-path→extensional!

instance opaque
  H-Level-Bool : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n Bool
  H-Level-Bool ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ identity-system→is-of-hlevel! 1 (Extensional-Bool .idsᵉ)
  {-# OVERLAPPING H-Level-Bool #-}

not-inj : not b₁ ＝ not b₂ → b₁ ＝ b₂
not-inj {(false)} {(false)} e = refl
not-inj {(false)} {(true)}  e = e ⁻¹
not-inj {(true)}  {(false)} e = e ⁻¹
not-inj {(true)}  {(true)}  e = refl

so≃is-true : So b ≃ is-true b
so≃is-true = go ∙ identity-system-gives-path (Extensional-Bool .idsᵉ) where
  go : ⌞ b ⌟ ≃ ⌞ b equals true ⌟
  go {(false)} = refl
  go {(true)}  = refl

¬so≃is-false : (¬ ⌞ b ⌟) ≃ is-false b
¬so≃is-false = go ∙ identity-system-gives-path (Extensional-Bool .idsᵉ) where
  go : (¬ ⌞ b ⌟) ≃ ⌞ b equals false ⌟
  go {(false)} = prop-extₑ! _ λ _ → λ ()
  go {(true)}  = prop-extₑ! false! λ()
