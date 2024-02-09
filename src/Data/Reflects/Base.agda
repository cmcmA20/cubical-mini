{-# OPTIONS --safe #-}
module Data.Reflects.Base where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Empty.Base as ⊥

data Reflects⁰ {ℓ} (P : Type ℓ) : Bool → Type ℓ where
  ofʸ : ( p :   P) → Reflects⁰ P true
  ofⁿ : (¬p : ¬ P) → Reflects⁰ P false

private variable
  ℓ ℓ′ : Level
  a b : Bool
  P : Type ℓ
  Q : Type ℓ′

true-reflects : Reflects⁰ P a → ⟦ a ⟧ᵇ → P
true-reflects (ofʸ p) tt = p

false-reflects : Reflects⁰ P a → ⟦ not a ⟧ᵇ → ¬ P
false-reflects (ofⁿ ¬p) tt = ¬p

reflects-true : Reflects⁰ P a → P → ⟦ a ⟧ᵇ
reflects-true (ofʸ  p₀) p = tt
reflects-true (ofⁿ ¬p)  p = ¬p p

reflects-false : Reflects⁰ P a → ¬ P → ⟦ not a ⟧ᵇ
reflects-false (ofʸ p)   ¬p = ¬p p
reflects-false (ofⁿ ¬p₀) ¬p = tt

invert-true : Reflects⁰ P true → P
invert-true r = true-reflects r tt

invert-false : Reflects⁰ P false → ¬ P
invert-false r = false-reflects r tt

of : if b then P else ¬ P → Reflects⁰ P b
of {b = false} ¬p = ofⁿ ¬p
of {b = true }  p = ofʸ p

invert : Reflects⁰ P b → if b then P else ¬ P
invert (ofʸ  p) = p
invert (ofⁿ ¬p) = ¬p

dmap : (P → Q) → (¬ P → ¬ Q) → Reflects⁰ P b → Reflects⁰ Q b
dmap to fro (ofʸ  p) = ofʸ (to p)
dmap to fro (ofⁿ ¬p) = ofⁿ (fro ¬p)
