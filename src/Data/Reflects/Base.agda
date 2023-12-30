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

invert-true : Reflects⁰ P true → P
invert-true (ofʸ p) = p

invert-false : Reflects⁰ P false → ¬ P
invert-false (ofⁿ ¬p) = ¬p

of : if b then P else ¬ P → Reflects⁰ P b
of {b = false} ¬p = ofⁿ ¬p
of {b = true }  p = ofʸ p

invert : Reflects⁰ P b → if b then P else ¬ P
invert (ofʸ  p) = p
invert (ofⁿ ¬p) = ¬p

dmap : (P → Q) → (¬ P → ¬ Q) → Reflects⁰ P b → Reflects⁰ Q b
dmap to fro (ofʸ  p) = ofʸ (to p)
dmap to fro (ofⁿ ¬p) = ofⁿ (fro ¬p)
