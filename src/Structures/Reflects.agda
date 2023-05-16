{-# OPTIONS --safe #-}
module Structures.Reflects where

open import Foundations.Base
open import Data.Empty.Base as ⊥
open import Data.Bool.Base
open import Structures.Negation public

data Reflects {ℓ} (P : Type ℓ) : Bool → Type ℓ where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false

private variable
  ℓ ℓ′ : Level
  P : Type ℓ
  Q : Type ℓ′
  a b : Bool

of : if b then P else ¬ P → Reflects P b
of {b = false} ¬p = ofⁿ ¬p
of {b = true }  p = ofʸ p

invert : Reflects P b → if b then P else ¬ P
invert (ofʸ  p) = p
invert (ofⁿ ¬p) = ¬p

¬-reflects : Reflects P b → Reflects (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

det : Reflects P a → Reflects P b → a ＝ b
det (ofʸ  p) (ofʸ  p′) = refl
det (ofʸ  p) (ofⁿ ¬p′) = ⊥.rec (¬p′ p)
det (ofⁿ ¬p) (ofʸ  p′) = ⊥.rec (¬p p′)
det (ofⁿ ¬p) (ofⁿ ¬p′) = refl
