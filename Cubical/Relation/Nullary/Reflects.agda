{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.Reflects where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty.Base as ⊥
open import Cubical.Data.Bool.Base

open import Cubical.Relation.Nullary.Negation public

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

-- infixr 2 _×-reflects_
-- _×-reflects_ : Reflects P a → Reflects Q b
--              → Reflects (P × Q) (a and b)
-- ofʸ  p ×-reflects ofʸ  q = ofʸ (p , q)
-- ofʸ  p ×-reflects ofⁿ ¬q = ofⁿ (¬q ∘ snd)
-- ofⁿ ¬p ×-reflects _      = ofⁿ (¬p ∘ fst)

det : Reflects P a → Reflects P b → a ≡ b
det (ofʸ  p) (ofʸ  p′) = refl
det (ofʸ  p) (ofⁿ ¬p′) = ⊥.rec (¬p′ p)
det (ofⁿ ¬p) (ofʸ  p′) = ⊥.rec (¬p p′)
det (ofⁿ ¬p) (ofⁿ ¬p′) = refl
