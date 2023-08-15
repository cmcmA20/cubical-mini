{-# OPTIONS --safe #-}
module Data.Bool.Base where

open import Foundations.Base

open import Data.Empty.Base using (⊥)
open import Data.Unit.Base  using (⊤)

open import Agda.Builtin.Bool public

private variable
  ℓ : Level
  A : Type ℓ

elim : {P : Bool → Type ℓ} (t : P true) (f : P false) (b : Bool) → P b
elim _ f false = f
elim t _ true  = t

rec : A → A → Bool → A
rec = elim

not : Bool → Bool
not true = false
not false = true

infixr 5 _or_
_or_ : Bool → Bool → Bool
false or x = x
true  or _ = true

infixr 6 _and_
_and_ : Bool → Bool → Bool
false and _ = false
true  and x = x

-- xor / mod-2 addition
infixr 5 _⊕_
_⊕_ : Bool → Bool → Bool
false ⊕ x = x
true  ⊕ x = not x

infix 0 if_then_else_
if_then_else_ : Bool → A → A → A
if b then tr else fa = rec tr fa b

⟦_⟧ᵇ : Bool → Type
⟦ b ⟧ᵇ = if b then ⊤ else ⊥
