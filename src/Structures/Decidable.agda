{-# OPTIONS --safe #-}
module Structures.Decidable where

open import Foundations.Base
open import Foundations.Univalence.SIP
import      Data.Empty as ⊥
open import Data.Bool.Base

open import Structures.Path     public
open import Structures.Reflects public

infix 2 _because_

record Dec {ℓ} (P : Type ℓ) : Type ℓ where
  constructor _because_
  field
    does  : Bool
    proof : Reflects P does
open Dec public

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

Discrete : Type ℓ → Type ℓ
Discrete A = Dec on-paths-of A

recompute : Dec A → @0 A → A
recompute (yes a) _  = a
recompute (no ¬a) 0a = ⊥.rec (¬a 0a)

rec : (A → B) → (¬ A → B) → Dec A → B
rec ifyes ifno (yes p) = ifyes p
rec ifyes ifno (no ¬p) = ifno ¬p

⌊_⌋ : Dec A → Bool
⌊ false because _ ⌋ = false
⌊ true  because _ ⌋ = true
