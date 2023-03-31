{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.Decidable where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool.Base

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Reflects public

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
Discrete = onAllPaths Dec

recompute : Dec A → @0 A → A
recompute (yes a) _  = a
recompute (no ¬a) 0a = ⊥.rec (¬a 0a)

decRec : (B → A) → (¬ B → A) → Dec B → A
decRec ifyes ifno (yes p) = ifyes p
decRec ifyes ifno (no ¬p) = ifno ¬p
