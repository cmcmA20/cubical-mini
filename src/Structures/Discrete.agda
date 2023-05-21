{-# OPTIONS --safe #-}
module Structures.Discrete where

open import Foundations.Base

open import Data.Dec.Base
open import Data.Empty.Base

open import Structures.Base
open import Structures.IdentitySystem.Base
open import Structures.Separated

private variable
  ℓ : Level
  A : Type ℓ

Discrete : Type ℓ → Type ℓ
Discrete A = Dec on-paths-of A

-- Hedberg
Discrete→is-set : Discrete A → is-set A
Discrete→is-set dec =
  identity-system→hlevel 1 (separated-identity-system helper) λ _ _ _ f →
    fun-ext λ g → absurd (f g)
  where
    helper : Separated _
    helper x y ¬¬p with dec x y
    ... | yes p = p
    ... | no ¬p = absurd (¬¬p ¬p)
