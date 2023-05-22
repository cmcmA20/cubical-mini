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

dec→¬¬-stable : Dec A → ¬¬_ stable A
dec→¬¬-stable (no ¬a) f = absurd (f ¬a)
dec→¬¬-stable (yes a) _ = a

discrete→separated : Discrete A → Separated A
discrete→separated dec x y f = dec→¬¬-stable (dec x y) f

-- Hedberg
discrete→is-set : Discrete A → is-set A
discrete→is-set dec =
  identity-system→hlevel 1
    (separated-identity-system (discrete→separated dec)) λ _ _ _ f →
      fun-ext λ g → absurd (f g)
