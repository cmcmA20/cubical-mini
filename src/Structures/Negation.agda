{-# OPTIONS --safe #-}
module Structures.Negation where

open import Foundations.Base
open import Data.Empty.Base

private variable
  ℓ  : Level
  A  : Type ℓ

infix 3 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

is-non-empty : Type ℓ → Type ℓ
is-non-empty A = ¬ ¬ A

is-stable : Type ℓ → Type ℓ
is-stable A = is-non-empty A → A

-- TODO move
-- _≠_ : A → A → Type (level-of-type A)
-- x ≠ y = ¬ (x ＝ y)
