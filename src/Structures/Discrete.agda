{-# OPTIONS --safe #-}
module Structures.Discrete where

open import Foundations.Base
open import Foundations.HLevel

open import Data.Dec.Path

open import Structures.Base
open import Structures.DoubleNegation.Base

private variable
  ℓ : Level
  A : Type ℓ

is-discrete : Type ℓ → Type ℓ
is-discrete A = Dec on-paths-of A

is-discrete→is-separated : is-discrete A → is-separated A
is-discrete→is-separated dec x y f = dec→¬¬-stable (dec x y) f

-- Hedberg
is-discrete→is-set : is-discrete A → is-set A
is-discrete→is-set = is-separated→is-set ∘ is-discrete→is-separated

is-discrete-is-prop : is-prop (is-discrete A)
is-discrete-is-prop d₁ d₂ i _ _ =
  dec-is-of-hlevel 1 (is-discrete→is-set d₁ _ _) (d₁ _ _) (d₂ _ _) i

is-of-hlevel-is-discrete : (n : HLevel) → is-discrete (is-of-hlevel n A)
is-of-hlevel-is-discrete _ _ _ = yes (is-of-hlevel-is-prop _ _ _)
