{-# OPTIONS --safe #-}
module Structures.Discrete where

open import Foundations.Base

open import Data.Dec.Base
open import Data.Dec.Path
open import Data.Empty.Base

open import Structures.Base
open import Structures.IdentitySystem.Base
open import Structures.Separated

open import Meta.HLevel
open import Meta.Reflection.HLevel

private variable
  ℓ : Level
  A : Type ℓ

is-discrete : Type ℓ → Type ℓ
is-discrete A = Dec on-paths-of A

dec→¬¬-stable : Dec A → ¬¬_ stable A
dec→¬¬-stable (no ¬a) f = absurd (f ¬a)
dec→¬¬-stable (yes a) _ = a

is-discrete→is-separated : is-discrete A → is-separated A
is-discrete→is-separated dec x y f = dec→¬¬-stable (dec x y) f

-- Hedberg
is-discrete→is-set : is-discrete A → is-set A
is-discrete→is-set = is-separated→is-set ∘ is-discrete→is-separated

is-discrete-is-prop : is-prop (is-discrete A)
is-discrete-is-prop d₁ d₂ i _ _ =
  Dec-is-of-hlevel 1 (is-discrete→is-set d₁ _ _) (d₁ _ _) (d₂ _ _) i

is-of-hlevel-is-discrete : (n : HLevel) → is-discrete (is-of-hlevel n A)
is-of-hlevel-is-discrete _ _ _ = yes (is-of-hlevel-is-prop _ _ _)
