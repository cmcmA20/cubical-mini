{-# OPTIONS --safe #-}
module Correspondences.Nullary.Discrete where

open import Foundations.Base
open import Foundations.HLevel

open import Structures.Base

open import Correspondences.Nullary.DoubleNegation.Base

open import Data.Dec.Path

open import Functions.Embedding

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

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

is-discrete-injection : (A ↣ B) → is-discrete B → is-discrete A
is-discrete-injection (f , f-inj) B-dis x y =
  map f-inj
      (λ ¬fp p → ¬fp (ap f p))
      (B-dis (f x) (f y))

is-discrete-embedding : (A ↪ B) → is-discrete B → is-discrete A
is-discrete-embedding (f , f-emb) =
  is-discrete-injection (f , has-prop-fibres→injective f f-emb)
