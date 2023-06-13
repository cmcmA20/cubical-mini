{-# OPTIONS --safe #-}
module Correspondences.Nullary.Decidable where

open import Foundations.Base
open import Foundations.HLevel

open import Correspondences.Nullary.Separated

import Data.Dec.Base as Dec
open import Data.Dec.Path

open import Functions.Embedding

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

is-decidable-at-hlevel : HLevel → Type ℓ → Type ℓ
is-decidable-at-hlevel 0       = Dec
is-decidable-at-hlevel (suc n) = is-decidable-at-hlevel n on-paths-of_

is-discrete : Type ℓ → Type ℓ
is-discrete = is-decidable-at-hlevel 1

is-decidable-at-hlevel→is-separated-at-hlevel
  : (n : HLevel) → is-decidable-at-hlevel n A → is-separated-at-hlevel n A
is-decidable-at-hlevel→is-separated-at-hlevel 0 = dec→¬¬-stable
is-decidable-at-hlevel→is-separated-at-hlevel (suc n) di x y =
 is-decidable-at-hlevel→is-separated-at-hlevel n $ di x y

is-discrete→is-separated : is-discrete A → is-separated A
is-discrete→is-separated = is-decidable-at-hlevel→is-separated-at-hlevel 1

-- Hedberg
is-discrete→is-set : is-discrete A → is-set A
is-discrete→is-set = is-separated→is-set ∘ is-discrete→is-separated

is-decidable-at-hlevel-is-prop : (n : ℕ) → is-prop (is-decidable-at-hlevel (suc n) A)
is-decidable-at-hlevel-is-prop 0 d₁ d₂ i _ _ =
  dec-is-of-hlevel 1 (is-discrete→is-set d₁ _ _) (d₁ _ _) (d₂ _ _) i
is-decidable-at-hlevel-is-prop (suc n) p q i x y
  = is-decidable-at-hlevel-is-prop n (p x y) (q x y) i

is-discrete-is-prop : is-prop (is-discrete A)
is-discrete-is-prop = is-decidable-at-hlevel-is-prop 0

is-decidable-at-hlevel-suc
  : (n : HLevel)
  → is-decidable-at-hlevel (suc n) A
  → is-decidable-at-hlevel (suc (suc n)) A
is-decidable-at-hlevel-suc 0 di x y =
  Dec.rec (λ x=y p q → yes $ is-discrete→is-set di x y p q)
          (λ x≠y p q → no $ λ _ → x≠y p)
          (di x y)
is-decidable-at-hlevel-suc (suc n) di x y = is-decidable-at-hlevel-suc n $ di x y

is-of-hlevel-is-discrete : (n : HLevel) → is-discrete (is-of-hlevel n A)
is-of-hlevel-is-discrete _ _ _ = yes (is-of-hlevel-is-prop _ _ _)

is-discrete-injection : (A ↣ B) → is-discrete B → is-discrete A
is-discrete-injection (f , f-inj) B-dis x y =
  Dec.map f-inj
          (λ ¬fp p → ¬fp (ap f p))
          (B-dis (f x) (f y))

is-discrete-embedding : (A ↪ B) → is-discrete B → is-discrete A
is-discrete-embedding (f , f-emb) =
  is-discrete-injection (f , has-prop-fibres→injective f f-emb)
