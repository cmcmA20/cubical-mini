{-# OPTIONS --safe #-}
module Correspondences.Exhaustible where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Base public
open import Correspondences.Decidable

open import Data.Dec.Instances.HLevel

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

opaque
  is-exhaustible-at-hlevel : {ℓ′ : Level} → HLevel → Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
  is-exhaustible-at-hlevel {ℓ′} 0 A =
    {P : Pred₁ ℓ′ A} → Decidable ⌞ P ⌟ₚ → Decision (Π[ ⌞_⌟ ∘ P ])
  is-exhaustible-at-hlevel {ℓ′} (suc n) = is-exhaustible-at-hlevel {ℓ′ = ℓ′} n on-paths-of_

is-exhaustible : {ℓ′ : Level} → Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
is-exhaustible {ℓ′} = is-exhaustible-at-hlevel {ℓ′ = ℓ′} 0
{-# INLINE is-exhaustible #-}

opaque
  unfolding is-exhaustible-at-hlevel is-decidable-at-hlevel
  is-exhaustible-is-prop : is-prop (is-exhaustible {ℓ′ = ℓ′} A)
  is-exhaustible-is-prop = hlevel!
