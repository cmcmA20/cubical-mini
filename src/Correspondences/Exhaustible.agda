{-# OPTIONS --safe #-}
module Correspondences.Exhaustible where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Base public
open import Correspondences.Decidable

open import Data.Dec.Base as Dec
open import Data.Dec.Instances.HLevel

private variable
  ℓ ℓ′ ℓᵃ : Level
  A : Type ℓᵃ

opaque
  is-exhaustible : {ℓ′ : Level} → Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
  is-exhaustible {ℓ′} A =
    {P : Pred₁ ℓ′ A} → Decidable ⌞ P ⌟ₚ → Dec (Π[ P ]ₙ)

  is-exhaustible-β : is-exhaustible A → {P : Pred₁ ℓ′ A} → Decidable ⌞ P ⌟ₚ → Dec Π[ P ]ₙ
  is-exhaustible-β = id

  is-exhaustible-η : ({P : Pred₁ ℓ′ A} → Decidable ⌞ P ⌟ₚ → Dec Π[ P ]ₙ) → is-exhaustible A
  is-exhaustible-η = id

  is-exhaustible-is-prop : is-prop (is-exhaustible {ℓ′ = ℓ′} A)
  is-exhaustible-is-prop = hlevel!

exhaust : ⦃ x : is-exhaustible {ℓ′ = ℓ′} A ⦄ → is-exhaustible A
exhaust ⦃ x ⦄ = x

opaque
  unfolding is-exhaustible
  lift-is-exhaustible
    : is-exhaustible {ℓ′ = ℓ′} A → is-exhaustible (Lift ℓ A)
  lift-is-exhaustible ex P? = Dec.map (_∘ lower) (λ ¬f g → ¬f $ g ∘ lift) $ ex $ P? ∘ lift
