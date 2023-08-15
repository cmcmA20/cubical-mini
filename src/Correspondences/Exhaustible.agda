{-# OPTIONS --safe #-}
module Correspondences.Exhaustible where

open import Foundations.Base

open import Meta.Search.HLevel

open import Correspondences.Base public
open import Correspondences.Decidable

open import Data.Dec.Base as Dec
open import Data.Dec.Instances.HLevel

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ

opaque
  Exhaustible : {ℓ′ : Level} → Type ℓ → Type (ℓ ⊔ ℓsuc ℓ′)
  Exhaustible {ℓ′} A =
    {P : Pred ℓ′ A} → Decidable P → Dec Π[ P ]

  exhaustible-β : Exhaustible A → {P : Pred ℓ′ A} → Decidable P → Dec Π[ P ]
  exhaustible-β = id

  exhaustible-η : ({P : Pred ℓ′ A} → Decidable P → Dec Π[ P ]) → Exhaustible A
  exhaustible-η = id

exhaust : ⦃ x : Exhaustible {ℓ′ = ℓ′} A ⦄ → Exhaustible A
exhaust ⦃ x ⦄ = x

opaque
  unfolding Exhaustible
  lift-exhaustible
    : Exhaustible {ℓ′ = ℓ′} A → Exhaustible (Lift ℓ A)
  lift-exhaustible ex P? = Dec.map (_∘ lower) (λ ¬f g → ¬f $ g ∘ lift) $ ex $ P? ∘ lift

Π-decision : {B : A → Type ℓᵇ} → Decidable B → Exhaustible {ℓ′ = ℓᵇ} A → Dec Π[ B ]
Π-decision d ex = exhaustible-β ex d
