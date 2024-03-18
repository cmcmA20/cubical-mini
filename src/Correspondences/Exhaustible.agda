{-# OPTIONS --safe #-}
module Correspondences.Exhaustible where

open import Meta.Prelude

open import Meta.Search.HLevel

open import Correspondences.Base public
open import Correspondences.Decidable

open import Data.Dec as Dec

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ

record Exhaustible {ℓ : Level} {ℓᵃ : Level} (A : Type ℓᵃ) : Type (ℓᵃ ⊔ ℓsuc ℓ) where
  no-eta-equality
  constructor exhaustible-η
  field exhaustible-β : {P : Pred A ℓ} → Decidable P → Dec Π[ P ]

open Exhaustible public

exhaust : ⦃ x : Exhaustible {ℓ} A ⦄ → Exhaustible A
exhaust ⦃ x ⦄ = x

lift-exhaustible : Exhaustible {ℓ} A → Exhaustible (Lift ℓ A)
lift-exhaustible ex .exhaustible-β P? = Dec.dmap (_∘ lower) (λ ¬f g → ¬f $ g ∘ lift)
  (ex .exhaustible-β $ P? ∘ lift)

Π-decision : {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} {B : Pred A ℓᵇ} → Decidable B → Exhaustible A → Dec Π[ B ]
Π-decision d ex = ex .exhaustible-β d

∀-decision : {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} {B : Pred A ℓᵇ} → Decidable B → Exhaustible A → Dec ∀[ B ]
∀-decision d ex = dec-≃ Π-impl-Π-≃ $ Π-decision d ex
