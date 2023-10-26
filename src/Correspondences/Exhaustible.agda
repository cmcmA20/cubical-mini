{-# OPTIONS --safe #-}
module Correspondences.Exhaustible where

open import Foundations.Base
open import Foundations.Pi

open import Meta.Search.HLevel

open import Correspondences.Base public
open import Correspondences.Decidable

open import Data.Dec as Dec

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ

record Exhaustible {ℓ : Level} (A : Type ℓᵃ) : Type (ℓᵃ ⊔ ℓsuc ℓ) where
  no-eta-equality
  constructor exhaustible-η
  field exhaustible-β : {P : Pred ℓ A} → Decidable¹ P → Dec Π¹[ P ]

open Exhaustible public

exhaust : ⦃ x : Exhaustible {ℓ = ℓ} A ⦄ → Exhaustible A
exhaust ⦃ x ⦄ = x

lift-exhaustible : Exhaustible {ℓ = ℓ} A → Exhaustible (Lift ℓ A)
lift-exhaustible ex .exhaustible-β P? = Dec.map (_∘ lower) (λ ¬f g → ¬f $ g ∘ lift)
  (ex .exhaustible-β $ P? ∘ lift)

Π-decision : {B : A → Type ℓᵇ} → Decidable¹ B → Exhaustible A → Dec Π¹[ B ]
Π-decision d ex = ex .exhaustible-β d

∀-decision : {B : A → Type ℓᵇ} → Decidable¹ B → Exhaustible A → Dec ∀¹[ B ]
∀-decision d ex = dec-≃ Π-impl-Π-≃ .fst (Π-decision d ex)
