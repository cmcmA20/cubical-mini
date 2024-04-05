{-# OPTIONS --safe #-}
module Correspondences.Exhaustible where

open import Meta.Prelude

open import Correspondences.Base public
open import Correspondences.Decidable

open import Data.Dec as Dec
open import Data.Empty.Base as ⊥

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

record Exhaustible {ℓᵃ : Level} (A : Type ℓᵃ) : Typeω where
  no-eta-equality
  constructor exhaustible-η
  field exhaustible-β : ∀{ℓ} {P : Pred A ℓ} → Decidable P → Decidable Π[ P ]

open Exhaustible public

instance
  lift-exhaustible : ⦃ ex : Exhaustible A ⦄ → Exhaustible (Lift ℓ A)
  lift-exhaustible ⦃ ex ⦄ .exhaustible-β P? = Dec.dmap (_∘ lower) (contra $ _∘ lift)
    (ex .exhaustible-β P?)

  Π-decision
    : {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} {B : Pred A ℓᵇ}
    → ⦃ d : Decidable B ⦄ → ⦃ ex : Exhaustible A ⦄
    → Decidable Π[ B ]
  Π-decision ⦃ d ⦄ ⦃ ex ⦄ = ex .exhaustible-β d
  {-# OVERLAPPABLE Π-decision #-}

  ∀-decision
    : {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} {B : Pred A ℓᵇ}
    → ⦃ d : Decidable B ⦄ → ⦃ ex : Exhaustible A ⦄
    → Decidable ∀[ B ]
  ∀-decision ⦃ d ⦄ ⦃ ex ⦄ = Dec.ae Π≃∀ $ Π-decision
  {-# OVERLAPPABLE ∀-decision #-}


-- Usage
module _ ⦃ A-exh : Exhaustible A ⦄ where private
  _ : Exhaustible (Lift ℓ A)
  _ = autoω
