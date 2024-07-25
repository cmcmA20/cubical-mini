{-# OPTIONS --safe #-}
module Data.Container.Instances.Membership where

open import Foundations.Prelude

open import Data.Container.Base
open import Data.Container.Instances.Brackets

instance
  Membership-container
    : ∀ {ℓ s p} {X : Type ℓ} {S : Type s} {P : S → Type p}
    → Membership X (⟦ S ▶ P ⟧ X) (ℓ ⊔ p)
  Membership-container ._∈_ x (_ , p) = fibre p x
