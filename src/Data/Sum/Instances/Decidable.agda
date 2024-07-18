{-# OPTIONS --safe #-}
module Data.Sum.Instances.Decidable where

open import Foundations.Base

open import Meta.Effect.Alternative

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Dec.Instances.Alternative
open import Data.Sum.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

instance
  Dec-⊎ : ⦃ da : Dec A ⦄ → ⦃ db : Dec B ⦄ → Dec (A ⊎ B)
  Dec-⊎ ⦃ da ⦄ ⦃ db ⦄ = da <+> db
  {-# OVERLAPPING Dec-⊎ #-}
