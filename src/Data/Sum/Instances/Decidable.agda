{-# OPTIONS --safe #-}
module Data.Sum.Instances.Decidable where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Sum.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

instance
  Dec-⊎ : ⦃ da : Dec A ⦄ → ⦃ db : Dec B ⦄ → Dec (A ⊎ B)
  Dec-⊎ ⦃ da ⦄ ⦃ db ⦄ .does = da .does or db .does
  Dec-⊎ ⦃ yes a ⦄ .proof = ofʸ (inl a)
  Dec-⊎ ⦃ no ¬a ⦄ ⦃ yes b ⦄ .proof = ofʸ (inr b)
  Dec-⊎ ⦃ no ¬a ⦄ ⦃ no ¬b ⦄ .proof = ofⁿ [ ¬a , ¬b ]ᵤ
  {-# OVERLAPPING Dec-⊎ #-}
