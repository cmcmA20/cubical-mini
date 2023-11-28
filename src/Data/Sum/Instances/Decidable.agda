{-# OPTIONS --safe #-}
module Data.Sum.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Sum.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

⊎-decision : Dec A → Dec B → Dec (A ⊎ B)
⊎-decision da db .does = da .does or db .does
⊎-decision (yes a) _ .proof = ofʸ (inl a)
⊎-decision (no ¬a) (yes b) .proof = ofʸ (inr b)
⊎-decision (no ¬a) (no ¬b) .proof = ofⁿ [ ¬a , ¬b ]ᵤ

instance
  decomp-dec-⊎ : goal-decomposition (quote Dec) (A ⊎ B)
  decomp-dec-⊎ = decomp (quote ⊎-decision)
    [ `search (quote Dec) , `search (quote Dec) ]
