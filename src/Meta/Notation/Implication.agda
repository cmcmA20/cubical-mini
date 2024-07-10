{-# OPTIONS --safe #-}
module Meta.Notation.Implication where

open import Foundations.Base

record ⇒-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : Typeω where
  infixr 6 _⇒_
  field _⇒_ : A → B → R

open ⇒-notation ⦃ ... ⦄ public

instance
  ⇒-Type : ∀{ℓ ℓ′} → ⇒-notation (𝒰 ℓ) (𝒰 ℓ′) _
  ⇒-Type ._⇒_ A B = A → B
