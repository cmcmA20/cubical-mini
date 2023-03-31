{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Toset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum.Base

open import Cubical.Relation.Binary.Poset
open import Cubical.Relation.Nullary.Negation

open import Cubical.Reflection.RecordEquiv

private variable ℓ ℓ′ : Level

record IsToset {A : Type ℓ} (_≤_ : A → A → Type ℓ′) : Type (ℓ-max ℓ ℓ′) where
  no-eta-equality
  constructor istoset

  field
    total : (x y : A) → (x ≤ y) ⊎ (y ≤ x)
    isPoset : IsPoset _≤_

  total′ : (x y : A) → ¬ (x ≤ y) → y ≤ x
  total′ x y x≰y with total x y
  ... | inr y≤x = y≤x
  ... | inl x≤y = ⊥.rec (x≰y x≤y)

unquoteDecl IsTosetIsoΣ = declareRecordIsoΣ IsTosetIsoΣ (quote IsToset)

record TosetStr (ℓ′ : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ′)) where
  constructor tosetstr
  field
    _≤_     : A → A → Type ℓ′
    isToset : IsToset _≤_

  infixl 7 _≤_
  open IsToset isToset public
  open IsPoset isPoset public

Toset : ∀ ℓ ℓ′ → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ′))
Toset ℓ ℓ′ = TypeWithStr ℓ (TosetStr ℓ′)

toset : (A : Type ℓ) (_≤_ : A → A → Type ℓ′) (h : IsToset _≤_) → Toset ℓ ℓ′
toset A _≤_ h = A , tosetstr _≤_ h

-- TODO equiv, DUARel
