{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Toset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Reflection.RecordEquiv

private variable ℓ ℓ′ : Level

module _ where
  open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
  open import Cubical.Relation.Binary.Poset using (IsPoset)

  record @0 IsToset {A : Type ℓ} (@0 _≤_ : A → A → Type ℓ′) : Type (ℓ-max ℓ ℓ′) where
    no-eta-equality
    constructor istoset

    field
      total : (x y : A) → (x ≤ y) ⊎ (y ≤ x)
      @0 isPoset : IsPoset _≤_

    open import Cubical.Relation.Nullary using (¬_)
    total′ : (x y : A) → ¬ (x ≤ y) → y ≤ x
    total′ x y x≰y with total x y
    ... | inr y≤x = y≤x
    ... | inl x≤y = ⊥-rec (x≰y x≤y)
      where open import Cubical.Data.Empty using () renaming (rec to ⊥-rec)

  module @0 _ where unquoteDecl IsTosetIsoΣ = declareRecordIsoΣ IsTosetIsoΣ (quote IsToset)

  record TosetStr (ℓ′ : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ′)) where
    constructor tosetstr
    field
      _≤_     : A → A → Type ℓ′
      @0 isToset : IsToset _≤_

    infixl 7 _≤_
    open module @0 IT = IsToset isToset public
    open module @0 IP = IsPoset isPoset public

Toset : ∀ ℓ ℓ′ → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ′))
Toset ℓ ℓ′ = TypeWithStr ℓ (TosetStr ℓ′)

toset : (A : Type ℓ) (_≤_ : A → A → Type ℓ′) (@0 h : IsToset _≤_) → Toset ℓ ℓ′
toset A _≤_ h = A , tosetstr _≤_ h

-- TODO equiv, DUARel
