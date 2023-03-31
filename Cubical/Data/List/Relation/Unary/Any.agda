{-# OPTIONS --safe #-}
module Cubical.Data.List.Relation.Unary.Any where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Data.FinSum.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

data Any {A : Type ℓ} (P : A → Type ℓ′) : List A → Type (ℓ-max ℓ ℓ′) where
  here  : ∀ {x xs} → P x      → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)
