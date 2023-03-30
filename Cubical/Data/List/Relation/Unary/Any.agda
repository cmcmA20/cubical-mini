{-# OPTIONS --safe #-}
module Cubical.Data.List.Relation.Unary.Any where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Data.FinSum.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

data ⋄ {A : Type ℓ} (P : A → Type ℓ′) : List A → Type (ℓ-max ℓ ℓ′) where
  here  : ∀ {x xs} → P x    → ⋄ P (x ∷ xs)
  there : ∀ {x xs} → ⋄ P xs → ⋄ P (x ∷ xs)

infixl 6 _!_
_!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) ! fzero  = x
(x ∷ xs) ! fsuc i = xs ! i

◇′ : (P : A → Type ℓ′) → List A → Type _
◇′ P xs = Σ[ i ꞉ Fin (length xs) ] P (xs ! i)
