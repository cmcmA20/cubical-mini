{-# OPTIONS --safe #-}
module Cubical.Data.List.Relation.Unary.AnySubtype where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Fin.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

-- ◇ : (P : A → Type ℓ′) → List A → Type _
-- ◇ P xs = Σ[ i ꞉ Fin (length xs) ] P (xs ! i)

-- ◇! : (P : A → Type ℓ′) → List A → Type _
-- ◇! P xs = isContr (◇ P xs)
