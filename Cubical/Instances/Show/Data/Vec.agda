{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Vec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base
open import Cubical.Data.Vec.Base
open import Cubical.Data.Vec.Properties

open import Cubical.Instances.Show.Base renaming (_++_ to _++ₛ_)

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

instance
  ShowVec : ⦃ Show A ⦄ → Show (Vec A n)
  Show.show ShowVec xs = foldrₗ _++ₛ_ "" $ intersperse ", " $ mapₗ show (toList xs)
    where open import Cubical.Data.List.Base renaming (map to mapₗ; foldr to foldrₗ)
          toList : Vec A n → List A
          toList []       = []
          toList (x ∷ xs) = x ∷ toList xs
