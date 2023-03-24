{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List.Base

open import Cubical.Instances.Show.Base renaming (_++_ to _++ₛ_)

private variable
  ℓ : Level
  A : Type ℓ

instance
  ShowList : ⦃ Show A ⦄ → Show (List A)
  Show.show ShowList xs = "[" ++ₛ ((foldr _++ₛ_ "" $ intersperse ", " $ map show xs) ++ₛ "]")
