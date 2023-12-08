{-# OPTIONS --safe #-}
module Data.List.Instances.Show where

open import Foundations.Base

open import Meta.Deriving.Show

open import Data.List.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  unquoteDecl Show-List = derive-show Show-List (quote List)

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (1 ∷ 2 ∷ 3 ∷ []) ＝ "1 ∷ 2 ∷ 3 ∷ []"
  _ = refl

  _ : show ((1 ∷ []) ∷ (2 ∷ []) ∷ [] ∷ []) ＝ "(1 ∷ []) ∷ (2 ∷ []) ∷ [] ∷ []"
  _ = refl
