{-# OPTIONS --safe #-}
module Data.List.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Bool.Base
open import Data.List.Base
open import Data.Nat.Base
open import Data.String.Base

private variable
  ℓ : Level
  A : Type ℓ

-- TODO show as list-syntax?
instance
  Show-list : ⦃ Show A ⦄ → Show (List A)
  Show-list .shows-prec = show-impl where
    show-impl : ⦃ Show A ⦄ → ℕ → List A → String
    show-impl _ [] = "[]"
    show-impl n (x ∷ xs) = show-parens (∷-prec <ᵇ n) $
      shows-prec (suc ∷-prec) x ++ₛ " ∷ " ++ₛ show-impl n xs
      where ∷-prec = 5

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (1 ∷ 2 ∷ 3 ∷ []) ＝ "1 ∷ 2 ∷ 3 ∷ []"
  _ = refl

  _ : show ((1 ∷ []) ∷ (2 ∷ []) ∷ [] ∷ []) ＝ "(1 ∷ []) ∷ (2 ∷ []) ∷ [] ∷ []"
  _ = refl
