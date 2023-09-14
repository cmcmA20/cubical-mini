{-# OPTIONS --safe #-}
module Data.Vec.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Nat.Base
open import Data.Vec.Base

private variable
  ℓ : Level
  A : Type ℓ
  @0 n : ℕ

instance
  Show-vec : ⦃ Show A ⦄ → Show (Vec A n)
  Show-vec .shows-prec = show-impl where
    ∷-prec = 5

    show-impl : ⦃ Show A ⦄ → ℕ → Vec A n → String
    show-impl _ [] = "[]"
    show-impl n (x ∷ xs) = show-parens (∷-prec <ᵇ n) $
      shows-prec (suc ∷-prec) x ++ₛ " ∷ " ++ₛ show-impl (suc n) xs

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (1 ∷ 2 ∷ 3 ∷ []) ＝ "1 ∷ 2 ∷ 3 ∷ []"
  _ = refl

  _ : show ((1 ∷ []) ∷ (2 ∷ []) ∷ []) ＝ "(1 ∷ []) ∷ (2 ∷ []) ∷ []"
  _ = refl
