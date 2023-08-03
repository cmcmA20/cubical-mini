{-# OPTIONS --safe #-}
module Data.Vec.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Vec.Base
open import Data.Nat.Base
open import Data.String.Base

private
  variable
    @0 n : ℕ

  show-impl : ∀ {ℓ} {A : Type ℓ} → ⦃ _ : Show A ⦄ → ℕ → Vec A n → String
  show-impl _ [] = "[]"
  show-impl n (x ∷ xs) =
    show-parens (∷-prec <-internal n) $
      shows-prec (suc ∷-prec) x ++ₛ " ∷ " ++ₛ show-impl (suc n) xs
    where
      ∷-prec = 5

instance
  show-vec : ∀ {ℓ} {A : Type ℓ} → ⦃ _ : Show A ⦄ → Show (Vec A n)
  show-vec .shows-prec = show-impl

private
  module _ where
    open import Data.Nat.Instances.Show

    _ : show (1 ∷ 2 ∷ 3 ∷ []) ＝ "1 ∷ 2 ∷ 3 ∷ []"
    _ = refl

    _ : show ((1 ∷ []) ∷ (2 ∷ []) ∷ []) ＝ "(1 ∷ []) ∷ (2 ∷ []) ∷ []"
    _ = refl
