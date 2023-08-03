{-# OPTIONS --safe #-}
module Data.List.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Bool.Base
open import Data.List.Base
open import Data.Nat.Base
open import Data.String.Base

private
  show-impl : ∀ {ℓ} {A : Type ℓ} → ⦃ _ : Show A ⦄ → ℕ → List A → String
  show-impl _ [] = "[]"
  show-impl n (x ∷ xs) =
    show-parens (∷-prec <-internal n) $
      shows-prec (suc ∷-prec) x ++ₛ " ∷ " ++ₛ show-impl n xs
    where
      ∷-prec = 5

instance
  show-list : ∀ {ℓ} {A : Type ℓ} → ⦃ _ : Show A ⦄ → Show (List A)
  show-list .shows-prec = show-impl

private
  module _ where
    open import Data.Nat.Instances.Show

    _ : show (1 ∷ 2 ∷ 3 ∷ []) ＝ "1 ∷ 2 ∷ 3 ∷ []"
    _ = refl

    _ : show ((1 ∷ []) ∷ (2 ∷ []) ∷ [] ∷ []) ＝ "(1 ∷ []) ∷ (2 ∷ []) ∷ [] ∷ []"
    _ = refl
