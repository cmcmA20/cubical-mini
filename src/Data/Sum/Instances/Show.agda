{-# OPTIONS --safe #-}
module Data.Sum.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Nat.Base
open import Data.String.Base
open import Data.Sum.Base

instance
  show-sum
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ _ : Show A ⦄ → ⦃ _ : Show B ⦄ → Show (A ⊎ B)
  show-sum .shows-prec n (inl v) =
    show-parens (0 <-internal n) $ "inl " ++ₛ (shows-prec (suc n) v)
  show-sum .shows-prec n (inr v) =
    show-parens (0 <-internal n) $ "inr " ++ₛ (shows-prec (suc n) v)

private
  module _ where
    open import Data.Nat.Instances.Show

    _ : show (the (ℕ ⊎ ℕ) (inl 0)) ＝ "inl 0"
    _ = refl

    _ : show (the ((ℕ ⊎ ℕ) ⊎ ℕ) (inl (inr 0))) ＝ "inl (inr 0)"
    _ = refl
