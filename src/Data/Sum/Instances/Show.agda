{-# OPTIONS --safe #-}
module Data.Sum.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Nat.Base
open import Data.String.Base
open import Data.Sum.Base

instance
  Show-⊎
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A ⊎ B)
  Show-⊎ .shows-prec n (inl a) =
    show-parens (0 <ᵇ n) $ "inl " ++ₛ shows-prec (suc n) a
  Show-⊎ .shows-prec n (inr b) =
    show-parens (0 <ᵇ n) $ "inr " ++ₛ shows-prec (suc n) b

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (the (ℕ ⊎ ℕ) (inl 0)) ＝ "inl 0"
  _ = refl

  _ : show (the ((ℕ ⊎ ℕ) ⊎ ℕ) (inl (inr 0))) ＝ "inl (inr 0)"
  _ = refl
