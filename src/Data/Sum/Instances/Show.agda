{-# OPTIONS --safe #-}
module Data.Sum.Instances.Show where

open import Foundations.Base

open import Meta.Deriving.Show

open import Data.Nat.Base
open import Data.String.Base
open import Data.Sum.Base

instance
  unquoteDecl Show-⊎ = derive-show Show-⊎ (quote _⊎ₜ_)

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (the (ℕ ⊎ ℕ) (inl 0)) ＝ "inl 0"
  _ = refl

  _ : show (the ((ℕ ⊎ ℕ) ⊎ ℕ) (inl (inr 0))) ＝ "inl (inr 0)"
  _ = refl
