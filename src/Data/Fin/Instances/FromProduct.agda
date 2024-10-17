{-# OPTIONS --safe #-}
module Data.Fin.Instances.FromProduct where

open import Foundations.Base

open import Meta.Literals.FromProduct

open import Data.Fin.Base

instance
  From-prod-fin-fun : ∀{ℓ} {A : Type ℓ} → From-product A (λ n → Fin n → A)
  From-prod-fin-fun {A} .from-prod = go where
    go : ∀ n → Prod A n → Fin n → A
    go 1 x _ = x
    go (suc (suc n)) (x , _) fzero = x
    go (suc (suc n)) (x , xs) (fsuc f) = go _ xs f
