{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.FromProduct where

open import Foundations.Base

open import Meta.Literals.FromProduct

open import Data.Fin.Computational.Base

instance
  From-prod-fin-fun : ∀{ℓ} {A : Type ℓ} → From-product A (λ n → Fin n → A)
  From-prod-fin-fun {A} .from-prod = go where
    go : ∀ n → Prod A n → Fin n → A
    go 1 x _ = x
    go (suc (suc n)) (x , _)  (mk-fin 0) = x
    go (suc (suc n)) (_ , xs) (mk-fin (suc index) {(b)}) =
      go _ xs (mk-fin index {b})
