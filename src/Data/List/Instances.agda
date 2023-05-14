{-# OPTIONS --safe #-}
module Data.List.Instances where

open import Foundations.Base
open import Meta.FromProduct

open import Data.List.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  From-prod-List : From-product A (λ _ → List A)
  From-prod-List .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → List A
    go zero xs                = []
    go (suc zero) xs          = xs ∷ []
    go (suc (suc n)) (x , xs) = x ∷ go (suc n) xs
