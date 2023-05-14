{-# OPTIONS --safe #-}
module Data.Vec.Instances where

open import Foundations.Base
open import Meta.FromProduct

open import Data.Vec.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  From-prod-Vec : From-product A (Vec A)
  From-prod-Vec .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → Vec A n
    go zero xs                = []
    go (suc zero) xs          = xs ∷ []
    go (suc (suc n)) (x , xs) = x ∷ go (suc n) xs
