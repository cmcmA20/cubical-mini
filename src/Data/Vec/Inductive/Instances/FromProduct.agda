{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.FromProduct where

open import Foundations.Base

open import Meta.Literals.FromProduct

open import Data.Vec.Inductive.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  From-prod-Vec : From-product A (λ n → Vec A n)
  From-prod-Vec .from-prod = go where
    go : ∀ n → Product A n → Vec A n
    go 0 _ = []
    go 1 x = x ∷ []
    go (suc (suc n)) (x , xs) = x ∷ go (suc n) xs
