{-# OPTIONS --safe #-}
module Data.List.Instances.FromProduct where

open import Foundations.Base

open import Meta.Literals.FromProduct

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Base
  using ([])
  public

private variable
  ℓ : Level
  A : Type ℓ

instance
  From-prod-List : From-product A (λ _ → List A)
  From-prod-List .From-product.from-prod = go where
    go : ∀ n → HProduct A n → List A
    go zero xs                = []
    go (suc zero) xs          = xs ∷ []
    go (suc (suc n)) (x , xs) = x ∷ go (suc n) xs
