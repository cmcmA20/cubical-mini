{-# OPTIONS --safe #-}
module Containers.List.Instances.FromProduct where

open import Foundations.Base
open import Meta.FromProduct

open import Data.FinSum.Base

open import Containers.List.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  From-prod-ListC : From-product A (λ _ → ⟦ ListC ⟧ A)
  From-prod-ListC .From-product.from-prod = go
    where
    go : (n : ℕ) → Vecₓ _ n → ⟦ ListC ⟧ _
    go 0 _ = 0 , λ ()
    go 1 x = 1 , const x
    go (suc (suc n)) (x , xs) with go (suc n) xs
    ... | m , f = suc m , λ where
      fzero    → x
      (fsuc k) → f k
