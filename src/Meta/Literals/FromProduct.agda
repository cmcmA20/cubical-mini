{-# OPTIONS --safe #-}
module Meta.Literals.FromProduct where

open import Foundations.Base

open import Data.Nat.Base public
  using (ℕ; zero; suc)
open import Data.Product.Base public
  using (HProduct)

record From-product {ℓ} (A : Type ℓ) (T : @0 ℕ → Type ℓ) : Type ℓ where
  field from-prod : ∀ n → HProduct n A → T n

[_] : ∀ {ℓ} {A : Type ℓ} {T : @0 ℕ → Type ℓ} {n} ⦃ fp : From-product A T ⦄
    → HProduct n A → T n
[_] ⦃ fp ⦄ = fp .From-product.from-prod _
