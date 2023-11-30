{-# OPTIONS --safe #-}
module Meta.Literals.FromProduct where

open import Foundations.Base

open import Data.Nat.Base public
  using (ℕ; zero; suc)
open import Data.HVec.Base
  using ()
  renaming (Vec′ to HProduct)
  public

record From-product {ℓ} (A : Type ℓ) (T : @0 ℕ → Type ℓ) : Type ℓ where
  field from-prod : ∀ n → HProduct A n → T n

[_] : ∀ {ℓ} {A : Type ℓ} {T : @0 ℕ → Type ℓ} {n} ⦃ fp : From-product A T ⦄
    → HProduct A n → T n
[_] ⦃ fp ⦄ = fp .From-product.from-prod _
