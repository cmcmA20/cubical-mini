{-# OPTIONS --safe #-}
module Meta.Literals.FromProduct where

open import Foundations.Base

open import Data.Nat.Base
  using (ℕ; zero; suc)
  public
open import Data.Vec.Ergonomic.Base
  using ()
  renaming (Vec to Product)
  public

record From-product {ℓ} (A : Type ℓ) (T : ℕ → Type ℓ) : Type ℓ where
  field from-prod : ∀ n → Product A n → T n

open From-product ⦃ ... ⦄ public

[_] : ∀ {ℓ} {A : Type ℓ} {T : ℕ → Type ℓ} {n} ⦃ fp : From-product A T ⦄
    → Product A n → T n
[_] ⦃ fp ⦄ = fp .from-prod _
