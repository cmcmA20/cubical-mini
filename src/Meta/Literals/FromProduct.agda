{-# OPTIONS --safe #-}
module Meta.Literals.FromProduct where

open import Foundations.Base

open import Data.Nat.Base
  using (ℕ; zero; suc)
  public
open import Data.Vec.Ergonomic.Base
  using ()
  renaming ( Vec to Product
           ; Vecᵈ to Productᵈ
           )
  public

record From-product {ℓ} (A : Type ℓ) (T : ℕ → Type ℓ) : Type ℓ where
  field from-prod : ∀ n → Product A n → T n
open From-product ⦃ ... ⦄ public

[_] : ∀ {ℓ} {A : Type ℓ} {T : ℕ → Type ℓ} ⦃ fp : From-product A T ⦄
      {n : ℕ} → Product A n → T n
[_] ⦃ fp ⦄ = fp .from-prod _

record From-productᵈ {ℓ ℓ′} {A : Type ℓ} {S : ℕ → Type ℓ} ⦃ fp : From-product A S ⦄
  (B : A → Type ℓ′) (T : {n : ℕ} (xs : S n) → Type (ℓ ⊔ ℓ′)) : Type (ℓ ⊔ ℓ′) where
  field from-prodᵈ : (n : ℕ) (xs : Product A n) → Productᵈ B xs → T (from-prod n xs)
open From-productᵈ ⦃ ... ⦄ public

[_]ᵈ : ∀ {ℓ ℓ′} {A : Type ℓ} {S : ℕ → Type ℓ} ⦃ fp : From-product A S ⦄
       {B : A → Type ℓ′} {T : {n : ℕ} (xs : S n) → Type (ℓ ⊔ ℓ′)} ⦃ fdp : From-productᵈ B T ⦄
       {n : ℕ} {xs : Product A n} → Productᵈ B xs → T (from-prod n xs)
[_]ᵈ = from-prodᵈ _ _
