{-# OPTIONS --safe #-}
module Meta.Literals.FromProduct where

open import Foundations.Base

open import Data.Nat.Base
  using (ℕ; zero; suc)
  public
open import Data.Vec.Ergonomic.Base
  using ()
  renaming ( Vec  to Prod
           ; Vecᵈ to Prodᵈ
           )
  public

record From-product {ℓ} (A : Type ℓ) (T : ℕ → Type ℓ) : Type ℓ where
  field from-prod : ∀ n → Prod A n → T n
open From-product ⦃ ... ⦄ public

[_] : ∀ {ℓ} {A : Type ℓ} {T : ℕ → Type ℓ} ⦃ fp : From-product A T ⦄
      {n : ℕ} → Prod A n → T n
[_] ⦃ fp ⦄ = fp .from-prod _
{-# DISPLAY From-product.from-prod _ _ xs = [ xs ] #-}

record From-productᵈ {ℓ ℓ′} {A : Type ℓ} {S : ℕ → Type ℓ} ⦃ fp : From-product A S ⦄
  (B : A → Type ℓ′) (T : {n : ℕ} (xs : S n) → Type (ℓ ⊔ ℓ′)) : Type (ℓ ⊔ ℓ′) where
  field from-prodᵈ : (n : ℕ) (xs : Prod A n) → Prodᵈ B xs → T (from-prod n xs)
open From-productᵈ ⦃ ... ⦄ public

[_]ᵈ : ∀ {ℓ ℓ′} {A : Type ℓ} {S : ℕ → Type ℓ} ⦃ fp : From-product A S ⦄
       {B : A → Type ℓ′} {T : {n : ℕ} (xs : S n) → Type (ℓ ⊔ ℓ′)} ⦃ fdp : From-productᵈ B T ⦄
       {n : ℕ} {xs : Prod A n} → Prodᵈ B xs → T (from-prod n xs)
[_]ᵈ = from-prodᵈ _ _
{-# DISPLAY From-productᵈ.from-prodᵈ _ _ _ xs = [ xs ]ᵈ #-}
