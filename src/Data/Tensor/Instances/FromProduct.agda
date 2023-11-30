{-# OPTIONS --safe #-}
open import Foundations.Base
open import Data.Fin.Interface
open import Data.Nat.Base using (ℕ; zero; suc)

module Data.Tensor.Instances.FromProduct {F : @0 ℕ → Type} (fin-impl : FinI F) where

open import Meta.Literals.FromProduct

open import Data.Empty.Base as ⊥
  using (⊥)
open import Data.Tensor.Base fin-impl

private variable
  ℓ : Level
  A : Type ℓ

open FinI fin-impl

instance
  From-prod-tensor : From-product A (λ n → F n → A)
  From-prod-tensor .From-product.from-prod = go where
    go : ∀ n → HProduct A n → (F n → A)
    go 0 xs k = ⊥.rec (¬fin-0 k)
    go 1 x  _ = x
    go (suc (suc n)) (x , xs) k =
      rec x (λ _ _ → go (suc n) xs (fpred k)) k
