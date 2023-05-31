{-# OPTIONS --safe #-}
module Data.Vec.Instances.Traverse where

open import Foundations.Base
open import Meta.Traverse

open import Data.Nat.Base

open import Data.Vec.Base public

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

instance
  Traverse-Vec : Traverse (eff (λ T → Vec T n))
  Traverse-Vec .Traverse.traverse {M} {a} {b} = go where
    private module M = Effect M
    go : {n : ℕ} → (a → M.₀ b) → Vec a n → M.₀ (Vec b n)
    go {(zero)} f []       = pure []
    go {suc n}  f (x ∷ xs) = ⦇ f x ∷ go f xs ⦈
