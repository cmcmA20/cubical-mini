{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Traversable

open import Data.Nat.Base

open import Data.Vec.Inductive.Base public

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

instance
  Traversable-Vec : Traversable (eff (λ T → Vec T n))
  Traversable-Vec .traverse {M} {A} {B} = go where
    private module M = Effect M
    go : (A → M.₀ B) → Vec A n → M.₀ (Vec B n)
    go {(zero)} f []       = pure []
    go {suc n}  f (x ∷ xs) = ⦇ f x ∷ go f xs ⦈
