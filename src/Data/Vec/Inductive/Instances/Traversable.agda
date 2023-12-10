{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Traversable

open import Data.Vec.Inductive.Base

private variable
  ℓ : Level
  A : Type ℓ
  @0 n : ℕ

instance
  Traversable-Vec : Traversable (eff λ T → Vec T n)
  Traversable-Vec .traverse {M} {A} {B} = go where
    private module M = Effect M
    go : (A → M.₀ B) → Vec A n → M.₀ (Vec B n)
    go _ []       = pure []
    go f (x ∷ xs) = ⦇ f x ∷ go f xs ⦈
