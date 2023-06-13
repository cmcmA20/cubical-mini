{-# OPTIONS --safe #-}
module Data.List.Instances.Traverse where

open import Foundations.Base

open import Meta.Traverse

open import Data.List.Base public

private variable
  ℓ : Level
  A : Type ℓ

instance
  Traverse-List : Traverse (eff List)
  Traverse-List .Traverse.traverse {M} {a} {b} = go where
    private module M = Effect M
    go : (a → M.₀ b) → List a → M.₀ (List b)
    go f []       = pure []
    go f (x ∷ xs) = ⦇ f x ∷ go f xs ⦈
