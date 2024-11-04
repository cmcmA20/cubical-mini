{-# OPTIONS --safe #-}
module Data.List.Instances.Traversable where

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Traversable

open import Data.List.Base

open Idiom ⦃ ... ⦄
open Traversable ⦃ ... ⦄

instance
  Traversable-List : Traversable (eff List)
  Traversable-List .traverse {M} {A} {B} = go where
    private module M = Effect M
    go : (A → M.₀ B) → List A → M.₀ (List B)
    go f []       = pure []
    go f (x ∷ xs) = ⦇ f x ∷ go f xs ⦈
