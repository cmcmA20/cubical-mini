{-# OPTIONS --safe #-}
module Data.Vec.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Traversable

open import Data.Vec.Base

open Idiom ⦃ ... ⦄
open Traversable ⦃ ... ⦄

instance
  Traversable-Vec : ∀{n} → Traversable (eff λ T → Vec T n)
  Traversable-Vec .traverse {M} {A} {B} = go where
    private module M = Effect M
    go : ∀{n} → (A → M.₀ B) → Vec A n → M.₀ (Vec B n)
    go {0}     _ _        = pure _
    go {suc _} f (x , xs) = ⦇ f x , go f xs ⦈
