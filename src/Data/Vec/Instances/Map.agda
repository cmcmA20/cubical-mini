{-# OPTIONS --safe #-}
module Data.Vec.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Vec.Base

instance
  Map-Vec : ∀{n} → Map (eff λ T → Vec T n)
  Map-Vec .map {A} {B} = go where
    go : ∀{n} → (A → B) → Vec A n → Vec B n
    go {n = 0}     _ _        = _
    go {n = suc _} f (x , xs) = f x ∷ go f xs
