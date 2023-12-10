{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Map

open import Data.Maybe.Base as Maybe

instance
  Map-Maybe : Map (eff Maybe)
  Map-Maybe .map {A} {B} = go where
    go : (A → B) → Maybe A → Maybe B
    go f (just x) = just (f x)
    go _ nothing  = nothing
