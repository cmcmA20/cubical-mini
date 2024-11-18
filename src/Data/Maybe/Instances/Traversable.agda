{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Map
open import Meta.Effect.Traversable

open import Data.Maybe.Base

open Idiom ⦃ ... ⦄
open Traversable ⦃ ... ⦄

instance
  Traversable-Maybe : Traversable (eff Maybe)
  Traversable-Maybe .traverse f (just x) = just <$> f x
  Traversable-Maybe .traverse _ nothing  = pure nothing
