{-# OPTIONS --safe #-}
module Data.Reflection.Instances.Traversable where

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Effect.Traversable

open import Data.Reflection.Argument

instance
  Traversable-Arg : Traversable (eff Arg)
  Traversable-Arg .traverse f (arg ai x) = arg ai <$> f x
