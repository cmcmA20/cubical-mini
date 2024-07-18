{-# OPTIONS --safe #-}
module Data.Reflection.Instances.Map where

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Reflection.Argument

instance
  Map-Arg : Map (eff Arg)
  Map-Arg .map f (arg ai x) = arg ai (f x)
