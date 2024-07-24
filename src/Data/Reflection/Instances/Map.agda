{-# OPTIONS --safe #-}
module Data.Reflection.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Reflection.Argument

instance
  Map-Arg : Map (eff Arg)
  Map-Arg .map f (arg ai x) = arg ai (f x)

  Lawful-Map-Arg : Lawful-Map (eff Arg)
  Lawful-Map-Arg .Lawful-Map.map-pres-id _ (arg ai x) =
    arg ai x
  Lawful-Map-Arg .Lawful-Map.map-pres-comp {f} {g} _ (arg ai x) =
    arg ai (g (f x))
