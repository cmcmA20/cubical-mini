{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Traverse where

open import Foundations.Base

open import Meta.Traverse

open import Data.Maybe.Base public

instance
  Traverse-Maybe : Traverse (eff Maybe)
  Traverse-Maybe .Traverse.traverse f (just x) = just <$> f x
  Traverse-Maybe .Traverse.traverse f nothing  = pure nothing
