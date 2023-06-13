{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Idiom where

open import Foundations.Base

open import Meta.Idiom

open import Data.Maybe.Base public

instance
  Map-Maybe : Map (eff Maybe)
  Map-Maybe .Map._<$>_ = map

  Idiom-Maybe : Idiom (eff Maybe)
  Idiom-Maybe .Idiom.pure = just
  Idiom-Maybe .Idiom._<*>_ = λ where
    (just f) (just x) → just (f x)
    _ _ → nothing
