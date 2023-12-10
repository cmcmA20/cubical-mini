{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Idiom where

open import Foundations.Base

open import Meta.Effect.Idiom

open import Data.Maybe.Base
open import Data.Maybe.Instances.Map public

instance
  Idiom-Maybe : Idiom (eff Maybe)
  Idiom-Maybe .pure = just
  Idiom-Maybe ._<*>_ (just f) (just x) = just (f x)
  Idiom-Maybe ._<*>_ _ _ = nothing
