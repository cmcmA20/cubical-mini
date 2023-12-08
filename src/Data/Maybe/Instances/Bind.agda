{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Bind where

open import Foundations.Base

open import Meta.Effect.Bind

open import Data.Maybe.Base
open import Data.Maybe.Instances.Idiom public

instance
  Bind-Maybe : Bind (eff Maybe)
  Bind-Maybe .Bind._>>=_ = extend
