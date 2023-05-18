{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Bind where

open import Foundations.Base
open import Meta.Bind

open import Data.Maybe.Instances.Idiom public

instance
  Bind-Maybe : Bind (eff Maybe)
  Bind-Maybe .Bind._>>=_ = extend
