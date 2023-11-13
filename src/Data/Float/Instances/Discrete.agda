{-# OPTIONS --safe #-}
module Data.Float.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Maybe.Instances.Discrete
open import Data.Word.Instances.Discrete

open import Data.Float.Properties

instance
  float-is-discrete : is-discrete Float
  float-is-discrete =
    is-discrete-injection (float→maybe-word64 , float→maybe-word64-inj) discrete!
