{-# OPTIONS --safe #-}
module Data.Float.Instances.Discrete where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Discrete

open import Data.Maybe.Instances.Discrete
open import Data.Word.Instances.Discrete
open import Data.Id

open import Data.Float.Properties

instance
  Discrete-Float : Discrete Float
  Discrete-Float .Discrete._≟_ =
    is-discrete-injection (float→maybe-word64 , float→maybe-word64-inj)
      (it .Discrete._≟_)
