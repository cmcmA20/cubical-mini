{-# OPTIONS --safe #-}
module Data.Char.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete

open import Data.Id

open import Data.Char.Properties

instance
  Discrete-char : Discrete Char
  Discrete-char .Discrete._≟_ =
    is-discreteⁱ→is-discrete char-is-discreteⁱ
