{-# OPTIONS --safe #-}
module Data.Float.Instances.Decidable where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Decidable

open import Data.Maybe.Instances.Decidable
open import Data.Word.Instances.Decidable
open import Data.Id

open import Data.Float.Properties

instance
  float-is-discrete : is-discrete Float
  float-is-discrete =
    is-discrete-injection (float→maybe-word64 , float→maybe-word64-inj) decide!
