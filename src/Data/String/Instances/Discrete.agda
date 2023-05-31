{-# OPTIONS --safe #-}
module Data.String.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete
open import Meta.Reflection.HLevel

open import Data.Char.Instances.Discrete
open import Data.List.Instances.Discrete

open import Data.String.Properties

instance
  Discrete-String : Discrete String
  Discrete-String .Discrete._≟_ =
    is-discrete-injection (string→list , string→list-inj)
      (it .Discrete._≟_)
