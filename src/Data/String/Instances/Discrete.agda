{-# OPTIONS --safe #-}
module Data.String.Instances.Discrete where

open import Foundations.Base

open import Meta.Decision
open import Meta.HLevel

open import Data.Char.Instances.Discrete
open import Data.List.Instances.Discrete

open import Data.String.Properties

instance
  Discrete-String : Discrete String
  Discrete-String .Decision.has-decidable =
    is-discrete-injection (string→list , string→list-inj)
      (it .Decision.has-decidable)
