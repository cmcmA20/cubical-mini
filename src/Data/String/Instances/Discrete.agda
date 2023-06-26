{-# OPTIONS --safe #-}
module Data.String.Instances.Discrete where

open import Foundations.Base

open import Meta.HLevel

open import Correspondences.Nullary.Decidable

open import Data.Char.Instances.Discrete
open import Data.List.Instances.Discrete

open import Data.String.Properties

instance
  string-is-discrete : is-discrete String
  string-is-discrete =
    is-discrete-injection (string→list , string→list-inj) it
