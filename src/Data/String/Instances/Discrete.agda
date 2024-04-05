{-# OPTIONS --safe #-}
module Data.String.Instances.Discrete where

open import Foundations.Base

open import Correspondences.Discrete

open import Data.Char.Instances.Discrete
open import Data.List.Instances.Discrete

open import Data.String.Properties

instance
  string-is-discrete : is-discrete String
  string-is-discrete =
    ↣→is-discrete! (string→list , string→list-inj)
