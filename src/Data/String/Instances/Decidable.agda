{-# OPTIONS --safe #-}
module Data.String.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Char.Instances.Decidable
open import Data.List.Instances.Decidable

open import Data.String.Properties

instance
  string-is-discrete : is-discrete String
  string-is-discrete =
    is-discrete-injection (string→list , string→list-inj) dec!
