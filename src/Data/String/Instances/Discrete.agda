{-# OPTIONS --safe #-}
module Data.String.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Char.Instances.Discrete
open import Data.List.Base
open import Data.List.Instances.Discrete

open import Data.String.Properties

instance
  string-is-discrete : is-discrete String
  string-is-discrete =
    is-discrete-injection (string→list , string→list-inj) discrete!

  decomp-dis-string : goal-decomposition (quote is-discrete) String
  decomp-dis-string = decomp (quote string-is-discrete) []
