{-# OPTIONS --safe #-}
module Data.Bool.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base
open import Data.List.Base

open import Data.Bool.Base
open import Data.Bool.Path

instance
  bool-is-discrete : is-discrete Bool
  bool-is-discrete .is-discrete-β false false = yes refl
  bool-is-discrete .is-discrete-β false true  = no false≠true
  bool-is-discrete .is-discrete-β true  false = no true≠false
  bool-is-discrete .is-discrete-β true  true  = yes refl

  decomp-dis-bool : goal-decomposition (quote is-discrete) Bool
  decomp-dis-bool = decomp (quote bool-is-discrete) []
