{-# OPTIONS --safe #-}
module Data.String.Instances.Append where

open import Foundations.Base

open import Data.String.Base as String

instance
  Reflᵘ-String : Reflᵘ String
  Reflᵘ-String .mempty = ""

  Transᵘ-String : Transᵘ String
  Transᵘ-String ._<>_ = _++ₛ_
