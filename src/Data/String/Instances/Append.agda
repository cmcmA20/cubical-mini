{-# OPTIONS --safe #-}
module Data.String.Instances.Append where

open import Meta.Groupoid

open import Data.String.Base as String

instance
  Reflexiveᵘ-String : Reflexiveᵘ String
  Reflexiveᵘ-String .mempty = ""

  Transitiveᵘ-String : Transitiveᵘ String
  Transitiveᵘ-String ._<>_ = _++ₛ_
