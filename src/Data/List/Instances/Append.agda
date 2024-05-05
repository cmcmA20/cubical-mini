{-# OPTIONS --safe #-}
module Data.List.Instances.Append where

open import Foundations.Base

open import Data.List.Base as List

private variable
  ℓ : Level
  A : 𝒰 ℓ

instance
  Reflᵘ-List : Reflᵘ (List A)
  Reflᵘ-List .mempty = []

  Transᵘ-List : Transᵘ (List A)
  Transᵘ-List ._<>_ = _++_
