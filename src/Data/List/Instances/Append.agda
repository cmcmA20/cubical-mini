{-# OPTIONS --safe #-}
module Data.List.Instances.Append where

open import Foundations.Base

open import Meta.Groupoid

open import Data.List.Base as List

private variable
  ℓ : Level
  A : Type ℓ

instance
  Reflexiveᵘ-List : Reflexiveᵘ (List A)
  Reflexiveᵘ-List .mempty = []

  Transitiveᵘ-List : Transitiveᵘ (List A)
  Transitiveᵘ-List ._<>_ = _++_
