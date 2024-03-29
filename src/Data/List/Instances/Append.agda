{-# OPTIONS --safe #-}
module Data.List.Instances.Append where

open import Foundations.Base

open import Meta.Append

open import Data.List.Base as List

private variable
  ℓ : Level
  A : Type ℓ

instance
  Append-List : Append (List A)
  Append-List .mempty = []
  Append-List ._<>_ = _++_
