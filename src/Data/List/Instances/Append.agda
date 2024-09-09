{-# OPTIONS --safe #-}
module Data.List.Instances.Append where

open import Foundations.Base

open import Data.List.Base as List

private variable
  ℓ : Level
  A : 𝒰 ℓ

instance
  Pointed-List : Pointed (List A)
  Pointed-List .mempty = []

  Has-binary-op-List : Has-binary-op (List A)
  Has-binary-op-List ._<>_ = _++_
