{-# OPTIONS --safe #-}
module Data.String.Instances.Append where

open import Foundations.Base

open import Data.String.Base as String

instance
  Pointed-String : Pointed String
  Pointed-String .mempty = ""

  Has-binary-op-String : Has-binary-op String
  Has-binary-op-String ._<>_ = _++ₛ_
