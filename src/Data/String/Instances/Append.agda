{-# OPTIONS --safe #-}
module Data.String.Instances.Append where

open import Meta.Append

open import Data.String.Base as String

instance
  Append-String : Append String
  Append-String .Append.mempty = ""
  Append-String .Append._<>_ = _++ₛ_
