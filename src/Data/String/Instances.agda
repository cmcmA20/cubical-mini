{-# OPTIONS --safe #-}
module Data.String.Instances where

open import Foundations.Base
open import Meta.Literals

open import Data.String.Base

instance
  IsString-String : is-string String
  IsString-String .is-string.Constraint _ = ⊤
  IsString-String .is-string.fromString s = s
