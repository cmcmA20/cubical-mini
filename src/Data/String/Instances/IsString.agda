{-# OPTIONS --safe #-}
module Data.String.Instances.IsString where

open import Foundations.Base

open import Meta.Literals

open import Data.String.Base

instance
  IsString-String : IsString String
  IsString-String .IsString.Constraint _ = ⊤
  IsString-String .IsString.fromString s = s
