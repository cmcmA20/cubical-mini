{-# OPTIONS --safe #-}
module Data.Reflection.Instances.FromString where

open import Foundations.Base

open import Meta.Literals.FromString

open import Data.List.Base
open import Data.Reflection.Error
open import Data.Unit.Base

instance
  From-string-ErrorPart : From-string ErrorPart
  From-string-ErrorPart .From-string.Constraint _ = ⊤
  From-string-ErrorPart .from-string s = str-err s

  From-string-error : From-string (List ErrorPart)
  From-string-error .From-string.Constraint _ = ⊤
  From-string-error .from-string s = str-err s ∷ []
