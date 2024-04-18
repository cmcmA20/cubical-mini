{-# OPTIONS --safe #-}
module Data.Reflection.Abs where

open import Foundations.Base

open import Data.String.Base

open import Agda.Builtin.Reflection
  public
  using ( Abs ; abs
        )

private variable
  ℓ : Level
  A : Type ℓ

abs-name : Abs A → String
abs-name (abs s _) = s

abs-binder : Abs A → A
abs-binder (abs _ x) = x
