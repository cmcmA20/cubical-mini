{-# OPTIONS --safe #-}
module Data.Reflects where

open import Data.Reflects.Base       public
import Data.Reflects.Path
open module Path = Data.Reflects.Path
  hiding (Code ; code-refl ; identity-system ; code-is-of-hlevel)
  public
open import Data.Reflects.Properties public
