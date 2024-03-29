{-# OPTIONS --safe #-}
module Data.Sum where

open import Data.Sum.Base       public
import Data.Sum.Path
open module Path = Data.Sum.Path
  hiding (Code; code-refl; identity-system; code-is-of-hlevel)
  public
open import Data.Sum.Properties public

open import Data.Sum.Instances.Everything public
