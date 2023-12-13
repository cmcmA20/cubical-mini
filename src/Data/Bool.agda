{-# OPTIONS --safe #-}
module Data.Bool where

open import Data.Bool.Base       public
import Data.Bool.Path
open module Path = Data.Bool.Path
  hiding (Code; code-refl; decode; identity-system; code-is-prop)
  public
open import Data.Bool.Properties public

open import Data.Bool.Instances.Everything public
