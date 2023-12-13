{-# OPTIONS --safe #-}
module Data.List where

open import Data.List.Base       public
open import Data.List.Operations public
import Data.List.Path
open module Path = Data.List.Path
  hiding (Code; code-refl; decode; identity-system; code-is-of-hlevel)
  public
open import Data.List.Properties public

open import Data.List.Instances.Everything public
