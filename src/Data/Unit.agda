{-# OPTIONS --safe #-}
module Data.Unit where

open import Data.Unit.Base       public
import Data.Unit.Path
open module Path = Data.Unit.Path
  -- hiding ()
  public
open import Data.Unit.Properties public

open import Data.Unit.Instances.Everything public
