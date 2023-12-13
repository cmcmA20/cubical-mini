{-# OPTIONS --safe #-}
module Data.Dec where

open import Data.Dec.Base       public
import Data.Dec.Path
open module Path = Data.Dec.Path
  -- hiding ()
  public
open import Data.Dec.Properties public
