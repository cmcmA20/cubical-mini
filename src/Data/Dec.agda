{-# OPTIONS --safe #-}
module Data.Dec where

open import Data.Dec.Base       public
import Data.Dec.Path
open module Path = Data.Dec.Path
  hiding (Code; code-is-of-hlevel; identity-system)
  public
open import Data.Dec.Properties public
