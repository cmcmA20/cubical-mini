{-# OPTIONS --safe #-}
module Data.Fin where

open import Data.Fin.Base       public
import Data.Fin.Path
open module Path = Data.Fin.Path
--  hiding ()
  public
-- open import Data.Fin.Properties public

open import Data.Fin.Instances.Everything public
