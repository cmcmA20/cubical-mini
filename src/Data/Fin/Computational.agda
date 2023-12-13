{-# OPTIONS --safe #-}
module Data.Fin.Computational where

open import Data.Fin.Computational.Base       public
open import Data.Fin.Computational.Closure    public
import Data.Fin.Computational.Path
open module Path = Data.Fin.Computational.Path
  -- hiding ()
  public
open import Data.Fin.Computational.Properties public

open import Data.Fin.Computational.Instances.Everything public
