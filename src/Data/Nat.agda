{-# OPTIONS --safe #-}
module Data.Nat where

open import Data.Nat.Base       public
import Data.Nat.Path
open module Path = Data.Nat.Path
  hiding (Code; code-refl; decode; identity-system; code-is-prop)
  public
open import Data.Nat.Properties public

open import Data.Nat.Instances.Everything public
