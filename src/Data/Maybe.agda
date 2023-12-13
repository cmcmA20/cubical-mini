{-# OPTIONS --safe #-}
module Data.Maybe where

open import Data.Maybe.Base       public
import Data.Maybe.Path
open module Path = Data.Maybe.Path
  hiding (Code; code-refl; identity-system; code-is-of-hlevel)
  public
open import Data.Maybe.Properties public

open import Data.Maybe.Instances.Everything  public
