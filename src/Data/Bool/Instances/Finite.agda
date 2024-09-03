{-# OPTIONS --safe #-}
module Data.Bool.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Combinatorics.Finiteness.Bishop.Manifest

open import Data.Bool.Base
open import Data.Fin.Computational.Base
open import Data.List.Base

instance
  bool-manifest-bishop-finite : Manifest-bishop-finite Bool
  bool-manifest-bishop-finite = finite $ ≅→≃ go where
    open Iso
    go : Bool ≅ Fin 2
    go .to false = mk-fin 0
    go .to true  = mk-fin 1
    go .from (mk-fin 0) = false
    go .from (mk-fin 1) = true
    go .inverses .Inverses.inv-o _ (mk-fin 0) = mk-fin 0
    go .inverses .Inverses.inv-o _ (mk-fin 1) = mk-fin 1
    go .inverses .Inverses.inv-i _ false = false
    go .inverses .Inverses.inv-i _ true = true
  {-# OVERLAPPING bool-manifest-bishop-finite #-}
