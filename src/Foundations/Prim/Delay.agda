{-# OPTIONS --guarded #-}
module Foundations.Prim.Delay where

open import Foundations.Base

module Prims where
  primitive
    primLockUniv : Type₁
open Prims public
  renaming (primLockUniv to LockU)

postulate
  Clock : LockU
{-# COMPILE GHC Clock = type () #-}
