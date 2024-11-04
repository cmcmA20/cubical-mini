{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Alt where

open import Meta.Effect.Alt
open import Meta.Effect.Base

open import Data.Tree.Binary.Base

open Alt ⦃ ... ⦄

instance
  Alt-Tree : Alt (eff Tree)
  Alt-Tree .fail  = empty
  Alt-Tree ._<|>_ = node
