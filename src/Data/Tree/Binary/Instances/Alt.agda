{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.Alt where

open import Meta.Effect.Alt
open import Meta.Effect.Base
open import Meta.Effect.Choice

open import Data.Tree.Binary.Base

open Alt ⦃ ... ⦄
open Choice ⦃ ... ⦄

instance
  Choice-Tree : Choice (eff Tree)
  Choice-Tree ._<|>_ = node

  Alt-Tree : Alt (eff Tree)
  Alt-Tree .fail  = empty
