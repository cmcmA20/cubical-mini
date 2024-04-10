{-# OPTIONS --safe #-}
module Data.List.Instances.Alt where

open import Foundations.Base

open import Meta.Effect.Alt

open import Data.List.Base

instance
  Alt-List : Alt (eff List)
  Alt-List .fail = []
  Alt-List ._<|>_ = _++_
