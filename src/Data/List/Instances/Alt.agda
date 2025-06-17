{-# OPTIONS --safe #-}
module Data.List.Instances.Alt where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Choice
open import Meta.Effect.Alt

open import Data.List.Base

open Choice ⦃ ... ⦄
open Alt ⦃ ... ⦄

instance
  Choice-List : Choice (eff List)
  Choice-List ._<|>_ = _++_

  Alt-List : Alt (eff List)
  Alt-List .fail = []
