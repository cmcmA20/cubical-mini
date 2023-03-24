{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Empty where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty.Base

open import Cubical.Instances.Show.Base

instance
  Show⊥ : Show ⊥
  Show.show Show⊥ ()
