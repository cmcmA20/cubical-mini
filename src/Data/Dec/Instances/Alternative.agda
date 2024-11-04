{-# OPTIONS --safe #-}
module Data.Dec.Instances.Alternative where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Alternative

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Reflects.Instances.Alternative
open import Data.Sum.Base

open Alternative ⦃ ... ⦄

instance
  Alternative-Dec : Alternative (eff Dec)
  Alternative-Dec .empty = no id
  Alternative-Dec ._<+>_ da db .does = da .does or db. does
  Alternative-Dec ._<+>_ (yes a) _       .proof = ofʸ (inl a)
  Alternative-Dec ._<+>_ (no ¬a) (yes b) .proof = ofʸ (inr b)
  Alternative-Dec ._<+>_ (no ¬a) (no ¬b) .proof = ofⁿ ¬a <+> ofⁿ ¬b
