{-# OPTIONS --safe #-}
module Data.Dec.Instances.Monoidal where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Monoidal

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Reflects.Instances.Monoidal

instance
  Monoidal-Dec : Monoidal (eff Dec)
  Monoidal-Dec .unit = yes tt
  Monoidal-Dec ._<,>_ da db .does = da .does and db .does
  Monoidal-Dec ._<,>_ (no ¬a) _       .proof = ofⁿ (¬a ∘ fst)
  Monoidal-Dec ._<,>_ (yes _) (no ¬b) .proof = ofⁿ (¬b ∘ snd)
  Monoidal-Dec ._<,>_ (yes a) (yes b) .proof = ofʸ a <,> ofʸ b
