{-# OPTIONS --safe #-}
module Data.Float.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Id

open import Data.Float.Base public

open import Agda.Builtin.Float.Properties public
  using ()
  renaming (primFloatToWord64Injective to float→maybe-word64-injⁱ)

float→maybe-word64-inj : {a b : Float} → float→maybe-word64 a ＝ float→maybe-word64 b → a ＝ b
float→maybe-word64-inj = Id≃path.to ∘ float→maybe-word64-injⁱ _ _ ∘′ Id≃path.from
