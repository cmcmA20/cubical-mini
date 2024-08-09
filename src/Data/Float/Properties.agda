{-# OPTIONS --safe #-}
module Data.Float.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Id.Inductive

open import Data.Float.Base public

open import Agda.Builtin.Float.Properties public
  using ()
  renaming (primFloatToWord64Injective to float→word64ᵐ-injⁱ)

float→word64ᵐ-inj : {a b : Float} → float→word64ᵐ a ＝ float→word64ᵐ b → a ＝ b
float→word64ᵐ-inj = Id≃path.to ∘ float→word64ᵐ-injⁱ _ _ ∘ Id≃path.from
