{-# OPTIONS --safe #-}
module Data.Word.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Id

open import Data.Word.Base public

open import Agda.Builtin.Word.Properties public
  using ()
  renaming ( primWord64ToNatInjective to word64→ℕ-injⁱ)

word64→ℕ-inj : {a b : Word64} → word64→ℕ a ＝ word64→ℕ b → a ＝ b
word64→ℕ-inj p = Id≃path .fst (word64→ℕ-injⁱ _ _ ((Id≃path ₑ⁻¹) .fst p))
