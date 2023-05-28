{-# OPTIONS --safe #-}
module Meta.Show where

open import Foundations.Base
open import Data.Nat.Base
open import Data.String.Base

record Show {ℓ} (T : Type ℓ) : Type ℓ where
  field shows-prec : ℕ → T → String

  show : T → String
  show = shows-prec 0

open Show ⦃ ... ⦄ public
