{-# OPTIONS --safe #-}
module Meta.Append where

open import Foundations.Base

-- aka raw monoid
record Append {ℓ} (A : Type ℓ) : Type ℓ where
  infixr 6 _<>_

  field
    mempty : A
    _<>_   : A → A → A

open Append ⦃ ... ⦄ public
