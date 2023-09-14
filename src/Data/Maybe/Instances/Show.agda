{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.String.Base

instance
  Show-maybe : ∀ {ℓ} {A : Type ℓ} → ⦃ Show A ⦄ → Show (Maybe A)
  Show-maybe .shows-prec _ nothing  = "nothing"
  Show-maybe .shows-prec n (just v) =
    show-parens (0 <ᵇ n) $ "just " ++ₛ shows-prec (suc n) v

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (just (just 2)) ＝ "just (just 2)"
  _ = refl
