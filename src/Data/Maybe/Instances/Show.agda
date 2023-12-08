{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Show where

open import Foundations.Base

open import Meta.Deriving.Show

open import Data.Maybe.Base

instance
  unquoteDecl Show-Maybe = derive-show Show-Maybe (quote Maybe)

private module _ where
  open import Data.Nat.Instances.Show

  _ : show (just (just 2)) ＝ "just (just 2)"
  _ = refl
