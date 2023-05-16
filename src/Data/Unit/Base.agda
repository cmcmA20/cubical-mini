{-# OPTIONS --safe #-}
module Data.Unit.Base where

open import Foundations.Base

open import Agda.Builtin.Unit public

private variable ℓ : Level

⊤* : Type ℓ
⊤* {ℓ} = Lift ℓ ⊤

record ⊤ω : Typeω where
  instance constructor ttω
