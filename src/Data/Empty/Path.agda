{-# OPTIONS --safe #-}
module Data.Empty.Path where

open import Foundations.Prelude

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects

instance
  Reflects-⊥-Path : {a b : ⊥} → Reflects (a ＝ b) true
  Reflects-⊥-Path {()}
  {-# OVERLAPPING Reflects-⊥-Path #-}

  ⊥-is-discrete : is-discrete ⊥
  ⊥-is-discrete = reflects-path→is-discrete!

  Reflects-Absurd-Path : ∀{ℓ} {A : Type ℓ} {f g : ¬ A} → Reflects (f ＝ g) true
  Reflects-Absurd-Path = ofʸ prop!
