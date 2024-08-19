{-# OPTIONS --safe #-}
module Data.Quotient.Type.Path where

open import Foundations.Prelude

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Quotient.Type.Base
open import Data.Reflects.Base as Reflects

private variable
  ℓ ℓᵃ : Level
  A : Type ℓᵃ
  R : A → A → Type ℓ
  a b x y : A

instance
  Reflects-⦋-⦌=⦋-⦌ : ⦃ r : Reflects (R a b) true ⦄ → Reflects (Path (A / R) ⦋ a ⦌ ⦋ b ⦌) true
  Reflects-⦋-⦌=⦋-⦌ = Reflects.dmap (eq/ _ _) false! auto
