{-# OPTIONS --safe #-}
open import Foundations.Base

module Data.Wellfounded
  {ℓ ℓ′} {A : Type ℓ} (_<_ : A → A → 𝒰 ℓ′)
  where

open import Data.Wellfounded.Base _<_ public
open import Data.Wellfounded.Path     public
