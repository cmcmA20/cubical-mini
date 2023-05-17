{-# OPTIONS --safe #-}
module Data.Sum.Base where

open import Foundations.Base

infixr 1 _⊎_
data _⊎_ {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  inj-l : A → A ⊎ B
  inj-r : B → A ⊎ B
