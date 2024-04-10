{-# OPTIONS --safe #-}
module Data.Container.Base where

open import Foundations.Base

-- it has many names
infix 5 _▶_
record Container (s p : Level) : Type (ℓsuc (s ⊔ p)) where
  inductive
  eta-equality
  constructor _▶_
  field
    Shape    : Type s
    Position : Shape → Type p
