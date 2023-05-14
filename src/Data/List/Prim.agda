{-# OPTIONS --safe #-}
module Data.List.Prim where

open import Foundations.Prim.Type

open import Agda.Builtin.List public

private variable ℓ : Level

[_] : {A : Type ℓ} → A → List A
[ x ] = x ∷ []
