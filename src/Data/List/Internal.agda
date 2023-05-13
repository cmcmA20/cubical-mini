{-# OPTIONS --safe #-}
module Data.List.Internal where

open import Foundations.Type.Internal

open import Agda.Builtin.List public

private variable ℓ : Level

[_] : {A : Type ℓ} → A → List A
[ x ] = x ∷ []
