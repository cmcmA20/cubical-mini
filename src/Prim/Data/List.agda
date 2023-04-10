{-# OPTIONS --safe #-}
module Prim.Data.List where

open import Prim.Type

open import Agda.Builtin.List public

private variable ℓ : Level

[_] : {A : Type ℓ} → A → List A
[ x ] = x ∷ []
